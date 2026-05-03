import Lean
import LeanLean.Kernel

namespace LeanLean
namespace Import

def translateName (name : Lean.Name) : LeanLean.Name :=
  toString name

def translateBinderName : Lean.Name → String
  | .anonymous => "_"
  | name => translateName name

def translateLevel : Lean.Level → Result LeanLean.Level
  | .zero => pure .zero
  | .succ level => do
      pure (.succ (← translateLevel level))
  | .max left right => do
      pure (.max (← translateLevel left) (← translateLevel right))
  | .imax left right => do
      pure (.imax (← translateLevel left) (← translateLevel right))
  | .param name => pure (.param (translateName name))
  | .mvar id => .error s!"universe metavariable is outside the local kernel syntax: {repr id}"
termination_by level => level

def translateLevelParams (params : List Lean.Name) : LevelContext :=
  params.map translateName

def translateExpr : Lean.Expr → Result LeanLean.Expr
  | .bvar index => pure (.bvar index)
  | .sort level => do
      pure (.sort (← translateLevel level))
  | .const name levels => do
      pure (.const (translateName name) (← levels.mapM translateLevel))
  | .app fn arg => do
      pure (.app (← translateExpr fn) (← translateExpr arg))
  | .lam name type body _ => do
      pure (.lam (translateBinderName name) (← translateExpr type) (← translateExpr body))
  | .forallE name type body _ => do
      pure (.forallE (translateBinderName name) (← translateExpr type) (← translateExpr body))
  | .letE name type value body _ => do
      pure
        (.letE
          (translateBinderName name)
          (← translateExpr type)
          (← translateExpr value)
          (← translateExpr body))
  | .proj typeName index struct => do
      pure (.proj (translateName typeName) index (← translateExpr struct))
  | .mdata _ body => translateExpr body
  | .fvar id => .error s!"free variable is outside the local kernel syntax: {repr id}"
  | .mvar id => .error s!"term metavariable is outside the local kernel syntax: {repr id}"
  | .lit lit => .error s!"literal expression is outside the local kernel syntax: {repr lit}"
termination_by expr => expr

def translateReducibilityHints : Lean.ReducibilityHints → ReducibilityHint
  | .regular height => .regular height.toNat
  | .abbrev => .abbrev
  | .opaque => .opaque

def checkTrustedDefinitionSafety (name : Lean.Name) : Lean.DefinitionSafety → Result Unit
  | .safe => pure ()
  | .«unsafe» => .error s!"trusted replay rejects unsafe definition: {name}"
  | .«partial» => .error s!"partial definition is outside the local importer: {name}"

def checkTrustedUnsafeFlag (kind : String) (name : Lean.Name) (isUnsafe : Bool) : Result Unit :=
  if isUnsafe then
    .error s!"trusted replay rejects unsafe {kind}: {name}"
  else
    pure ()

def translateConstructor (ctor : Lean.Constructor) : Result KernelConstructorDecl := do
  pure
    {
      name := translateName ctor.name
      type := (← translateExpr ctor.type)
    }

def translateInductiveType (typeDecl : Lean.InductiveType) : Result KernelInductiveTypeDecl := do
  pure
    {
      name := translateName typeDecl.name
      type := (← translateExpr typeDecl.type)
      ctors := (← typeDecl.ctors.mapM translateConstructor)
    }

def translateDeclaration : Lean.Declaration → Result Declaration
  | .axiomDecl value => do
      checkTrustedUnsafeFlag "axiom" value.name value.isUnsafe
      pure
        (.axiom
          (translateName value.name)
          (translateLevelParams value.levelParams)
          (← translateExpr value.type))
  | .defnDecl value => do
      checkTrustedDefinitionSafety value.name value.safety
      pure
        (.definitionWithHint
          (translateName value.name)
          (translateLevelParams value.levelParams)
          (translateReducibilityHints value.hints)
          (← translateExpr value.type)
          (← translateExpr value.value))
  | .thmDecl value => do
      pure
        (.theorem
          (translateName value.name)
          (translateLevelParams value.levelParams)
          (← translateExpr value.type)
          (← translateExpr value.value))
  | .opaqueDecl value => do
      checkTrustedUnsafeFlag "opaque definition" value.name value.isUnsafe
      pure
        (.opaqueDefinition
          (translateName value.name)
          (translateLevelParams value.levelParams)
          (← translateExpr value.type)
          (← translateExpr value.value))
  | .quotDecl => pure .quotientPrimitives
  | .mutualDefnDecl values =>
      .error s!"mutual definition declarations are outside the local importer: {repr (values.map (·.name))}"
  | .inductDecl levelParams numParams types isUnsafe => do
      if isUnsafe then
        .error s!"trusted replay rejects unsafe inductive declaration: {repr (types.map (·.name))}"
      pure
        (.kernelInductive
          {
            levelParams := translateLevelParams levelParams
            numParams
            types := (← types.mapM translateInductiveType)
          })

def translateGeneratedConstantInfo : Lean.ConstantInfo → Result Declaration
  | .ctorInfo value => do
      checkTrustedUnsafeFlag "constructor" value.name value.isUnsafe
      pure
        (.generatedConstructor
          (translateName value.name)
          (translateLevelParams value.levelParams)
          (← translateExpr value.type)
          (translateName value.induct))
  | .recInfo value => do
      checkTrustedUnsafeFlag "recursor" value.name value.isUnsafe
      pure
        (.generatedRecursorWithInfo
          (translateName value.name)
          (translateLevelParams value.levelParams)
          (← translateExpr value.type)
          {
            all := value.all.map translateName
            numParams := value.numParams
            numIndices := value.numIndices
            numMotives := value.numMotives
            numMinors := value.numMinors
            rules :=
              (← value.rules.mapM fun rule => do
                pure
                  {
                    ctor := translateName rule.ctor
                    nfields := rule.nfields
                    rhs? := some (← translateExpr rule.rhs)
                  })
          })
  | info => .error s!"constant is not a generated constructor or recursor: {info.name}"

def findInductiveInfo? : List Lean.ConstantInfo → Lean.Name → Option Lean.InductiveVal
  | [], _ => none
  | .inductInfo value :: rest, name =>
      if value.name == name then
        some value
      else
        findInductiveInfo? rest name
  | _ :: rest, name => findInductiveInfo? rest name

def findConstructorInfo? : List Lean.ConstantInfo → Lean.Name → Option Lean.ConstructorVal
  | [], _ => none
  | .ctorInfo value :: rest, name =>
      if value.name == name then
        some value
      else
        findConstructorInfo? rest name
  | _ :: rest, name => findConstructorInfo? rest name

def nameListsEq (left right : List Lean.Name) : Bool :=
  left.length = right.length && (List.zip left right).all fun pair => pair.1 == pair.2

def appendGroupKey (keys : List (List Lean.Name)) (key : List Lean.Name) : List (List Lean.Name) :=
  if keys.any fun existing => nameListsEq existing key then
    keys
  else
    keys ++ [key]

def inductiveGroupKey (value : Lean.InductiveVal) : List Lean.Name :=
  match value.all with
  | [] => [value.name]
  | names => names

def inductiveGroupKeys (infos : List Lean.ConstantInfo) : List (List Lean.Name) :=
  infos.foldl
    (fun keys info =>
      match info with
      | .inductInfo value => appendGroupKey keys (inductiveGroupKey value)
      | _ => keys)
    []

def translateConstructorFromInfo
    (infos : List Lean.ConstantInfo)
    (inductiveName ctorName : Lean.Name)
    (numParams expectedIndex : Nat) : Result KernelConstructorDecl := do
  let some ctor ← pure (findConstructorInfo? infos ctorName)
    | .error s!"missing constructor info for inductive snapshot: {ctorName}"
  checkTrustedUnsafeFlag "constructor" ctor.name ctor.isUnsafe
  if ctor.induct != inductiveName then
    .error s!"constructor {ctorName} belongs to {ctor.induct}, not {inductiveName}"
  if ctor.cidx != expectedIndex then
    .error s!"constructor {ctorName} has an unexpected constructor index"
  if ctor.numParams != numParams then
    .error s!"constructor {ctorName} has an unexpected parameter count"
  pure
    {
      name := translateName ctor.name
      type := (← translateExpr ctor.type)
    }

def translateConstructorsFromInfo
    (infos : List Lean.ConstantInfo)
    (inductiveName : Lean.Name)
    (numParams : Nat) : Nat → List Lean.Name → Result (List KernelConstructorDecl)
  | _, [] => pure []
  | index, ctorName :: rest => do
      let ctor ← translateConstructorFromInfo infos inductiveName ctorName numParams index
      let rest ← translateConstructorsFromInfo infos inductiveName numParams (index + 1) rest
      pure (ctor :: rest)

def translateInductiveInfo
    (infos : List Lean.ConstantInfo)
    (groupNames : List Lean.Name)
    (levelParams : List Lean.Name)
    (numParams : Nat)
    (name : Lean.Name) : Result KernelInductiveTypeDecl := do
  let some value ← pure (findInductiveInfo? infos name)
    | .error s!"missing inductive info for snapshot group member: {name}"
  if value.isUnsafe then
    .error s!"trusted replay rejects unsafe inductive declaration: {name}"
  if !nameListsEq (inductiveGroupKey value) groupNames then
    .error s!"inductive snapshot group has inconsistent member list: {name}"
  if !nameListsEq value.levelParams levelParams then
    .error s!"inductive snapshot group has inconsistent universe parameters: {name}"
  if value.numParams != numParams then
    .error s!"inductive snapshot group has inconsistent parameter counts: {name}"
  let ctors ← translateConstructorsFromInfo infos value.name numParams 0 value.ctors
  pure
    {
      name := translateName value.name
      type := (← translateExpr value.type)
      ctors
    }

def translateInductiveGroup
    (infos : List Lean.ConstantInfo)
    (names : List Lean.Name) : Result Declaration := do
  let some firstName := names.head?
    | .error "empty inductive snapshot group"
  let some first ← pure (findInductiveInfo? infos firstName)
    | .error s!"missing inductive info for snapshot group root: {firstName}"
  if first.isUnsafe then
    .error s!"trusted replay rejects unsafe inductive declaration: {first.name}"
  let groupNames := inductiveGroupKey first
  if !nameListsEq groupNames names then
    .error s!"inductive snapshot group has inconsistent member list: {repr names}"
  let types ← names.mapM (translateInductiveInfo infos names first.levelParams first.numParams)
  pure
    (.kernelInductive
      {
        levelParams := translateLevelParams first.levelParams
        numParams := first.numParams
        types
      })

def translateOrdinaryConstantInfo? : Lean.ConstantInfo → Result (Option Declaration)
  | .axiomInfo value => do
      checkTrustedUnsafeFlag "axiom" value.name value.isUnsafe
      pure
        (some
          (.axiom
            (translateName value.name)
            (translateLevelParams value.levelParams)
            (← translateExpr value.type)))
  | .defnInfo value => do
      checkTrustedDefinitionSafety value.name value.safety
      pure
        (some
          (.definitionWithHint
            (translateName value.name)
            (translateLevelParams value.levelParams)
            (translateReducibilityHints value.hints)
            (← translateExpr value.type)
            (← translateExpr value.value)))
  | .thmInfo value => do
      pure
        (some
          (.theorem
            (translateName value.name)
            (translateLevelParams value.levelParams)
            (← translateExpr value.type)
            (← translateExpr value.value)))
  | .opaqueInfo value => do
      checkTrustedUnsafeFlag "opaque definition" value.name value.isUnsafe
      pure
        (some
          (.opaqueDefinition
            (translateName value.name)
            (translateLevelParams value.levelParams)
            (← translateExpr value.type)
            (← translateExpr value.value)))
  | .quotInfo _ => pure none
  | .inductInfo _ => pure none
  | .ctorInfo _ => pure none
  | .recInfo _ => pure none

def translateOrdinaryConstantInfos (infos : List Lean.ConstantInfo) : Result (List Declaration) :=
  let collect :=
    infos.foldlM
      (fun declarations info => do
        match (← translateOrdinaryConstantInfo? info) with
        | some declaration => pure (declaration :: declarations)
        | none => pure declarations)
      []
  collect.map List.reverse

def translateGeneratedConstantInfos (infos : List Lean.ConstantInfo) : Result (List Declaration) :=
  let collect :=
    infos.foldlM
      (fun declarations info => do
        match info with
        | .ctorInfo _ | .recInfo _ =>
            pure ((← translateGeneratedConstantInfo info) :: declarations)
        | _ => pure declarations)
      []
  collect.map List.reverse

def hasQuotientInfo (infos : List Lean.ConstantInfo) : Bool :=
  infos.any fun info =>
    match info with
    | .quotInfo _ => true
    | _ => false

def translateConstantInfoSnapshot (infos : List Lean.ConstantInfo) : Result (List Declaration) := do
  let quotientDecls := if hasQuotientInfo infos then [.quotientPrimitives] else []
  let ordinary ← translateOrdinaryConstantInfos infos
  let inductives ← (inductiveGroupKeys infos).mapM (translateInductiveGroup infos)
  let generated ← translateGeneratedConstantInfos infos
  pure (quotientDecls ++ ordinary ++ inductives ++ generated)

def replayConstantInfoSnapshot (env : Env) (infos : List Lean.ConstantInfo) : Result Env := do
  replayDeclarations env (← translateConstantInfoSnapshot infos)

def appendLeanNames (names extra : List Lean.Name) : List Lean.Name :=
  extra.foldl
    (fun acc name =>
      if acc.any fun existing => existing == name then
        acc
      else
        acc ++ [name])
    names

def leanExprConstants (expr : Lean.Expr) : List Lean.Name :=
  expr.getUsedConstants.toList

def recursorRuleConstants (rule : Lean.RecursorRule) : List Lean.Name :=
  leanExprConstants rule.rhs

def recursorNames (names : List Lean.Name) : List Lean.Name :=
  names.map Lean.mkRecName

def constantInfoValueConstants : Lean.ConstantInfo → List Lean.Name
  | .defnInfo value => leanExprConstants value.value
  | .thmInfo value => leanExprConstants value.value
  | .opaqueInfo value => leanExprConstants value.value
  | .recInfo value =>
      value.rules.foldl
        (fun names rule => appendLeanNames names (recursorRuleConstants rule))
        []
  | _ => []

def quotientPrimitiveNames : List Lean.Name :=
  [``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind]

def constantInfoMetadataConstants : Lean.ConstantInfo → List Lean.Name
  | .inductInfo value =>
      appendLeanNames
        (appendLeanNames (inductiveGroupKey value) value.ctors)
        (recursorNames (inductiveGroupKey value))
  | .ctorInfo value => [value.induct]
  | .recInfo value => value.all
  | .quotInfo _ => ``Eq :: quotientPrimitiveNames
  | _ => []

def constantInfoDependencyNames (info : Lean.ConstantInfo) : List Lean.Name :=
  appendLeanNames
    (appendLeanNames (leanExprConstants info.type) (constantInfoValueConstants info))
    (constantInfoMetadataConstants info)

partial def collectConstantInfoClosureWith?
    (lookup : Lean.Name → Option Lean.ConstantInfo)
    (roots : List Lean.Name) : Result (List Lean.ConstantInfo) := do
  let rec loop
      (pending seen : List Lean.Name)
      (infos : List Lean.ConstantInfo) : Result (List Lean.ConstantInfo) := do
    match pending with
    | [] => pure infos.reverse
    | name :: rest =>
        if seen.any fun existing => existing == name then
          loop rest seen infos
        else
          let some info := lookup name
            | .error s!"unknown Lean environment constant in import closure: {name}"
          let dependencies := constantInfoDependencyNames info
          let pending := appendLeanNames rest dependencies
          loop pending (name :: seen) (info :: infos)
  loop roots [] []

def collectEnvironmentClosure
    (env : Lean.Environment)
    (roots : List Lean.Name) : Result (List Lean.ConstantInfo) :=
  collectConstantInfoClosureWith? (fun name => env.find? name) roots

def replayEnvironmentClosure
    (env : Env)
    (leanEnv : Lean.Environment)
    (roots : List Lean.Name) : Result Env := do
  replayConstantInfoSnapshot env (← collectEnvironmentClosure leanEnv roots)

end Import
end LeanLean
