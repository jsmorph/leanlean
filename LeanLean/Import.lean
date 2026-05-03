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

def checkSafeDefinition (name : Lean.Name) : Lean.DefinitionSafety → Result Unit
  | .safe => pure ()
  | .«unsafe» => .error s!"unsafe definition is outside the local importer: {name}"
  | .«partial» => .error s!"partial definition is outside the local importer: {name}"

def checkSafeFlag (kind : String) (name : Lean.Name) (isUnsafe : Bool) : Result Unit :=
  if isUnsafe then
    .error s!"unsafe {kind} is outside the local importer: {name}"
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
      checkSafeFlag "axiom" value.name value.isUnsafe
      pure
        (.axiom
          (translateName value.name)
          (translateLevelParams value.levelParams)
          (← translateExpr value.type))
  | .defnDecl value => do
      checkSafeDefinition value.name value.safety
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
      checkSafeFlag "opaque definition" value.name value.isUnsafe
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
        .error s!"unsafe inductive declaration is outside the local importer: {repr (types.map (·.name))}"
      pure
        (.kernelInductive
          {
            levelParams := translateLevelParams levelParams
            numParams
            types := (← types.mapM translateInductiveType)
          })

def translateGeneratedConstantInfo : Lean.ConstantInfo → Result Declaration
  | .ctorInfo value => do
      pure
        (.generatedConstructor
          (translateName value.name)
          (translateLevelParams value.levelParams)
          (← translateExpr value.type)
          (translateName value.induct))
  | .recInfo value => do
      pure
        (.generatedRecursor
          (translateName value.name)
          (translateLevelParams value.levelParams)
          (← translateExpr value.type))
  | info => .error s!"constant is not a generated constructor or recursor: {info.name}"

end Import
end LeanLean
