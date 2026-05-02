import LeanLean.Syntax

namespace LeanLean

structure Binder where
  name : String
  type : Expr
  deriving DecidableEq, Repr, Inhabited

structure ConstructorSpec where
  name : Name
  fields : List Binder
  deriving DecidableEq, Repr, Inhabited

structure InductiveSpec where
  name : Name
  params : List Binder
  level : Level
  ctors : List ConstructorSpec
  deriving DecidableEq, Repr, Inhabited

inductive ConstantInfo where
  | axiom : Name → Expr → ConstantInfo
  | defn : Name → Expr → Expr → ConstantInfo
  | inductive : Name → Expr → InductiveSpec → ConstantInfo
  | ctor : Name → Expr → Name → List Binder → List Bool → ConstantInfo
  | recursor : Name → Name → ConstantInfo
  deriving DecidableEq, Repr, Inhabited

abbrev Context := List Binder
abbrev Env := List ConstantInfo
abbrev Result := Except String

namespace ConstantInfo

def name : ConstantInfo → Name
  | .axiom name _ => name
  | .defn name _ _ => name
  | .inductive name _ _ => name
  | .ctor name _ _ _ _ => name
  | .recursor name _ => name

def type? : ConstantInfo → Option Expr
  | .axiom _ type => some type
  | .defn _ type _ => some type
  | .inductive _ type _ => some type
  | .ctor _ type _ _ _ => some type
  | .recursor _ _ => none

end ConstantInfo

namespace Env

def find? : Env → Name → Option ConstantInfo
  | [], _ => none
  | info :: rest, target =>
      if ConstantInfo.name info = target then
        some info
      else
        find? rest target

def contains (env : Env) (target : Name) : Bool :=
  (find? env target).isSome

def findInductive? (env : Env) (target : Name) : Option InductiveSpec :=
  match find? env target with
  | some (.inductive _ _ spec) => some spec
  | _ => none

def findCtor? (env : Env) (target : Name) : Option (List Binder × List Bool) :=
  match find? env target with
  | some (.ctor _ _ _ fields recursive) => some (fields, recursive)
  | _ => none

end Env

def recursorName (indName : Name) : Name :=
  indName ++ ".rec"

def bindTelescopeForall (tele : List Binder) (body : Expr) : Expr :=
  (tele.reverse.foldl
      (fun (state : Expr × Nat) binder =>
        let expr := state.1
        let inner := state.2
        (.forallE binder.name (Expr.lift inner binder.type) expr, inner + 1))
      (body, 0)).1

def bindIndependentForall (binders : List Binder) (body : Expr) : Expr :=
  let rec loop (shift : Nat) (remaining : List Binder) : Expr :=
    match remaining with
    | [] => body
    | binder :: rest =>
        .forallE binder.name (Expr.lift shift binder.type) (loop (shift + 1) rest)
  loop 0 binders

def inductiveTarget (indName : Name) (params : List Expr) : Expr :=
  Expr.mkApps (.const indName) params

def inductiveTypeExpr (spec : InductiveSpec) : Expr :=
  bindTelescopeForall spec.params (.sort spec.level)

def constructorTypeExpr (spec : InductiveSpec) (ctor : ConstructorSpec) : Expr :=
  let paramArgs := Expr.bvarArgs spec.params.length ctor.fields.length
  let target := inductiveTarget spec.name paramArgs
  let withFields := bindIndependentForall ctor.fields target
  bindTelescopeForall spec.params withFields

def inferSortOfPi (domain codomain : Level) : Level :=
  Nat.max domain codomain

def withBinder (ctx : Context) (binder : Binder) : Context :=
  binder :: ctx

def instantiateBinderType (values : List Expr) (binder : Binder) : Expr :=
  Expr.instantiateMany values binder.type

def recursiveTargetExpr (spec : InductiveSpec) : Expr :=
  inductiveTarget spec.name (Expr.bvarArgs spec.params.length 0)

def classifyFieldSyntax (spec : InductiveSpec) (field : Binder) : Result Bool :=
  if field.type = recursiveTargetExpr spec then
    pure true
  else if field.type.occursConst spec.name then
    .error
      s!"recursive field must be a direct occurrence of {spec.name}: {repr field.type}"
  else
    pure false

def caseTypeExpr
    (ctor : ConstructorSpec)
    (recursive : List Bool)
    (params : List Expr)
    (motive : Expr) : Expr :=
  let fieldTypes :=
    ctor.fields.map fun field =>
      { field with type := Expr.instantiateMany params field.type }
  let fieldCount := fieldTypes.length
  let recursiveFieldVars :=
    (List.zip (Expr.bvarArgs fieldCount 0) recursive).filterMap fun pair =>
      match pair.2 with
      | true => some pair.1
      | false => none
  let ihBinders :=
    (List.zip (List.range recursiveFieldVars.length) recursiveFieldVars).map fun pair =>
      {
        name := s!"ih{pair.1}"
        type := .app (Expr.lift fieldCount motive) pair.2
      }
  let totalBinders := fieldCount + ihBinders.length
  let liftedMotive := Expr.lift totalBinders motive
  let liftedParams := params.map (Expr.lift totalBinders)
  let fieldVars := Expr.bvarArgs fieldCount ihBinders.length
  let body :=
    .app liftedMotive (Expr.mkApps (.const ctor.name) (liftedParams ++ fieldVars))
  let withIhs := bindIndependentForall ihBinders body
  bindIndependentForall fieldTypes withIhs

def splitRecursorArgs
    (spec : InductiveSpec)
    (args : List Expr) :
    Option (List Expr × Expr × List Expr × Expr) :=
  let paramCount := spec.params.length
  let caseCount := spec.ctors.length
  if args.length != paramCount + caseCount + 2 then
    none
  else
    let params := args.take paramCount
    let tail := args.drop paramCount
    match tail with
    | motive :: rest =>
        let cases := rest.take caseCount
        match rest.drop caseCount with
        | [target] => some (params, motive, cases, target)
        | _ => none
    | _ => none

def findCtorCase? :
    List ConstructorSpec → List Expr → Name → Option (ConstructorSpec × Expr)
  | ctor :: ctors, case :: cases, target =>
      if ctor.name = target then
        some (ctor, case)
      else
        findCtorCase? ctors cases target
  | _, _, _ => none

def lookupCtx : Context → Nat → Option Binder
  | [], _ => none
  | binder :: _, 0 => some binder
  | _ :: rest, index + 1 => lookupCtx rest index

mutual

partial def inferSort (env : Env) (ctx : Context) (expr : Expr) : Result Level := do
  let inferred ← infer env ctx expr
  let reduced ← whnf env inferred
  match reduced with
  | .sort level => pure level
  | _ => .error s!"expected a type, got {repr reduced}"

partial def checkDefEq (env : Env) (left right : Expr) : Result Unit := do
  let leftNf ← normalize env left
  let rightNf ← normalize env right
  if leftNf.alphaEq rightNf then
    pure ()
  else
    .error s!"definitional equality failed: {repr leftNf} vs {repr rightNf}"

partial def reduceRecursorApp
    (env : Env)
    (indName : Name)
    (args : List Expr) : Result (Option Expr) := do
  let some spec := env.findInductive? indName
    | .error s!"unknown inductive: {indName}"
  let some (params, motive, cases, target) := splitRecursorArgs spec args
    | pure none
  let targetWhnf ← whnf env target
  let head := targetWhnf.getAppFn
  let ctorArgs := targetWhnf.getAppArgs
  let .const ctorName := head
    | pure none
  let some (ctor, minor) := findCtorCase? spec.ctors cases ctorName
    | pure none
  let some (_, recursive) := env.findCtor? ctorName
    | .error s!"unknown constructor: {ctorName}"
  if ctorArgs.length != spec.params.length + ctor.fields.length then
    pure none
  else
    let fieldArgs := ctorArgs.drop spec.params.length
    let recursiveResults :=
      (List.zip fieldArgs recursive).filterMap fun pair =>
        match pair.2 with
        | true =>
            some
              (Expr.mkApps
                (.const (recursorName indName))
                (params ++ motive :: cases ++ [pair.1]))
        | false => none
    pure (some (Expr.mkApps minor (fieldArgs ++ recursiveResults)))

partial def whnf (env : Env) (expr : Expr) : Result Expr := do
  match expr with
  | .app _ _ =>
      let head := expr.getAppFn
      let args := expr.getAppArgs
      let headWhnf ← whnf env head
      let rebuilt := Expr.mkApps headWhnf args
      match headWhnf with
      | .lam _ _ body =>
          match args with
          | [] => pure rebuilt
          | arg :: rest => whnf env (Expr.mkApps (Expr.instantiate1 arg body) rest)
      | .const name =>
          match env.find? name with
          | some (.defn _ _ value) => whnf env (Expr.mkApps value args)
          | some (.recursor _ indName) =>
              match ← reduceRecursorApp env indName args with
              | some reduced => whnf env reduced
              | none => pure rebuilt
          | _ => pure rebuilt
      | .letE _ _ value body =>
          whnf env (Expr.mkApps (Expr.instantiate1 value body) args)
      | _ =>
          if rebuilt = expr then
            pure rebuilt
          else
            whnf env rebuilt
  | .letE _ _ value body => whnf env (Expr.instantiate1 value body)
  | .const name =>
      match env.find? name with
      | some (.defn _ _ value) => whnf env value
      | _ => pure expr
  | _ => pure expr

partial def normalize (env : Env) (expr : Expr) : Result Expr := do
  let reduced ← whnf env expr
  match reduced with
  | .bvar _ => pure reduced
  | .sort _ => pure reduced
  | .const _ => pure reduced
  | .lam name ty body => do
      let ty' ← normalize env ty
      let body' ← normalize env body
      pure (.lam name ty' body')
  | .forallE name ty body => do
      let ty' ← normalize env ty
      let body' ← normalize env body
      pure (.forallE name ty' body')
  | .letE name ty value body => do
      let ty' ← normalize env ty
      let value' ← normalize env value
      let body' ← normalize env body
      let rebuilt := .letE name ty' value' body'
      let whnfRebuilt ← whnf env rebuilt
      if whnfRebuilt = rebuilt then
        pure rebuilt
      else
        normalize env whnfRebuilt
  | .app _ _ => do
      let head := reduced.getAppFn
      let args := reduced.getAppArgs
      let head' ← normalize env head
      let args' ← args.mapM (normalize env)
      let rebuilt := Expr.mkApps head' args'
      let whnfRebuilt ← whnf env rebuilt
      if whnfRebuilt = rebuilt then
        pure rebuilt
      else
        normalize env whnfRebuilt

partial def inferSpine
    (env : Env)
    (ctx : Context)
    (headTy : Expr)
    (args : List Expr) : Result Expr := do
  let rec loop (type : Expr) (restArgs : List Expr) : Result Expr := do
    match restArgs with
    | [] => pure type
    | arg :: rest =>
        let reduced ← whnf env type
        match reduced with
        | .forallE _ domain body =>
            let actual ← infer env ctx arg
            let _ ← checkDefEq env actual domain
            loop (Expr.instantiate1 arg body) rest
        | _ => .error s!"application expects a function, got {repr reduced}"
  loop headTy args

partial def inferRecursorApp
    (env : Env)
    (ctx : Context)
    (indName : Name)
    (args : List Expr) : Result Expr := do
  let some spec := env.findInductive? indName
    | .error s!"unknown inductive: {indName}"
  let some (params, motive, cases, target) := splitRecursorArgs spec args
    | .error s!"recursor {recursorName indName} expects a saturated application"
  let rec checkParams
      (values : List Expr)
      (remainingBinders : List Binder)
      (remainingValues : List Expr) : Result Unit := do
    match remainingBinders, remainingValues with
    | [], [] => pure ()
    | binder :: rest, value :: more =>
        let expected := instantiateBinderType values binder
        let actual ← infer env ctx value
        let _ ← checkDefEq env actual expected
        checkParams (values ++ [value]) rest more
    | _, _ => .error s!"invalid parameter list for {indName}"
  let _ ← checkParams [] spec.params params
  let targetTy := inductiveTarget indName params
  let motiveTy ← infer env ctx motive
  let motiveWhnf ← whnf env motiveTy
  let .forallE _ motiveDomain motiveBody := motiveWhnf
    | .error s!"motive for {recursorName indName} must be a dependent function"
  let _ ← checkDefEq env motiveDomain targetTy
  let _ ← inferSort env ({ name := "_target", type := targetTy } :: ctx) motiveBody
  for pair in List.zip spec.ctors cases do
    let ctor := pair.1
    let caseExpr := pair.2
    let some (_, recursive) := env.findCtor? ctor.name
      | .error s!"unknown constructor: {ctor.name}"
    let expectedCase := caseTypeExpr ctor recursive params motive
    let actualCase ← infer env ctx caseExpr
    let _ ← checkDefEq env actualCase expectedCase
  let actualTarget ← infer env ctx target
  let _ ← checkDefEq env actualTarget targetTy
  pure (.app motive target)

partial def inferApp (env : Env) (ctx : Context) (expr : Expr) : Result Expr := do
  let head := expr.getAppFn
  let args := expr.getAppArgs
  match head with
  | .const name =>
      match env.find? name with
      | some (.recursor _ indName) => inferRecursorApp env ctx indName args
      | _ =>
          let headTy ← infer env ctx head
          inferSpine env ctx headTy args
  | _ =>
      let headTy ← infer env ctx head
      inferSpine env ctx headTy args

partial def infer (env : Env) (ctx : Context) (expr : Expr) : Result Expr := do
  match expr with
  | .bvar index =>
      match lookupCtx ctx index with
      | some binder => pure binder.type
      | none => .error s!"unbound variable #{index}"
  | .sort level => pure (.sort (level + 1))
  | .const name =>
      match env.find? name with
      | some info =>
          match info.type? with
          | some type => pure type
          | none =>
              .error s!"primitive constant {name} requires a saturated application"
      | none => .error s!"unknown constant: {name}"
  | .app _ _ => inferApp env ctx expr
  | .lam name type body => do
      let _ ← inferSort env ctx type
      let bodyTy ← infer env ({ name, type } :: ctx) body
      pure (.forallE name type bodyTy)
  | .forallE name domain body => do
      let domainLevel ← inferSort env ctx domain
      let bodyLevel ← inferSort env ({ name, type := domain } :: ctx) body
      pure (.sort (inferSortOfPi domainLevel bodyLevel))
  | .letE name type value body => do
      let _ ← inferSort env ctx type
      let valueTy ← infer env ctx value
      let _ ← checkDefEq env valueTy type
      let bodyTy ← infer env ({ name, type } :: ctx) body
      pure (Expr.instantiate1 value bodyTy)

end

def checkClosed (what : String) (expr : Expr) : Result Unit :=
  if expr.closed then
    pure ()
  else
    .error s!"{what} must be closed"

def checkFreshName (env : Env) (name : Name) : Result Unit :=
  if env.contains name then
    .error s!"name already exists: {name}"
  else
    pure ()

def checkTelescope (env : Env) (tele : List Binder) : Result Unit := do
  let rec loop (ctx : Context) (remaining : List Binder) : Result Unit := do
    match remaining with
    | [] => pure ()
    | binder :: rest =>
        let _ ← inferSort env ctx binder.type
        loop (withBinder ctx binder) rest
  loop [] tele

def addAxiom (env : Env) (name : Name) (type : Expr) : Result Env := do
  let _ ← checkFreshName env name
  let _ ← checkClosed s!"axiom {name}" type
  let _ ← inferSort env [] type
  pure (.axiom name type :: env)

def addDefinition (env : Env) (name : Name) (type value : Expr) : Result Env := do
  let _ ← checkFreshName env name
  let _ ← checkClosed s!"definition {name} type" type
  let _ ← checkClosed s!"definition {name} value" value
  let _ ← inferSort env [] type
  let valueTy ← infer env [] value
  let _ ← checkDefEq env valueTy type
  pure (.defn name type value :: env)

def addInductive (env : Env) (spec : InductiveSpec) : Result Env := do
  let _ ← checkFreshName env spec.name
  let _ ← checkFreshName env (recursorName spec.name)
  for ctor in spec.ctors do
    let _ ← checkFreshName env ctor.name
  let _ ← checkTelescope env spec.params
  let indType := inductiveTypeExpr spec
  let tempEnv := .inductive spec.name indType spec :: env
  let paramCtx := spec.params.reverse
  for ctor in spec.ctors do
    for field in ctor.fields do
      let _ ← inferSort tempEnv paramCtx field.type
  let recursiveFlags ←
    spec.ctors.mapM fun ctor =>
      ctor.fields.mapM (classifyFieldSyntax spec)
  let ctorInfos :=
    (List.zip spec.ctors recursiveFlags).map fun pair =>
      .ctor
        pair.1.name
        (constructorTypeExpr spec pair.1)
        spec.name
        pair.1.fields
        pair.2
  let recInfo := .recursor (recursorName spec.name) spec.name
  pure (recInfo :: ctorInfos.reverse ++ tempEnv)

end LeanLean
