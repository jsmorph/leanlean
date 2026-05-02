import LeanLean.Syntax

namespace LeanLean

structure Binder where
  name : String
  type : Expr
  deriving DecidableEq, Repr, Inhabited

abbrev Telescope := List Binder
abbrev Context := List Binder
abbrev Result := Except String

namespace Telescope

def toContext (tele : Telescope) : Context :=
  tele.reverse

def withBinder (ctx : Context) (binder : Binder) : Context :=
  binder :: ctx

def bindForall (tele : Telescope) (body : Expr) : Expr :=
  let rec loop : Telescope → Expr
    | [] => body
    | binder :: rest =>
        .forallE binder.name binder.type (loop rest)
  loop tele

def bindIndependentForall (tele : Telescope) (body : Expr) : Expr :=
  let rec loop (shift : Nat) (remaining : Telescope) : Expr :=
    match remaining with
    | [] => body
    | binder :: rest =>
        .forallE binder.name (Expr.lift shift binder.type) (loop (shift + 1) rest)
  loop 0 tele

def instantiateTypes (values : List Expr) (tele : Telescope) : Telescope :=
  tele.map fun binder =>
    { binder with type := Expr.instantiateMany values binder.type }

def bindForallM
    (paramVars : List Expr)
    (locals : Telescope)
    (buildBody : List Expr → List Expr → Result Expr) : Result Expr := do
  let rec loop
      (paramVars : List Expr)
      (localVars : List Expr) : Telescope → Result Expr
    | [] => buildBody paramVars localVars
    | binder :: rest => do
        let ty := Expr.instantiateMany (paramVars ++ localVars) binder.type
        let body ←
          loop
            (paramVars.map (Expr.lift 1))
            (localVars.map (Expr.lift 1) ++ [.bvar 0])
            rest
        pure (.forallE binder.name ty body)
  loop paramVars [] locals

end Telescope

structure ConstructorSpec where
  name : Name
  fields : Telescope
  deriving DecidableEq, Repr, Inhabited

structure InductiveSpec where
  name : Name
  params : Telescope
  level : Level
  ctors : List ConstructorSpec
  deriving DecidableEq, Repr, Inhabited

structure TargetSchema where
  locals : Telescope
  target : Expr
  headName : Name
  deriving DecidableEq, Repr, Inhabited

inductive RawFieldShape where
  | none : RawFieldShape
  | direct : RawFieldShape
  | pi : Binder → RawFieldShape → RawFieldShape
  | nested : TargetSchema → RawFieldShape
  deriving DecidableEq, Repr, Inhabited

inductive FieldShape where
  | none : FieldShape
  | direct : FieldShape
  | pi : Binder → FieldShape → FieldShape
  | nested : Nat → FieldShape
  deriving DecidableEq, Repr, Inhabited

structure FamilyField where
  binder : Binder
  shape : FieldShape
  deriving DecidableEq, Repr, Inhabited

structure FamilyCtor where
  name : Name
  fields : List FamilyField
  deriving DecidableEq, Repr, Inhabited

structure FamilyTarget where
  recName : Name
  schema : TargetSchema
  ctors : List FamilyCtor
  deriving DecidableEq, Repr, Inhabited

structure RecursorFamily where
  rootName : Name
  params : Telescope
  targets : List FamilyTarget
  deriving DecidableEq, Repr, Inhabited

structure InductiveInfo where
  type : Expr
  spec : InductiveSpec
  positiveParams : List Bool
  deriving DecidableEq, Repr, Inhabited

inductive ConstantInfo where
  | axiom : Name → List Name → Expr → ConstantInfo
  | defn : Name → List Name → Expr → Expr → ConstantInfo
  | inductive : Name → List Name → InductiveInfo → ConstantInfo
  | ctor : Name → List Name → Expr → Name → ConstantInfo
  | recursor : Name → List Name → Expr → Nat → RecursorFamily → ConstantInfo
  deriving DecidableEq, Repr, Inhabited

abbrev Env := List ConstantInfo

namespace ConstantInfo

def name : ConstantInfo → Name
  | .axiom name _ _ => name
  | .defn name _ _ _ => name
  | .inductive name _ _ => name
  | .ctor name _ _ _ => name
  | .recursor name _ _ _ _ => name

def levelParams : ConstantInfo → List Name
  | .axiom _ params _ => params
  | .defn _ params _ _ => params
  | .inductive _ params _ => params
  | .ctor _ params _ _ => params
  | .recursor _ params _ _ _ => params

def checkLevels (info : ConstantInfo) (levels : List Level) : Result Unit := do
  let params := info.levelParams
  if levels.length != params.length then
    .error
      s!"constant {info.name} expects {params.length} universe arguments, \
         but got {levels.length}"
  else if !levels.all Level.closed then
    .error s!"constant {info.name} requires closed universe arguments"
  else
    pure ()

def instantiateExpr
    (constName : Name)
    (what : String)
    (params : List Name)
    (levels : List Level)
    (expr : Expr) : Result Expr :=
  if levels.length != params.length then
    .error
      s!"constant {constName} expects {params.length} universe arguments in its {what}, \
         but got {levels.length}"
  else if !levels.all Level.closed then
    .error s!"constant {constName} requires closed universe arguments in its {what}"
  else
    pure (Expr.instantiateLevels params levels expr)

def type (info : ConstantInfo) (levels : List Level) : Result Expr :=
  match info with
  | .axiom name params type =>
      instantiateExpr name "type" params levels type
  | .defn name params type _ =>
      instantiateExpr name "type" params levels type
  | .inductive name params indInfo =>
      instantiateExpr name "type" params levels indInfo.type
  | .ctor name params type _ =>
      instantiateExpr name "type" params levels type
  | .recursor name params type _ _ =>
      instantiateExpr name "type" params levels type

def value? (info : ConstantInfo) (levels : List Level) : Result (Option Expr) :=
  match info with
  | .defn name params _ value =>
      some <$> instantiateExpr name "value" params levels value
  | _ => pure none

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

def findInductive? (env : Env) (target : Name) : Option InductiveInfo :=
  match find? env target with
  | some (.inductive _ _ info) => some info
  | _ => none

def findCtor? (env : Env) (target : Name) : Option Name :=
  match find? env target with
  | some (.ctor _ _ _ indName) => some indName
  | _ => none

def findRecursor? (env : Env) (target : Name) : Option (Nat × RecursorFamily) :=
  match find? env target with
  | some (.recursor _ _ _ index family) => some (index, family)
  | _ => none

end Env

def recursorName (indName : Name) : Name :=
  indName ++ ".rec"

def recursorLevelParam : Name :=
  "u"

def recursorLevelParams : List Name :=
  [recursorLevelParam]

def inductiveTarget (indName : Name) (params : List Expr) : Expr :=
  Expr.mkApps (.const indName []) params

def inductiveTypeExpr (spec : InductiveSpec) : Expr :=
  Telescope.bindForall spec.params (.sort spec.level)

def constructorTypeExpr (spec : InductiveSpec) (ctor : ConstructorSpec) : Expr :=
  let paramArgs := Expr.bvarArgs spec.params.length ctor.fields.length
  let target := inductiveTarget spec.name paramArgs
  let withFields := Telescope.bindIndependentForall ctor.fields target
  Telescope.bindForall spec.params withFields

def inferSortOfPi (domain codomain : Level) : Level :=
  Level.normalize (.max domain codomain)

def recursiveTargetExpr (spec : InductiveSpec) : Expr :=
  inductiveTarget spec.name (Expr.bvarArgs spec.params.length 0)

def helperRecursorName (indName : Name) (index : Nat) : Name :=
  recursorName indName ++ "_" ++ toString index

def rawShapeHasIH : RawFieldShape → Bool
  | .none => false
  | .direct => true
  | .pi _ body => rawShapeHasIH body
  | .nested _ => true

def shapeHasIH : FieldShape → Bool
  | .none => false
  | .direct => true
  | .pi _ body => shapeHasIH body
  | .nested _ => true

def rawShapeSchemas : RawFieldShape → List TargetSchema
  | .none => []
  | .direct => []
  | .pi _ body => rawShapeSchemas body
  | .nested schema => [schema]

def schemaEq (left right : TargetSchema) : Bool :=
  left.locals.length = right.locals.length &&
    ((List.zip left.locals right.locals).all fun pair =>
      pair.1.type.alphaEq pair.2.type) &&
    left.target.alphaEq right.target

def containsExprAt (target : Expr) (depth : Nat) (expr : Expr) : Bool :=
  if expr = Expr.lift depth target then
    true
  else
    match expr with
    | .bvar _ => false
    | .sort _ => false
    | .const _ _ => false
    | .app fn arg => containsExprAt target depth fn || containsExprAt target depth arg
    | .lam _ ty body =>
        containsExprAt target depth ty || containsExprAt target (depth + 1) body
    | .forallE _ ty body =>
        containsExprAt target depth ty || containsExprAt target (depth + 1) body
    | .letE _ ty val body =>
        containsExprAt target depth ty ||
        containsExprAt target depth val ||
        containsExprAt target (depth + 1) body
termination_by expr

def containsBVarAt (targetIndex depth : Nat) (expr : Expr) : Bool :=
  match expr with
  | .bvar index => index = targetIndex + depth
  | .sort _ => false
  | .const _ _ => false
  | .app fn arg => containsBVarAt targetIndex depth fn || containsBVarAt targetIndex depth arg
  | .lam _ ty body =>
      containsBVarAt targetIndex depth ty || containsBVarAt targetIndex (depth + 1) body
  | .forallE _ ty body =>
      containsBVarAt targetIndex depth ty || containsBVarAt targetIndex (depth + 1) body
  | .letE _ ty val body =>
      containsBVarAt targetIndex depth ty ||
      containsBVarAt targetIndex depth val ||
      containsBVarAt targetIndex (depth + 1) body
termination_by expr

def paramBaseIndex (paramCount paramIndex : Nat) : Nat :=
  paramCount - 1 - paramIndex

def decomposeInductiveApp (env : Env) (expr : Expr) :
    Option (Name × InductiveInfo × List Expr) :=
  let head := expr.getAppFn
  let args := expr.getAppArgs
  match head with
  | .const name levels =>
      if !levels.isEmpty then
        none
      else match env.findInductive? name with
      | some info =>
          if args.length = info.spec.params.length then
            some (name, info, args)
          else
            none
      | none => none
  | _ => none

def listGet? : List α → Nat → Option α
  | [], _ => none
  | value :: _, 0 => some value
  | _ :: rest, index + 1 => listGet? rest index

def findSchemaIndex? (schemas : List TargetSchema) (target : TargetSchema) : Option Nat :=
  let rec loop (index : Nat) : List TargetSchema → Option Nat
    | [] => none
    | schema :: rest =>
        if schemaEq schema target then
          some index
        else
          loop (index + 1) rest
  loop 0 schemas

def internSchema (schemas : List TargetSchema) (target : TargetSchema) : Nat × List TargetSchema :=
  match findSchemaIndex? schemas target with
  | some index => (index, schemas)
  | none => (schemas.length, schemas ++ [target])

def familyRecName (rootName : Name) (index : Nat) : Name :=
  if index = 0 then
    recursorName rootName
  else
    helperRecursorName rootName index

def instantiateTargetSchema
    (params : List Expr)
    (locals : List Expr)
    (schema : TargetSchema) : Expr :=
  Expr.instantiateMany (params ++ locals) schema.target

structure RecursorSplit where
  params : List Expr
  motives : List Expr
  minors : List Expr
  locals : List Expr
  target : Expr

structure MinorEntry where
  targetIndex : Nat
  target : FamilyTarget
  ctor : FamilyCtor

def familyMinorEntries (family : RecursorFamily) : List MinorEntry :=
  (List.zip (List.range family.targets.length) family.targets).foldr
    (fun pair rest =>
      pair.2.ctors.map (fun ctor => { targetIndex := pair.1, target := pair.2, ctor }) ++ rest)
    []

def familyMinorCount (family : RecursorFamily) : Nat :=
  (familyMinorEntries family).length

def splitFamilyRecursorArgs
    (family : RecursorFamily)
    (targetIndex : Nat)
    (args : List Expr) : Option RecursorSplit := do
  let targetInfo ← listGet? family.targets targetIndex
  let paramCount := family.params.length
  let motiveCount := family.targets.length
  let minorCount := familyMinorCount family
  let localCount := targetInfo.schema.locals.length
  if args.length != paramCount + motiveCount + minorCount + localCount + 1 then
    none
  else
    let params := args.take paramCount
    let rest := args.drop paramCount
    let motives := rest.take motiveCount
    let rest := rest.drop motiveCount
    let minors := rest.take minorCount
    let rest := rest.drop minorCount
    let locals := rest.take localCount
    match rest.drop localCount with
    | [target] => some { params, motives, minors, locals, target }
    | _ => none

def lookupMinorExpr?
    (family : RecursorFamily)
    (minors : List Expr)
    (targetIndex : Nat)
    (ctorName : Name) : Option Expr := do
  let entries := familyMinorEntries family
  let index ← entries.findIdx? fun entry =>
    entry.targetIndex = targetIndex && entry.ctor.name = ctorName
  listGet? minors index

partial def ihTypeExpr
    (family : RecursorFamily)
    (motives : List Expr)
    (paramVars : List Expr)
    (localVars : List Expr)
    (shape : FieldShape)
    (fieldExpr : Expr) : Result Expr := do
  match shape with
  | .none => .error "internal error: missing induction hypothesis"
  | .direct =>
      let some motive := listGet? motives 0
        | .error "internal error: missing root motive"
      pure (.app motive fieldExpr)
  | .nested targetIndex =>
      let some target := listGet? family.targets targetIndex
        | .error s!"internal error: unknown nested target index {targetIndex}"
      if target.schema.locals.length != localVars.length then
        .error s!"internal error: nested target #{targetIndex} expects {target.schema.locals.length} locals, got {localVars.length}"
      else
        let some motive := listGet? motives targetIndex
          | .error s!"internal error: missing motive for nested target #{targetIndex}"
        pure (Expr.mkApps motive (localVars ++ [fieldExpr]))
  | .pi binder body => do
      let dom := Expr.instantiateMany (paramVars ++ localVars) binder.type
      let bodyField := .app (Expr.lift 1 fieldExpr) (.bvar 0)
      let bodyTy ←
        ihTypeExpr
          family
          (motives.map (Expr.lift 1))
          (paramVars.map (Expr.lift 1))
          (localVars.map (Expr.lift 1) ++ [.bvar 0])
          body
          bodyField
      pure (.forallE binder.name dom bodyTy)

partial def ihTerm
    (family : RecursorFamily)
    (levels : List Level)
    (prefixArgs : List Expr)
    (paramVars : List Expr)
    (localVars : List Expr)
    (shape : FieldShape)
    (fieldExpr : Expr) : Result Expr := do
  match shape with
  | .none => .error "internal error: missing induction hypothesis term"
  | .direct =>
      let some firstTarget := listGet? family.targets 0
        | .error "internal error: missing root target"
      pure (Expr.mkApps (.const firstTarget.recName levels) (prefixArgs ++ [fieldExpr]))
  | .nested targetIndex =>
      let some target := listGet? family.targets targetIndex
        | .error s!"internal error: unknown nested target index {targetIndex}"
      if target.schema.locals.length != localVars.length then
        .error s!"internal error: nested target #{targetIndex} expects {target.schema.locals.length} locals, got {localVars.length}"
      else
        pure (Expr.mkApps (.const target.recName levels) (prefixArgs ++ localVars ++ [fieldExpr]))
  | .pi binder body => do
      let dom := Expr.instantiateMany (paramVars ++ localVars) binder.type
      let bodyField := .app (Expr.lift 1 fieldExpr) (.bvar 0)
      let bodyTerm ←
        ihTerm
          family
          levels
          (prefixArgs.map (Expr.lift 1))
          (paramVars.map (Expr.lift 1))
          (localVars.map (Expr.lift 1) ++ [.bvar 0])
          body
          bodyField
      pure (.lam binder.name dom bodyTerm)

partial def familyCtorMinorType
    (family : RecursorFamily)
    (paramVars : List Expr)
    (motives : List Expr)
    (targetIndex : Nat)
    (target : FamilyTarget)
    (ctor : FamilyCtor) : Result Expr := do
  Telescope.bindForallM paramVars target.schema.locals fun paramVars localVars => do
    let motiveVars := motives.map (Expr.lift target.schema.locals.length)
    let some motive := listGet? motiveVars targetIndex
      | .error s!"internal error: missing motive for target #{targetIndex}"
    let fieldBinders : Telescope :=
      Telescope.instantiateTypes (paramVars ++ localVars) (ctor.fields.map fun field => field.binder)
    let fieldVarsForIH := Expr.bvarArgs fieldBinders.length 0
    let motivesForIH := motiveVars.map (Expr.lift fieldBinders.length)
    let paramVarsForIH := paramVars.map (Expr.lift fieldBinders.length)
    let localVarsForIH := localVars.map (Expr.lift fieldBinders.length)
    let mut ihBinders : Telescope := []
    let mut ihIndex := 0
    for pair in List.zip ctor.fields fieldVarsForIH do
      let field := pair.1
      let fieldVar := pair.2
      if shapeHasIH field.shape then
        let ihTy ←
          ihTypeExpr
            family
            motivesForIH
            paramVarsForIH
            localVarsForIH
            field.shape
            fieldVar
        ihBinders := ihBinders ++ [{ name := s!"ih{ihIndex}", type := ihTy }]
        ihIndex := ihIndex + 1
    let targetExpr := instantiateTargetSchema paramVars localVars target.schema
    let totalBinders := fieldBinders.length + ihBinders.length
    let liftedMotive := Expr.lift totalBinders motive
    let liftedLocalVars := localVars.map (Expr.lift totalBinders)
    let liftedTargetArgs := targetExpr.getAppArgs.map (Expr.lift totalBinders)
    let fieldVars := Expr.bvarArgs fieldBinders.length ihBinders.length
    let ctorApp := Expr.mkApps (.const ctor.name []) (liftedTargetArgs ++ fieldVars)
    let body := Expr.mkApps liftedMotive (liftedLocalVars ++ [ctorApp])
    let withIhs := Telescope.bindIndependentForall ihBinders body
    pure (Telescope.bindIndependentForall fieldBinders withIhs)

def motiveBinderType
    (paramVars : List Expr)
    (motiveLevel : Level)
    (target : FamilyTarget) : Result Expr := do
  Telescope.bindForallM paramVars target.schema.locals fun paramVars localVars => do
    pure (.forallE "t" (instantiateTargetSchema paramVars localVars target.schema) (.sort motiveLevel))

partial def buildRecursorType
    (family : RecursorFamily)
    (targetIndex : Nat) : Result Expr := do
  let motiveLevel : Level := .param recursorLevelParam
  let paramCount := family.params.length
  let motiveCount := family.targets.length
  let minorEntries := familyMinorEntries family
  let minorCount := minorEntries.length
  let motiveBinders ←
    (List.zip (List.range motiveCount) family.targets).mapM fun pair => do
      let shift := pair.1
      let paramVars := Expr.bvarArgs paramCount shift
      let type ← motiveBinderType paramVars motiveLevel pair.2
      pure { name := s!"motive_{pair.1 + 1}", type }
  let minorBinders ←
    (List.zip (List.range minorCount) minorEntries).mapM fun pair => do
      let shift := motiveCount + pair.1
      let paramVars := Expr.bvarArgs paramCount shift
      let motiveVars := Expr.bvarArgs motiveCount pair.1
      let minorTy ←
        familyCtorMinorType
          family
          paramVars
          motiveVars
          pair.2.targetIndex
          pair.2.target
          pair.2.ctor
      pure { name := s!"minor_{pair.1}", type := minorTy }
  let some targetInfo := listGet? family.targets targetIndex
    | .error s!"internal error: invalid recursor index {targetIndex}"
  let targetType ←
    Telescope.bindForallM
      (Expr.bvarArgs paramCount (motiveCount + minorCount))
      targetInfo.schema.locals
      fun paramVars localVars => do
        let targetExpr := instantiateTargetSchema paramVars localVars targetInfo.schema
        let motiveVars :=
          (Expr.bvarArgs motiveCount minorCount).map (Expr.lift targetInfo.schema.locals.length)
        let some motive := listGet? motiveVars targetIndex
          | .error s!"internal error: missing motive #{targetIndex}"
        let body := Expr.mkApps (Expr.lift 1 motive) (localVars.map (Expr.lift 1) ++ [.bvar 0])
        pure (.forallE "t" targetExpr body)
  pure (Telescope.bindForall (family.params ++ motiveBinders ++ minorBinders) targetType)

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

partial def checkRecursorTargetArgs
    (env : Env)
    (recName : Name)
    (actual expected : List Expr) : Result Unit := do
  if actual.length != expected.length then
    .error s!"internal error: mismatched target argument arity for {recName}"
  else
    for pair in List.zip actual expected do
      try
        let _ ← checkDefEq env pair.1 pair.2
        pure ()
      catch _ =>
        .error s!"recursor target does not match its explicit schema arguments for {recName}"

partial def reduceRecursorApp
    (env : Env)
    (recName : Name)
    (levels : List Level)
    (args : List Expr) : Result (Option Expr) := do
  let some (targetIndex, family) := env.findRecursor? recName
    | .error s!"unknown recursor: {recName}"
  let some split := splitFamilyRecursorArgs family targetIndex args
    | pure none
  let some targetInfo := listGet? family.targets targetIndex
    | .error s!"internal error: invalid recursor index for {recName}"
  let targetWhnf ← whnf env split.target
  let head := targetWhnf.getAppFn
  let ctorArgs := targetWhnf.getAppArgs
  let .const ctorName ctorLevels := head
    | pure none
  if !ctorLevels.isEmpty then
    pure none
  else
    let some ctor := targetInfo.ctors.find? fun ctor => ctor.name = ctorName
      | pure none
    let targetExpr := instantiateTargetSchema split.params split.locals targetInfo.schema
    if ctorArgs.length != targetExpr.getAppArgs.length + ctor.fields.length then
      pure none
    else
      let targetArgs := ctorArgs.take targetExpr.getAppArgs.length
      let _ ← checkRecursorTargetArgs env recName targetArgs targetExpr.getAppArgs
      let fieldArgs := ctorArgs.drop targetExpr.getAppArgs.length
      let prefixArgs := split.params ++ split.motives ++ split.minors
      let mut ihTerms : List Expr := []
      for pair in List.zip ctor.fields fieldArgs do
        let field := pair.1
        let fieldArg := pair.2
        if shapeHasIH field.shape then
          let ih ← ihTerm family levels prefixArgs split.params split.locals field.shape fieldArg
          ihTerms := ihTerms ++ [ih]
      let some minor := lookupMinorExpr? family split.minors targetIndex ctor.name
        | .error s!"internal error: missing minor premise for {ctor.name}"
      pure (some (Expr.mkApps minor (split.locals ++ fieldArgs ++ ihTerms)))

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
      | .const name levels =>
          match env.find? name with
          | some info =>
              let _ ← info.checkLevels levels
              match ← info.value? levels with
              | some value => whnf env (Expr.mkApps value args)
              | none =>
                  match info with
                  | .recursor _ _ _ _ _ =>
                      match ← reduceRecursorApp env name levels args with
                      | some reduced => whnf env reduced
                      | none => pure rebuilt
                  | _ => pure rebuilt
          | none => .error s!"unknown constant: {name}"
      | .letE _ _ value body =>
          whnf env (Expr.mkApps (Expr.instantiate1 value body) args)
      | _ =>
          if rebuilt = expr then
            pure rebuilt
          else
            whnf env rebuilt
  | .letE _ _ value body => whnf env (Expr.instantiate1 value body)
  | .const name levels =>
      match env.find? name with
      | some info =>
          let _ ← info.checkLevels levels
          match ← info.value? levels with
          | some value => whnf env value
          | none => pure expr
      | _ => .error s!"unknown constant: {name}"
  | _ => pure expr

partial def normalize (env : Env) (expr : Expr) : Result Expr := do
  let reduced ← whnf env expr
  match reduced with
  | .bvar _ => pure reduced
  | .sort _ => pure reduced
  | .const _ _ => pure reduced
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

partial def inferApp (env : Env) (ctx : Context) (expr : Expr) : Result Expr := do
  let head := expr.getAppFn
  let args := expr.getAppArgs
  let headTy ← infer env ctx head
  inferSpine env ctx headTy args

partial def infer (env : Env) (ctx : Context) (expr : Expr) : Result Expr := do
  match expr with
  | .bvar index =>
      match lookupCtx ctx index with
      | some binder => pure (Expr.lift (index + 1) binder.type)
      | none => .error s!"unbound variable #{index}"
  | .sort level =>
      if level.closed then
        pure (.sort (.succ level))
      else
        .error s!"sort level must be closed: {repr level}"
  | .const name levels =>
      match env.find? name with
      | some info =>
          let _ ← info.checkLevels levels
          info.type levels
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

def normalizeForInductiveAnalysis (env : Env) (expr : Expr) : Result Expr :=
  normalize env expr

partial def positiveParamOccurrence
    (env : Env)
    (self : InductiveSpec)
    (selfPositive : List Bool)
    (targetIndex depth : Nat)
    (expr : Expr) : Result Bool := do
  let expr ← normalizeForInductiveAnalysis env expr
  if expr = Expr.bvar (targetIndex + depth) then
    pure true
  else
    match expr with
    | .bvar _ => pure false
    | .sort _ => pure false
    | .const _ _ => pure false
    | .letE _ _ _ _ =>
        .error s!"unexpected let-expression in positivity check: {repr expr}"
    | .lam _ _ _ =>
        .error s!"unexpected lambda in positivity check: {repr expr}"
    | .forallE _ dom body =>
        if containsBVarAt targetIndex depth dom then
          .error s!"non-positive parameter occurrence in {repr expr}"
        else
          positiveParamOccurrence env self selfPositive targetIndex (depth + 1) body
    | .app _ _ =>
        match decomposeInductiveApp env expr with
        | some (headName, info, args) =>
            let positiveFlags :=
              if headName = self.name then
                selfPositive
              else
                info.positiveParams
            let mut found := false
            for pair in List.zip args positiveFlags do
              let arg := pair.1
              let isPositive := pair.2
              let occurs := containsBVarAt targetIndex depth arg
              if occurs then
                if !isPositive then
                  .error s!"parameter occurs in a non-positive argument of {headName}"
                let nested ←
                  positiveParamOccurrence env self selfPositive targetIndex depth arg
                if nested then
                  found := true
            pure found
        | none =>
            if containsBVarAt targetIndex depth expr then
              .error s!"non-positive parameter occurrence in {repr expr}"
            else
              pure false

def computePositiveParams (env : Env) (spec : InductiveSpec) : Result (List Bool) := do
  let paramCount := spec.params.length
  let rec iterate (flags : List Bool) : Nat → Result (List Bool)
    | 0 => pure flags
    | fuel + 1 => do
        let next ←
          (List.range paramCount).mapM fun index => do
            let baseIndex := paramBaseIndex paramCount index
            let mut positive := true
            for ctor in spec.ctors do
              for field in ctor.fields do
                match positiveParamOccurrence env spec flags baseIndex 0 field.type with
                | .ok _ => pure ()
                | .error _ => positive := false
                if !positive then
                  break
              if !positive then
                break
            pure positive
        if next = flags then
          pure next
        else
          iterate next fuel
  iterate (List.replicate paramCount true) paramCount

partial def analyzeRecursiveShape
    (env : Env)
    (root : InductiveInfo)
    (locals : Telescope)
    (expr : Expr) : Result RawFieldShape := do
  let expr ← normalizeForInductiveAnalysis env expr
  let target := Expr.lift locals.length (recursiveTargetExpr root.spec)
  if expr = target then
    pure .direct
  else
    match expr with
    | .bvar _ => pure .none
    | .sort _ => pure .none
    | .const _ _ => pure .none
    | .letE _ _ _ _ =>
        .error s!"unexpected let-expression in positivity check: {repr expr}"
    | .lam _ _ _ =>
        .error s!"unexpected lambda in positivity check: {repr expr}"
    | .forallE name dom body =>
        let dom ← normalizeForInductiveAnalysis env dom
        if containsExprAt (recursiveTargetExpr root.spec) locals.length dom then
          .error s!"non-positive recursive occurrence in {repr expr}"
        else
          let binder : Binder := { name, type := dom }
          let bodyShape ← analyzeRecursiveShape env root (locals ++ [binder]) body
          match bodyShape with
          | .none => pure .none
          | _ => pure (.pi binder bodyShape)
    | .app _ _ =>
        match decomposeInductiveApp env expr with
        | some (headName, info, args) =>
            if headName = root.spec.name then
              .error s!"recursive occurrence must be {repr target}"
            let mut found := false
            for pair in List.zip args info.positiveParams do
              let arg := pair.1
              let isPositive := pair.2
              let occurs := containsExprAt (recursiveTargetExpr root.spec) locals.length arg
              if occurs then
                if !isPositive then
                  .error s!"recursive occurrence appears in a non-positive argument of {headName}"
                let shape ← analyzeRecursiveShape env root locals arg
                if rawShapeHasIH shape then
                  found := true
            if found then
              pure (.nested { locals, target := expr, headName })
            else
              pure .none
        | none =>
            if containsExprAt (recursiveTargetExpr root.spec) locals.length expr then
              .error s!"non-positive recursive occurrence in {repr expr}"
            else
              pure .none

partial def internFieldShape
    (schemas : List TargetSchema)
    (shape : RawFieldShape) : Result (FieldShape × List TargetSchema) := do
  match shape with
  | .none => pure (.none, schemas)
  | .direct => pure (.direct, schemas)
  | .pi binder body => do
      let (bodyShape, schemas) ← internFieldShape schemas body
      pure (.pi binder bodyShape, schemas)
  | .nested schema =>
      let (index, schemas) := internSchema schemas schema
      pure (.nested index, schemas)

partial def buildRecursorFamily
    (env : Env)
    (root : InductiveInfo) : Result RecursorFamily := do
  let rootTarget ← normalizeForInductiveAnalysis env (recursiveTargetExpr root.spec)
  let rootSchema : TargetSchema := { locals := [], target := rootTarget, headName := root.spec.name }
  let rec loop
      (schemas : List TargetSchema)
      (built : List FamilyTarget) : Result (List FamilyTarget) := do
    if built.length = schemas.length then
      pure built
    else
      let some schema := listGet? schemas built.length
        | .error s!"internal error: missing family target #{built.length}"
      let some (headName, info, args) := decomposeInductiveApp env schema.target
        | .error s!"internal error: invalid family target {repr schema.target}"
      if headName != schema.headName then
        .error s!"internal error: family target head mismatch for {repr schema.target}"
      else
        let index := built.length
        let targetName := familyRecName root.spec.name index
        let rec buildFields
            (currentSchemas : List TargetSchema)
            (remaining : Telescope) : Result (List FamilyField × List TargetSchema) := do
          match remaining with
          | [] => pure ([], currentSchemas)
          | field :: rest =>
              let rawShape ← analyzeRecursiveShape env root schema.locals field.type
              let (shape, currentSchemas) ← internFieldShape currentSchemas rawShape
              let (restFields, currentSchemas) ← buildFields currentSchemas rest
              pure ({ binder := field, shape } :: restFields, currentSchemas)
        let rec buildCtors
            (currentSchemas : List TargetSchema)
            (remaining : List ConstructorSpec) : Result (List FamilyCtor × List TargetSchema) := do
          match remaining with
          | [] => pure ([], currentSchemas)
          | ctor :: rest => do
              let instantiated := Telescope.instantiateTypes args ctor.fields
              let specialized ←
                instantiated.mapM fun field => do
                  let type ← normalizeForInductiveAnalysis env field.type
                  pure { field with type }
              let (fields, currentSchemas) ← buildFields currentSchemas specialized
              let (restCtors, currentSchemas) ← buildCtors currentSchemas rest
              pure ({ name := ctor.name, fields } :: restCtors, currentSchemas)
        let (ctors, currentSchemas) ← buildCtors schemas info.spec.ctors
        let target : FamilyTarget :=
          { recName := targetName, schema, ctors }
        loop currentSchemas (built ++ [target])
  let targets ← loop [rootSchema] []
  pure { rootName := root.spec.name, params := root.spec.params, targets }

def checkClosed (what : String) (expr : Expr) : Result Unit :=
  if expr.closed then
    pure ()
  else
    .error s!"{what} must be closed"

def validateGeneratedType
    (env : Env)
    (what : String)
    (levelParams : List Name)
    (type : Expr) : Result Unit := do
  let levels := List.replicate levelParams.length (0 : Level)
  let instantiated := Expr.instantiateLevels levelParams levels type
  let _ ← checkClosed what instantiated
  let _ ← inferSort env [] instantiated

def checkFreshName (env : Env) (name : Name) : Result Unit :=
  if env.contains name then
    .error s!"name already exists: {name}"
  else
    pure ()

def checkLevelAtMost
    (what : String)
    (actual bound : Level) : Result Unit :=
  if Level.le actual bound then
    pure ()
  else
    .error
      s!"{what} requires universe {repr (Level.normalize actual)}, \
         but the inductive result is only {repr (Level.normalize bound)}"

partial def inferBinderUniverse
    (env : Env)
    (ctx : Context)
    (type : Expr) : Result Level := do
  let reduced ← whnf env type
  match reduced with
  | .sort level => pure level
  | _ => inferSort env ctx type

def checkTelescope (env : Env) (tele : Telescope) : Result Unit := do
  let rec loop (ctx : Context) (remaining : Telescope) : Result Unit := do
    match remaining with
    | [] => pure ()
    | binder :: rest =>
        let _ ← inferSort env ctx binder.type
        loop (Telescope.withBinder ctx binder) rest
  loop [] tele

def addAxiom (env : Env) (name : Name) (type : Expr) : Result Env := do
  let _ ← checkFreshName env name
  let _ ← checkClosed s!"axiom {name}" type
  let _ ← inferSort env [] type
  pure (.axiom name [] type :: env)

def addDefinition (env : Env) (name : Name) (type value : Expr) : Result Env := do
  let _ ← checkFreshName env name
  let _ ← checkClosed s!"definition {name} type" type
  let _ ← checkClosed s!"definition {name} value" value
  let _ ← inferSort env [] type
  let valueTy ← infer env [] value
  let _ ← checkDefEq env valueTy type
  pure (.defn name [] type value :: env)

def addInductive (env : Env) (spec : InductiveSpec) : Result Env := do
  if !spec.level.closed then
    .error s!"inductive result universe must be closed: {repr spec.level}"
  let _ ← checkFreshName env spec.name
  let _ ← checkFreshName env (recursorName spec.name)
  let mut seenNames := [spec.name, recursorName spec.name]
  for ctor in spec.ctors do
    if seenNames.contains ctor.name then
      .error s!"duplicate name in inductive declaration: {ctor.name}"
    let _ ← checkFreshName env ctor.name
    seenNames := ctor.name :: seenNames
  let _ ← checkTelescope env spec.params
  let indType := inductiveTypeExpr spec
  let provisionalInfo : InductiveInfo :=
    {
      type := indType
      spec
      positiveParams := List.replicate spec.params.length true
    }
  let tempEnv := .inductive spec.name [] provisionalInfo :: env
  let paramCtx := Telescope.toContext spec.params
  if !spec.ctors.isEmpty then
    let rec checkParamLevels (ctx : Context) : Telescope → Result Unit
      | [] => pure ()
      | binder :: rest => do
          let level ← inferBinderUniverse env ctx binder.type
          let _ ←
            checkLevelAtMost
              s!"parameter {binder.name}"
              level
              spec.level
          checkParamLevels (Telescope.withBinder ctx binder) rest
    let _ ← checkParamLevels [] spec.params
  for ctor in spec.ctors do
    for field in ctor.fields do
      let level ← inferSort tempEnv paramCtx field.type
      let _ ←
        checkLevelAtMost
          s!"field {ctor.name}.{field.name}"
          level
          spec.level
  let positiveParams ← computePositiveParams tempEnv spec
  let info : InductiveInfo := { type := indType, spec, positiveParams }
  let infoEnv := .inductive spec.name [] info :: env
  let family ← buildRecursorFamily infoEnv info
  for target in family.targets.drop 1 do
    if seenNames.contains target.recName then
      .error s!"duplicate name in inductive declaration: {target.recName}"
    let _ ← checkFreshName env target.recName
    seenNames := target.recName :: seenNames
  let ctorInfos ←
    spec.ctors.mapM fun ctor => do
      let ctorType := constructorTypeExpr spec ctor
      let _ ←
        validateGeneratedType
          infoEnv
          s!"generated constructor {ctor.name} type"
          []
          ctorType
      pure (.ctor ctor.name [] ctorType spec.name)
  let ctorEnv := ctorInfos.reverse ++ infoEnv
  let recInfos ←
    (List.zip (List.range family.targets.length) family.targets).mapM fun pair => do
      let recType ← buildRecursorType family pair.1
      let _ ←
        validateGeneratedType
          ctorEnv
          s!"generated recursor {pair.2.recName} type"
          recursorLevelParams
          recType
      pure (.recursor pair.2.recName recursorLevelParams recType pair.1 family)
  pure (recInfos.reverse ++ ctorInfos.reverse ++ (.inductive spec.name [] info :: env))

end LeanLean
