import LeanLean.Syntax

namespace LeanLean

structure Binder where
  name : String
  type : Expr
  deriving DecidableEq, Repr, Inhabited

abbrev Telescope := List Binder
abbrev Context := List Binder
abbrev LevelContext := List Name
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
  let rec loop (cutoff : Nat) : Telescope → Telescope
    | [] => []
    | binder :: rest =>
        { binder with type := Expr.instantiateManyFrom cutoff values binder.type } ::
          loop (cutoff + 1) rest
  loop 0 tele

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
  target? : Option Expr := none
  deriving DecidableEq, Repr, Inhabited

structure InductiveSpec where
  name : Name
  levelParams : LevelContext := []
  params : Telescope
  indices : Telescope := []
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
  target : Expr
  fields : List FamilyField
  deriving DecidableEq, Repr, Inhabited

structure FamilyTarget where
  recName : Name
  schema : TargetSchema
  levels : List Level
  paramCount : Nat
  bindLocalsInMinors : Bool
  ctors : List FamilyCtor
  deriving DecidableEq, Repr, Inhabited

structure RecursorFamily where
  rootName : Name
  levelParams : LevelContext
  motiveLevelParam? : Option Name
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

def checkLevelsIn (info : ConstantInfo) (levelParams : LevelContext) (levels : List Level) : Result Unit := do
  let params := info.levelParams
  if levels.length != params.length then
    .error
      s!"constant {info.name} expects {params.length} universe arguments, \
         but got {levels.length}"
  else if !levels.all (Level.closedIn levelParams) then
    .error s!"constant {info.name} requires closed universe arguments"
  else
    pure ()

def checkLevels (info : ConstantInfo) (levels : List Level) : Result Unit :=
  info.checkLevelsIn [] levels

def instantiateExpr
    (constName : Name)
    (what : String)
    (params : List Name)
    (levelParams : LevelContext)
    (levels : List Level)
    (expr : Expr) : Result Expr :=
  if levels.length != params.length then
    .error
      s!"constant {constName} expects {params.length} universe arguments in its {what}, \
         but got {levels.length}"
  else if !levels.all (Level.closedIn levelParams) then
    .error s!"constant {constName} requires closed universe arguments in its {what}"
  else
    pure (Expr.instantiateLevels params levels expr)

def type (info : ConstantInfo) (levels : List Level) (levelParams : LevelContext := []) : Result Expr :=
  match info with
  | .axiom name params type =>
      instantiateExpr name "type" params levelParams levels type
  | .defn name params type _ =>
      instantiateExpr name "type" params levelParams levels type
  | .inductive name params indInfo =>
      instantiateExpr name "type" params levelParams levels indInfo.type
  | .ctor name params type _ =>
      instantiateExpr name "type" params levelParams levels type
  | .recursor name params type _ _ =>
      instantiateExpr name "type" params levelParams levels type

def value? (info : ConstantInfo) (levels : List Level) (levelParams : LevelContext := []) :
    Result (Option Expr) :=
  match info with
  | .defn name params _ value =>
      some <$> instantiateExpr name "value" params levelParams levels value
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

def freshNameAvoiding (used : List Name) (base : Name) : Name :=
  let rec loop : Nat → Name → Name
    | 0, candidate => candidate
    | fuel + 1, candidate =>
        if used.contains candidate then
          loop fuel (candidate ++ "'")
        else
          candidate
  loop (used.length + 1) base

def recursorMotiveLevelParam (spec : InductiveSpec) : Name :=
  freshNameAvoiding spec.levelParams recursorLevelParam

def recursorLevelParamsForFamily (family : RecursorFamily) : List Name :=
  match family.motiveLevelParam? with
  | some motiveLevelParam => family.levelParams ++ [motiveLevelParam]
  | none => family.levelParams

def inductiveIsProp (spec : InductiveSpec) : Bool :=
  Level.defEq spec.level .zero

def inductiveLevelArgs (spec : InductiveSpec) : List Level :=
  spec.levelParams.map Level.param

def levelsDefEq (left right : List Level) : Bool :=
  left.length = right.length &&
    (List.zip left right).all fun pair => Level.defEq pair.1 pair.2

def inductiveTarget (indName : Name) (params : List Expr) : Expr :=
  Expr.mkApps (.const indName []) params

def inductiveTargetWithLevels (indName : Name) (levels : List Level) (params : List Expr) :
    Expr :=
  Expr.mkApps (.const indName levels) params

def inductiveSelfTarget (spec : InductiveSpec) (params : List Expr) : Expr :=
  inductiveTargetWithLevels spec.name (inductiveLevelArgs spec) params

def inductiveTypeExpr (spec : InductiveSpec) : Expr :=
  Telescope.bindForall (spec.params ++ spec.indices) (.sort spec.level)

def constructorTargetExpr (spec : InductiveSpec) (ctor : ConstructorSpec) : Result Expr :=
  match ctor.target? with
  | some target => pure target
  | none =>
      if spec.indices.isEmpty then
        let paramArgs := Expr.bvarArgs spec.params.length ctor.fields.length
        pure (inductiveSelfTarget spec paramArgs)
      else
        .error s!"constructor {ctor.name} for indexed inductive {spec.name} must declare a target"

def checkConstructorTargetExpr
    (spec : InductiveSpec)
    (ctor : ConstructorSpec)
    (target : Expr) : Result Unit := do
  match target.getAppFn with
  | .const name levels =>
      if name != spec.name then
        .error s!"constructor {ctor.name} target must be headed by {spec.name}"
      else if !levelsDefEq levels (inductiveLevelArgs spec) then
        .error s!"constructor {ctor.name} target must use the inductive universe parameters"
      else
        let args := target.getAppArgs
        if args.length != spec.params.length + spec.indices.length then
          .error s!"constructor {ctor.name} target has the wrong arity for {spec.name}"
        else
          let paramArgs := args.take spec.params.length
          let expectedParams := Expr.bvarArgs spec.params.length ctor.fields.length
          if (List.zip paramArgs expectedParams).all fun pair => pair.1.alphaEq pair.2 then
            pure ()
          else
            .error s!"constructor {ctor.name} target must use the inductive parameters"
  | _ => .error s!"constructor {ctor.name} target must be an application of {spec.name}"

def constructorTypeExpr (spec : InductiveSpec) (ctor : ConstructorSpec) : Result Expr := do
  let target ← constructorTargetExpr spec ctor
  let _ ← checkConstructorTargetExpr spec ctor target
  let withFields := Telescope.bindForall ctor.fields target
  pure (Telescope.bindForall spec.params withFields)

def inferSortOfPi (domain codomain : Level) : Level :=
  Level.normalize (.imax domain codomain)

def recursiveTargetExpr (spec : InductiveSpec) : Expr :=
  let params := Expr.bvarArgs spec.params.length spec.indices.length
  let indices := Expr.bvarArgs spec.indices.length 0
  inductiveSelfTarget spec (params ++ indices)

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

def usedLocalPrefixLength (locals : Telescope) (expr : Expr) : Nat :=
  let localCount := locals.length
  let rec loop (sourceIndex : Nat) (used : Nat) : Nat :=
    if h : sourceIndex < localCount then
      let bvarIndex := localCount - 1 - sourceIndex
      let used :=
        if containsBVarAt bvarIndex 0 expr then
          sourceIndex + 1
        else
          used
      loop (sourceIndex + 1) used
    else
      used
  loop 0 0

def trimTargetSchema (schema : TargetSchema) : Result TargetSchema := do
  let keep := usedLocalPrefixLength schema.locals schema.target
  let drop := schema.locals.length - keep
  match Expr.lower drop schema.target with
  | some target =>
      pure { schema with locals := schema.locals.take keep, target }
  | none =>
      .error s!"internal error: target schema mentions a dropped local: {repr schema.target}"

def paramBaseIndex (paramCount paramIndex : Nat) : Nat :=
  paramCount - 1 - paramIndex

def decomposeInductiveApp (env : Env) (expr : Expr) :
    Option (Name × InductiveInfo × List Level × List Expr) :=
  let head := expr.getAppFn
  let args := expr.getAppArgs
  match head with
  | .const name levels =>
      match env.findInductive? name with
      | some info =>
          if levels.length = info.spec.levelParams.length &&
              args.length = info.spec.params.length + info.spec.indices.length then
            some (name, info, levels, args)
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
      if target.schema.locals.length > localVars.length then
        .error s!"internal error: nested target #{targetIndex} expects at least {target.schema.locals.length} locals, got {localVars.length}"
      else
        let some motive := listGet? motives targetIndex
          | .error s!"internal error: missing motive for nested target #{targetIndex}"
        pure (Expr.mkApps motive (localVars.take target.schema.locals.length ++ [fieldExpr]))
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
      if target.schema.locals.length > localVars.length then
        .error s!"internal error: nested target #{targetIndex} expects at least {target.schema.locals.length} locals, got {localVars.length}"
      else
        let schemaVars := localVars.take target.schema.locals.length
        pure (Expr.mkApps (.const target.recName levels) (prefixArgs ++ schemaVars ++ [fieldExpr]))
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

partial def familyCtorMinorBody
    (family : RecursorFamily)
    (motives : List Expr)
    (paramVars : List Expr)
    (schemaVars : List Expr)
    (targetIndex : Nat)
    (target : FamilyTarget)
    (ctor : FamilyCtor) : Result Expr := do
  let rec loop
      (ihIndex : Nat)
      (motives : List Expr)
      (paramVars : List Expr)
      (schemaVars : List Expr)
      (fieldVars : List Expr) :
      List FamilyField → Result Expr
    | [] => do
        let some motive := listGet? motives targetIndex
          | .error s!"internal error: missing motive for target #{targetIndex}"
        let ctorTarget := Expr.instantiateMany (paramVars ++ schemaVars ++ fieldVars) ctor.target
        let ctorParamArgs := ctorTarget.getAppArgs.take target.paramCount
        let ctorApp := Expr.mkApps (.const ctor.name target.levels) (ctorParamArgs ++ fieldVars)
        let motiveArgs :=
          if target.bindLocalsInMinors then
            schemaVars
          else
            ctorTarget.getAppArgs.drop target.paramCount
        pure (Expr.mkApps motive (motiveArgs ++ [ctorApp]))
    | field :: rest => do
        let fieldTy :=
          Expr.instantiateMany (paramVars ++ schemaVars ++ fieldVars) field.binder.type
        let motivesAfterField := motives.map (Expr.lift 1)
        let paramVarsAfterField := paramVars.map (Expr.lift 1)
        let schemaVarsAfterField := schemaVars.map (Expr.lift 1)
        let previousFieldVarsAfterField := fieldVars.map (Expr.lift 1)
        let fieldVarsAfterField := previousFieldVarsAfterField ++ [.bvar 0]
        let body ←
          if shapeHasIH field.shape then
            let ihTy ←
              ihTypeExpr
                family
                motivesAfterField
                paramVarsAfterField
                (schemaVarsAfterField ++ previousFieldVarsAfterField)
                field.shape
                (.bvar 0)
            let body ←
              loop
                (ihIndex + 1)
                (motivesAfterField.map (Expr.lift 1))
                (paramVarsAfterField.map (Expr.lift 1))
                (schemaVarsAfterField.map (Expr.lift 1))
                (fieldVarsAfterField.map (Expr.lift 1))
                rest
            pure (.forallE s!"ih{ihIndex}" ihTy body)
          else
            loop
              ihIndex
              motivesAfterField
              paramVarsAfterField
              schemaVarsAfterField
              fieldVarsAfterField
              rest
        pure (.forallE field.binder.name fieldTy body)
  loop 0 motives paramVars schemaVars [] ctor.fields

partial def familyCtorMinorType
    (family : RecursorFamily)
    (paramVars : List Expr)
    (motives : List Expr)
    (targetIndex : Nat)
    (target : FamilyTarget)
    (ctor : FamilyCtor) : Result Expr := do
  let minorLocals :=
    if target.bindLocalsInMinors then
      target.schema.locals
    else
      []
  Telescope.bindForallM paramVars minorLocals fun paramVars localVars => do
    familyCtorMinorBody
      family
      (motives.map (Expr.lift minorLocals.length))
      paramVars
      localVars
      targetIndex
      target
      ctor

def motiveBinderType
    (paramVars : List Expr)
    (motiveLevel : Level)
    (target : FamilyTarget) : Result Expr := do
  Telescope.bindForallM paramVars target.schema.locals fun paramVars localVars => do
    pure (.forallE "t" (instantiateTargetSchema paramVars localVars target.schema) (.sort motiveLevel))

partial def buildRecursorType
    (family : RecursorFamily)
    (targetIndex : Nat) : Result Expr := do
  let motiveLevel : Level :=
    match family.motiveLevelParam? with
    | some motiveLevelParam => .param motiveLevelParam
    | none => .zero
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

partial def inferSort
    (env : Env)
    (ctx : Context)
    (expr : Expr)
    (levelParams : LevelContext := []) : Result Level := do
  let inferred ← infer env ctx expr (levelParams := levelParams)
  let reduced ← whnf env inferred (levelParams := levelParams)
  match reduced with
  | .sort level => pure level
  | _ => .error s!"expected a type, got {repr reduced}"

partial def checkDefEqIn
    (env : Env)
    (ctx : Context)
    (left right : Expr)
    (levelParams : LevelContext := []) : Result Unit := do
  let leftNf ← normalize env left (levelParams := levelParams)
  let rightNf ← normalize env right (levelParams := levelParams)
  if leftNf.alphaEq rightNf then
    pure ()
  else
    let originalError := s!"definitional equality failed: {repr leftNf} vs {repr rightNf}"
    try
      let leftTy ← infer env ctx left (levelParams := levelParams)
      let rightTy ← infer env ctx right (levelParams := levelParams)
      let leftTyNf ← normalize env leftTy (levelParams := levelParams)
      let rightTyNf ← normalize env rightTy (levelParams := levelParams)
      if !leftTyNf.alphaEq rightTyNf then
        .error originalError
      else
        let typeLevel ← inferSort env ctx leftTy (levelParams := levelParams)
        if Level.defEq typeLevel .zero then
          pure ()
        else
          .error originalError
    catch _ =>
      .error originalError

partial def checkDefEq
    (env : Env)
    (left right : Expr)
    (levelParams : LevelContext := []) : Result Unit :=
  checkDefEqIn env [] left right (levelParams := levelParams)

partial def checkRecursorTargetArgs
    (env : Env)
    (recName : Name)
    (actual expected : List Expr)
    (levelParams : LevelContext := []) : Result Unit := do
  if actual.length != expected.length then
    .error s!"internal error: mismatched target argument arity for {recName}"
  else
    for pair in List.zip actual expected do
      try
        let _ ← checkDefEq env pair.1 pair.2 (levelParams := levelParams)
        pure ()
      catch _ =>
        .error s!"recursor target does not match its explicit schema arguments for {recName}"

partial def reduceRecursorApp
    (env : Env)
    (recName : Name)
    (levels : List Level)
    (args : List Expr)
    (levelParams : LevelContext := []) : Result (Option Expr) := do
  let some (targetIndex, family) := env.findRecursor? recName
    | .error s!"unknown recursor: {recName}"
  let some split := splitFamilyRecursorArgs family targetIndex args
    | pure none
  let some targetInfo := listGet? family.targets targetIndex
    | .error s!"internal error: invalid recursor index for {recName}"
  let targetWhnf ← whnf env split.target (levelParams := levelParams)
  let head := targetWhnf.getAppFn
  let ctorArgs := targetWhnf.getAppArgs
  let .const ctorName ctorLevels := head
    | pure none
  let some ctor := targetInfo.ctors.find? fun ctor => ctor.name = ctorName
    | pure none
  let expectedCtorLevels :=
    targetInfo.levels.map (Level.instantiate (recursorLevelParamsForFamily family) levels)
  if !levelsDefEq ctorLevels expectedCtorLevels then
    .error s!"recursor target constructor universe arguments do not match for {recName}"
  else
    let targetExpr := instantiateTargetSchema split.params split.locals targetInfo.schema
    if ctorArgs.length != targetInfo.paramCount + ctor.fields.length then
      pure none
    else
      let targetArgs := ctorArgs.take targetInfo.paramCount
      let fieldArgs := ctorArgs.drop targetInfo.paramCount
      let minorLocalArgs :=
        if targetInfo.bindLocalsInMinors then
          split.locals
        else
          []
      let ctorTarget :=
        Expr.instantiateMany (split.params ++ minorLocalArgs ++ fieldArgs) ctor.target
      let _ ←
        checkRecursorTargetArgs
          env
          recName
          targetArgs
          (targetExpr.getAppArgs.take targetInfo.paramCount)
          (levelParams := levelParams)
      let _ ←
        checkRecursorTargetArgs
          env
          recName
          ctorTarget.getAppArgs
          targetExpr.getAppArgs
          (levelParams := levelParams)
      let prefixArgs := split.params ++ split.motives ++ split.minors
      let mut previousFields : List Expr := []
      let mut minorArgs := minorLocalArgs
      for pair in List.zip ctor.fields fieldArgs do
        let field := pair.1
        let fieldArg := pair.2
        minorArgs := minorArgs ++ [fieldArg]
        if shapeHasIH field.shape then
          let ih ←
            ihTerm
              family
              levels
              prefixArgs
              split.params
              (minorLocalArgs ++ previousFields)
              field.shape
              fieldArg
          minorArgs := minorArgs ++ [ih]
        previousFields := previousFields ++ [fieldArg]
      let some minor := lookupMinorExpr? family split.minors targetIndex ctor.name
        | .error s!"internal error: missing minor premise for {ctor.name}"
      pure (some (Expr.mkApps minor minorArgs))

partial def whnf (env : Env) (expr : Expr) (levelParams : LevelContext := []) : Result Expr := do
  match expr with
  | .app _ _ =>
      let head := expr.getAppFn
      let args := expr.getAppArgs
      let headWhnf ← whnf env head (levelParams := levelParams)
      let rebuilt := Expr.mkApps headWhnf args
      match headWhnf with
      | .lam _ _ body =>
          match args with
          | [] => pure rebuilt
          | arg :: rest => whnf env (Expr.mkApps (Expr.instantiate1 arg body) rest)
      | .const name levels =>
          match env.find? name with
          | some info =>
              let _ ← info.checkLevelsIn levelParams levels
              match ← info.value? levels (levelParams := levelParams) with
              | some value => whnf env (Expr.mkApps value args) (levelParams := levelParams)
              | none =>
                  match info with
                  | .recursor _ _ _ _ _ =>
                      match ← reduceRecursorApp env name levels args (levelParams := levelParams) with
                      | some reduced => whnf env reduced (levelParams := levelParams)
                      | none => pure rebuilt
                  | _ => pure rebuilt
          | none => .error s!"unknown constant: {name}"
      | .letE _ _ value body =>
          whnf env (Expr.mkApps (Expr.instantiate1 value body) args) (levelParams := levelParams)
      | _ =>
          if rebuilt = expr then
            pure rebuilt
          else
            whnf env rebuilt (levelParams := levelParams)
  | .letE _ _ value body => whnf env (Expr.instantiate1 value body) (levelParams := levelParams)
  | .const name levels =>
      match env.find? name with
      | some info =>
          let _ ← info.checkLevelsIn levelParams levels
          match ← info.value? levels (levelParams := levelParams) with
          | some value => whnf env value (levelParams := levelParams)
          | none => pure expr
      | _ => .error s!"unknown constant: {name}"
  | _ => pure expr

partial def normalize (env : Env) (expr : Expr) (levelParams : LevelContext := []) : Result Expr := do
  let reduced ← whnf env expr (levelParams := levelParams)
  match reduced with
  | .bvar _ => pure reduced
  | .sort _ => pure reduced
  | .const _ _ => pure reduced
  | .lam name ty body => do
      let ty' ← normalize env ty (levelParams := levelParams)
      let body' ← normalize env body (levelParams := levelParams)
      pure (.lam name ty' body')
  | .forallE name ty body => do
      let ty' ← normalize env ty (levelParams := levelParams)
      let body' ← normalize env body (levelParams := levelParams)
      pure (.forallE name ty' body')
  | .letE name ty value body => do
      let ty' ← normalize env ty (levelParams := levelParams)
      let value' ← normalize env value (levelParams := levelParams)
      let body' ← normalize env body (levelParams := levelParams)
      let rebuilt := .letE name ty' value' body'
      let whnfRebuilt ← whnf env rebuilt (levelParams := levelParams)
      if whnfRebuilt = rebuilt then
        pure rebuilt
      else
        normalize env whnfRebuilt (levelParams := levelParams)
  | .app _ _ => do
      let head := reduced.getAppFn
      let args := reduced.getAppArgs
      let head' ← normalize env head (levelParams := levelParams)
      let args' ← args.mapM fun arg => normalize env arg (levelParams := levelParams)
      let rebuilt := Expr.mkApps head' args'
      let whnfRebuilt ← whnf env rebuilt (levelParams := levelParams)
      if whnfRebuilt = rebuilt then
        pure rebuilt
      else
        normalize env whnfRebuilt (levelParams := levelParams)

partial def inferSpine
    (env : Env)
    (ctx : Context)
    (headTy : Expr)
    (args : List Expr)
    (levelParams : LevelContext := []) : Result Expr := do
  let rec loop (type : Expr) (restArgs : List Expr) : Result Expr := do
    match restArgs with
    | [] => pure type
    | arg :: rest =>
        let reduced ← whnf env type (levelParams := levelParams)
        match reduced with
        | .forallE _ domain body =>
            let actual ← infer env ctx arg (levelParams := levelParams)
            let _ ← checkDefEqIn env ctx actual domain (levelParams := levelParams)
            loop (Expr.instantiate1 arg body) rest
        | _ => .error s!"application expects a function, got {repr reduced}"
  loop headTy args

partial def inferApp
    (env : Env)
    (ctx : Context)
    (expr : Expr)
    (levelParams : LevelContext := []) : Result Expr := do
  let head := expr.getAppFn
  let args := expr.getAppArgs
  let headTy ← infer env ctx head (levelParams := levelParams)
  inferSpine env ctx headTy args (levelParams := levelParams)

partial def infer
    (env : Env)
    (ctx : Context)
    (expr : Expr)
    (levelParams : LevelContext := []) : Result Expr := do
  match expr with
  | .bvar index =>
      match lookupCtx ctx index with
      | some binder => pure (Expr.lift (index + 1) binder.type)
      | none => .error s!"unbound variable #{index}"
  | .sort level =>
      if level.closedIn levelParams then
        pure (.sort (.succ level))
      else
        .error s!"sort level must be closed: {repr level}"
  | .const name levels =>
      match env.find? name with
      | some info =>
          let _ ← info.checkLevelsIn levelParams levels
          info.type levels (levelParams := levelParams)
      | none => .error s!"unknown constant: {name}"
  | .app _ _ => inferApp env ctx expr (levelParams := levelParams)
  | .lam name type body => do
      let _ ← inferSort env ctx type (levelParams := levelParams)
      let bodyTy ← infer env ({ name, type } :: ctx) body (levelParams := levelParams)
      pure (.forallE name type bodyTy)
  | .forallE name domain body => do
      let domainLevel ← inferSort env ctx domain (levelParams := levelParams)
      let bodyLevel ← inferSort env ({ name, type := domain } :: ctx) body (levelParams := levelParams)
      pure (.sort (inferSortOfPi domainLevel bodyLevel))
  | .letE name type value body => do
      let _ ← inferSort env ctx type (levelParams := levelParams)
      let valueTy ← infer env ctx value (levelParams := levelParams)
      let _ ← checkDefEqIn env ctx valueTy type (levelParams := levelParams)
      let bodyTy ← infer env ({ name, type } :: ctx) body (levelParams := levelParams)
      pure (Expr.instantiate1 value bodyTy)

end

def normalizeForInductiveAnalysis
    (env : Env)
    (expr : Expr)
    (levelParams : LevelContext := []) : Result Expr :=
  normalize env expr (levelParams := levelParams)

partial def positiveParamOccurrence
    (env : Env)
    (self : InductiveSpec)
    (selfPositive : List Bool)
    (targetIndex depth : Nat)
    (expr : Expr)
    (levelParams : LevelContext := []) : Result Bool := do
  let expr ← normalizeForInductiveAnalysis env expr (levelParams := levelParams)
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
          positiveParamOccurrence
            env
            self
            selfPositive
            targetIndex
            (depth + 1)
            body
            (levelParams := levelParams)
    | .app _ _ =>
        match decomposeInductiveApp env expr with
        | some (headName, info, _, args) =>
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
                  positiveParamOccurrence
                    env
                    self
                    selfPositive
                    targetIndex
                    depth
                    arg
                    (levelParams := levelParams)
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
              let mut fieldDepth := 0
              for field in ctor.fields do
                match
                  positiveParamOccurrence
                    env
                    spec
                    flags
                    (baseIndex + fieldDepth)
                    0
                    field.type
                    (levelParams := spec.levelParams) with
                | .ok _ => pure ()
                | .error _ => positive := false
                if !positive then
                  break
                fieldDepth := fieldDepth + 1
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
    (expr : Expr)
    (levelParams : LevelContext := []) : Result RawFieldShape := do
  let expr ← normalizeForInductiveAnalysis env expr (levelParams := levelParams)
  let analyzeInductiveApp
      (headName : Name)
      (info : InductiveInfo)
      (levels : List Level)
      (args : List Expr) :
      Result RawFieldShape := do
    if headName = root.spec.name then
      if !levelsDefEq levels (inductiveLevelArgs root.spec) then
        .error s!"recursive occurrence must use the universe parameters of {root.spec.name}"
      else
        let paramArgs := args.take root.spec.params.length
        let expectedParams := Expr.bvarArgs root.spec.params.length locals.length
        if !((List.zip paramArgs expectedParams).all fun pair => pair.1.alphaEq pair.2) then
          .error s!"recursive occurrence must use the inductive parameters of {root.spec.name}"
        else if (args.drop root.spec.params.length).any fun arg =>
            containsExprAt (recursiveTargetExpr root.spec) locals.length arg then
          .error s!"recursive occurrence appears inside an index of {root.spec.name}"
        else
          pure (.nested { locals, target := expr, headName })
    else
      let mut found := false
      for pair in List.zip args info.positiveParams do
        let arg := pair.1
        let isPositive := pair.2
        let occurs := containsExprAt (recursiveTargetExpr root.spec) locals.length arg
        if occurs then
          if !isPositive then
            .error s!"recursive occurrence appears in a non-positive argument of {headName}"
          let shape ← analyzeRecursiveShape env root locals arg (levelParams := levelParams)
          if rawShapeHasIH shape then
            found := true
      for arg in args.drop info.spec.params.length do
        if containsExprAt (recursiveTargetExpr root.spec) locals.length arg then
          .error s!"recursive occurrence appears in an index argument of {headName}"
      if found then
        pure (.nested { locals, target := expr, headName })
      else
        pure .none
  match expr with
  | .bvar _ => pure .none
  | .sort _ => pure .none
  | .const _ _ =>
      match decomposeInductiveApp env expr with
      | some (headName, info, levels, args) => analyzeInductiveApp headName info levels args
      | none => pure .none
  | .letE _ _ _ _ =>
      .error s!"unexpected let-expression in positivity check: {repr expr}"
  | .lam _ _ _ =>
      .error s!"unexpected lambda in positivity check: {repr expr}"
  | .forallE name dom body =>
      let dom ← normalizeForInductiveAnalysis env dom (levelParams := levelParams)
      if containsExprAt (recursiveTargetExpr root.spec) locals.length dom then
        .error s!"non-positive recursive occurrence in {repr expr}"
      else
        let binder : Binder := { name, type := dom }
        let bodyShape ←
          analyzeRecursiveShape env root (locals ++ [binder]) body (levelParams := levelParams)
        match bodyShape with
        | .none => pure .none
        | _ => pure (.pi binder bodyShape)
  | .app _ _ =>
      match decomposeInductiveApp env expr with
      | some (headName, info, levels, args) => analyzeInductiveApp headName info levels args
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
      let schema ← trimTargetSchema schema
      let (index, schemas) := internSchema schemas schema
      pure (.nested index, schemas)

partial def buildRecursorFamily
    (env : Env)
    (root : InductiveInfo) : Result RecursorFamily := do
  let rootLevelParams := root.spec.levelParams
  let rootTarget ←
    normalizeForInductiveAnalysis
      env
      (recursiveTargetExpr root.spec)
      (levelParams := rootLevelParams)
  let rootSchema : TargetSchema := { locals := root.spec.indices, target := rootTarget, headName := root.spec.name }
  let rec loop
      (schemas : List TargetSchema)
      (built : List FamilyTarget) : Result (List FamilyTarget) := do
    if built.length = schemas.length then
      pure built
    else
      let some schema := listGet? schemas built.length
        | .error s!"internal error: missing family target #{built.length}"
      let some (headName, info, levels, args) := decomposeInductiveApp env schema.target
        | .error s!"internal error: invalid family target {repr schema.target}"
      if headName != schema.headName then
        .error s!"internal error: family target head mismatch for {repr schema.target}"
      else
        let index := built.length
        let targetName := familyRecName root.spec.name index
        let targetParamCount := info.spec.params.length
        let bindLocalsInMinors := index != 0
        let targetParamArgs :=
          if bindLocalsInMinors then
            args.take targetParamCount
          else
            Expr.bvarArgs targetParamCount 0
        let rec buildFields
            (currentSchemas : List TargetSchema)
            (fieldLocals : Telescope)
            (remaining : Telescope) : Result (List FamilyField × List TargetSchema) := do
          match remaining with
          | [] => pure ([], currentSchemas)
          | field :: rest =>
              let rawShape ←
                analyzeRecursiveShape
                  env
                  root
                  fieldLocals
                  field.type
                  (levelParams := rootLevelParams)
              let (shape, currentSchemas) ← internFieldShape currentSchemas rawShape
              let (restFields, currentSchemas) ←
                buildFields currentSchemas (fieldLocals ++ [field]) rest
              pure ({ binder := field, shape } :: restFields, currentSchemas)
        let rec buildCtors
            (currentSchemas : List TargetSchema)
            (remaining : List ConstructorSpec) : Result (List FamilyCtor × List TargetSchema) := do
          match remaining with
          | [] => pure ([], currentSchemas)
          | ctor :: rest => do
              let ctorFields :=
                ctor.fields.map fun field =>
                  { field with type := Expr.instantiateLevels info.spec.levelParams levels field.type }
              let instantiated := Telescope.instantiateTypes targetParamArgs ctorFields
              let specialized ←
                instantiated.mapM fun field => do
                  let type ←
                    normalizeForInductiveAnalysis env field.type (levelParams := rootLevelParams)
                  pure { field with type }
              let ctorTarget ← constructorTargetExpr info.spec ctor
              let ctorTarget :=
                Expr.instantiateLevels info.spec.levelParams levels ctorTarget
              let target ←
                normalizeForInductiveAnalysis
                  env
                  (Expr.instantiateManyFrom ctorFields.length targetParamArgs ctorTarget)
                  (levelParams := rootLevelParams)
              let initialFieldLocals :=
                if bindLocalsInMinors then
                  schema.locals
                else
                  []
              let (fields, currentSchemas) ← buildFields currentSchemas initialFieldLocals specialized
              let (restCtors, currentSchemas) ← buildCtors currentSchemas rest
              pure ({ name := ctor.name, target, fields } :: restCtors, currentSchemas)
        let (ctors, currentSchemas) ← buildCtors schemas info.spec.ctors
        let target : FamilyTarget :=
          {
            recName := targetName
            schema
            levels
            paramCount := targetParamCount
            bindLocalsInMinors
            ctors
          }
        loop currentSchemas (built ++ [target])
  let targets ← loop [rootSchema] []
  pure
    {
      rootName := root.spec.name
      levelParams := root.spec.levelParams
      motiveLevelParam? :=
        if inductiveIsProp root.spec then
          none
        else
          some (recursorMotiveLevelParam root.spec)
      params := root.spec.params
      targets
    }

def checkClosed (what : String) (expr : Expr) : Result Unit :=
  if expr.closed then
    pure ()
  else
    .error s!"{what} must be closed"

def checkClosedIn (levelParams : LevelContext) (what : String) (expr : Expr) : Result Unit :=
  if expr.closedIn levelParams then
    pure ()
  else
    .error s!"{what} must be closed under its universe parameters"

def checkLevelParamsUnique : LevelContext → Result Unit
  | [] => pure ()
  | param :: rest =>
      if rest.contains param then
        .error s!"duplicate universe parameter: {param}"
      else
        checkLevelParamsUnique rest

def validateGeneratedType
    (env : Env)
    (what : String)
    (levelParams : List Name)
    (type : Expr) : Result Unit := do
  let _ ← checkLevelParamsUnique levelParams
  let _ ← checkClosedIn levelParams what type
  let _ ← inferSort env [] type (levelParams := levelParams)

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
    (type : Expr)
    (levelParams : LevelContext := []) : Result Level := do
  let reduced ← whnf env type (levelParams := levelParams)
  match reduced with
  | .sort level => pure level
  | _ => inferSort env ctx type (levelParams := levelParams)

def checkTelescopeFrom
    (env : Env)
    (ctx : Context)
    (tele : Telescope)
    (levelParams : LevelContext := []) : Result Context := do
  let rec loop (ctx : Context) (remaining : Telescope) : Result Context := do
    match remaining with
    | [] => pure ctx
    | binder :: rest =>
        let _ ← inferSort env ctx binder.type (levelParams := levelParams)
        loop (Telescope.withBinder ctx binder) rest
  loop ctx tele

def checkTelescope
    (env : Env)
    (tele : Telescope)
    (levelParams : LevelContext := []) : Result Unit := do
  let _ ← checkTelescopeFrom env [] tele (levelParams := levelParams)
  pure ()

def addAxiomWithLevels (env : Env) (name : Name) (levelParams : LevelContext) (type : Expr) :
    Result Env := do
  let _ ← checkLevelParamsUnique levelParams
  let _ ← checkFreshName env name
  let _ ← checkClosedIn levelParams s!"axiom {name}" type
  let _ ← inferSort env [] type (levelParams := levelParams)
  pure (.axiom name levelParams type :: env)

def addAxiom (env : Env) (name : Name) (type : Expr) : Result Env :=
  addAxiomWithLevels env name [] type

def addDefinitionWithLevels
    (env : Env)
    (name : Name)
    (levelParams : LevelContext)
    (type value : Expr) : Result Env := do
  let _ ← checkLevelParamsUnique levelParams
  let _ ← checkFreshName env name
  let _ ← checkClosedIn levelParams s!"definition {name} type" type
  let _ ← checkClosedIn levelParams s!"definition {name} value" value
  let _ ← inferSort env [] type (levelParams := levelParams)
  let valueTy ← infer env [] value (levelParams := levelParams)
  let _ ← checkDefEq env valueTy type (levelParams := levelParams)
  pure (.defn name levelParams type value :: env)

def addDefinition (env : Env) (name : Name) (type value : Expr) : Result Env :=
  addDefinitionWithLevels env name [] type value

def addInductive (env : Env) (spec : InductiveSpec) : Result Env := do
  let _ ← checkLevelParamsUnique spec.levelParams
  if !spec.level.closedIn spec.levelParams then
    .error s!"inductive result universe must be closed under its universe parameters: {repr spec.level}"
  if !inductiveIsProp spec && !spec.level.definitelyPositive then
    .error s!"inductive result universe is neither Prop nor a data universe: {repr spec.level}"
  let _ ← checkFreshName env spec.name
  let _ ← checkFreshName env (recursorName spec.name)
  let mut seenNames := [spec.name, recursorName spec.name]
  for ctor in spec.ctors do
    if seenNames.contains ctor.name then
      .error s!"duplicate name in inductive declaration: {ctor.name}"
    let _ ← checkFreshName env ctor.name
    seenNames := ctor.name :: seenNames
  let _ ← checkTelescope env spec.params (levelParams := spec.levelParams)
  let paramCtx := Telescope.toContext spec.params
  let _ ← checkTelescopeFrom env paramCtx spec.indices (levelParams := spec.levelParams)
  let indType := inductiveTypeExpr spec
  let provisionalInfo : InductiveInfo :=
    {
      type := indType
      spec
      positiveParams := List.replicate spec.params.length true
    }
  let tempEnv := .inductive spec.name spec.levelParams provisionalInfo :: env
  if !spec.ctors.isEmpty && !inductiveIsProp spec then
    let rec checkParamLevels (ctx : Context) : Telescope → Result Unit
      | [] => pure ()
      | binder :: rest => do
          let level ← inferBinderUniverse env ctx binder.type (levelParams := spec.levelParams)
          let _ ←
            checkLevelAtMost
              s!"parameter {binder.name}"
              level
              spec.level
          checkParamLevels (Telescope.withBinder ctx binder) rest
    let _ ← checkParamLevels [] spec.params
  for ctor in spec.ctors do
    let rec checkFieldLevels (ctx : Context) : Telescope → Result Unit
      | [] => pure ()
      | field :: rest => do
          let level ← inferSort tempEnv ctx field.type (levelParams := spec.levelParams)
          let _ ←
            checkLevelAtMost
              s!"field {ctor.name}.{field.name}"
              level
              spec.level
          checkFieldLevels (Telescope.withBinder ctx field) rest
    let _ ← checkFieldLevels paramCtx ctor.fields
  let positiveParams ← computePositiveParams tempEnv spec
  let info : InductiveInfo := { type := indType, spec, positiveParams }
  let infoEnv := .inductive spec.name spec.levelParams info :: env
  let family ← buildRecursorFamily infoEnv info
  for target in family.targets.drop 1 do
    if seenNames.contains target.recName then
      .error s!"duplicate name in inductive declaration: {target.recName}"
    let _ ← checkFreshName env target.recName
    seenNames := target.recName :: seenNames
  let ctorInfos ←
    spec.ctors.mapM fun ctor => do
      let ctorType ← constructorTypeExpr spec ctor
      let _ ←
        validateGeneratedType
          infoEnv
          s!"generated constructor {ctor.name} type"
          spec.levelParams
          ctorType
      pure (.ctor ctor.name spec.levelParams ctorType spec.name)
  let ctorEnv := ctorInfos.reverse ++ infoEnv
  let recInfos ←
    (List.zip (List.range family.targets.length) family.targets).mapM fun pair => do
      let recType ← buildRecursorType family pair.1
      let recLevelParams := recursorLevelParamsForFamily family
      let _ ←
        validateGeneratedType
          ctorEnv
          s!"generated recursor {pair.2.recName} type"
          recLevelParams
          recType
      pure (.recursor pair.2.recName recLevelParams recType pair.1 family)
  pure (recInfos.reverse ++ ctorInfos.reverse ++ (.inductive spec.name spec.levelParams info :: env))

end LeanLean
