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

def bindIndependentForallLiftingBody (tele : Telescope) (body : Expr) : Expr :=
  let rec loop (shift : Nat) (remaining : Telescope) : Expr :=
    match remaining with
    | [] => Expr.lift shift body
    | binder :: rest =>
        .forallE binder.name (Expr.lift shift binder.type) (loop (shift + 1) rest)
  loop 0 tele

def bindLambda (tele : Telescope) (body : Expr) : Expr :=
  let rec loop : Telescope → Expr
    | [] => body
    | binder :: rest =>
        .lam binder.name binder.type (loop rest)
  loop tele

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

structure InductiveBlockSpec where
  levelParams : LevelContext := []
  specs : List InductiveSpec
  deriving DecidableEq, Repr, Inhabited

structure TargetSchema where
  locals : Telescope
  target : Expr
  headName : Name
  deriving DecidableEq, Repr, Inhabited

inductive RawFieldShape where
  | none : RawFieldShape
  | direct : TargetSchema → RawFieldShape
  | pi : Binder → RawFieldShape → RawFieldShape
  | nested : TargetSchema → RawFieldShape
  deriving DecidableEq, Repr, Inhabited

inductive FieldShape where
  | none : FieldShape
  | direct : TargetSchema → FieldShape
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
  k : Bool := false
  params : Telescope
  targets : List FamilyTarget
  deriving DecidableEq, Repr, Inhabited

structure StructureFieldInfo where
  fieldName : Name
  projFn : Name
  subobject? : Option Name := none
  deriving DecidableEq, Repr, Inhabited

structure StructureParentInfo where
  structName : Name
  subobject : Bool
  projFn : Name
  deriving DecidableEq, Repr, Inhabited

structure StructureInfo where
  structName : Name
  fieldNames : List Name := []
  fieldInfo : List StructureFieldInfo := []
  parentInfo : List StructureParentInfo := []
  deriving DecidableEq, Repr, Inhabited

structure InductiveInfo where
  type : Expr
  spec : InductiveSpec
  positiveParams : List Bool
  allowsLargeElim : Bool := true
  projectionFields : List Nat := []
  indexFields : List (Nat × Nat) := []
  structureInfo? : Option StructureInfo := none
  deriving DecidableEq, Repr, Inhabited

structure ProjectionInfo where
  structName : Name
  ctorName : Name
  numParams : Nat
  index : Nat
  fieldIndex : Nat
  deriving DecidableEq, Repr, Inhabited

inductive PrimitiveInfo where
  | recursor : Nat → RecursorFamily → PrimitiveInfo
  | quotType : PrimitiveInfo
  | quotMk : PrimitiveInfo
  | quotLift : PrimitiveInfo
  | quotInd : PrimitiveInfo
  | quotSound : PrimitiveInfo
  deriving DecidableEq, Repr, Inhabited

inductive DefinitionTransparency where
  | transparent : DefinitionTransparency
  | opaque : DefinitionTransparency
  deriving DecidableEq, Repr, Inhabited

inductive ReducibilityHint where
  | regular : Nat → ReducibilityHint
  | abbrev : ReducibilityHint
  | opaque : ReducibilityHint
  deriving DecidableEq, Repr, Inhabited

inductive ConstantKind where
  | axiom : ConstantKind
  | defn : DefinitionTransparency → ReducibilityHint → ConstantKind
  | thm : ConstantKind
  | inductive : InductiveInfo → ConstantKind
  | ctor : Name → ConstantKind
  | projection : ProjectionInfo → ConstantKind
  | primitive : PrimitiveInfo → ConstantKind
  deriving DecidableEq, Repr, Inhabited

structure ConstantInfo where
  name : Name
  levelParams : List Name
  typeExpr : Expr
  valueExpr? : Option Expr := none
  kind : ConstantKind
  deriving DecidableEq, Repr, Inhabited

abbrev Env := List ConstantInfo

structure KernelConstructorDecl where
  name : Name
  type : Expr
  deriving DecidableEq, Repr, Inhabited

structure KernelInductiveTypeDecl where
  name : Name
  type : Expr
  ctors : List KernelConstructorDecl
  deriving DecidableEq, Repr, Inhabited

structure KernelInductiveDecl where
  levelParams : LevelContext := []
  numParams : Nat
  types : List KernelInductiveTypeDecl
  deriving DecidableEq, Repr, Inhabited

structure GeneratedRecursorRuleInfo where
  ctor : Name
  nfields : Nat
  rhs? : Option Expr := none
  deriving DecidableEq, Repr, Inhabited

structure GeneratedRecursorInfo where
  all : List Name
  numParams : Nat
  numIndices : Nat
  numMotives : Nat
  numMinors : Nat
  k : Bool := false
  rules : List GeneratedRecursorRuleInfo
  deriving DecidableEq, Repr, Inhabited

inductive Declaration where
  | axiom : Name → LevelContext → Expr → Declaration
  | definition : Name → LevelContext → Expr → Expr → Declaration
  | definitionWithHint : Name → LevelContext → ReducibilityHint → Expr → Expr → Declaration
  | opaqueDefinition : Name → LevelContext → Expr → Expr → Declaration
  | theorem : Name → LevelContext → Expr → Expr → Declaration
  | inductive : InductiveSpec → Declaration
  | inductiveBlock : InductiveBlockSpec → Declaration
  | kernelInductive : KernelInductiveDecl → Declaration
  | generatedConstructor : Name → LevelContext → Expr → Name → Declaration
  | generatedRecursor : Name → LevelContext → Expr → Declaration
  | generatedRecursorWithInfo : Name → LevelContext → Expr → GeneratedRecursorInfo → Declaration
  | structureInfo : StructureInfo → Declaration
  | projection : Name → Name → Nat → Declaration
  | quotientPrimitives : Declaration
  | primitiveCheck : Name → LevelContext → Expr → PrimitiveInfo → Declaration
  deriving DecidableEq, Repr, Inhabited

namespace ConstantInfo

def mkAxiom (name : Name) (levelParams : List Name) (type : Expr) : ConstantInfo :=
  { name, levelParams, typeExpr := type, kind := .axiom }

def mkDefnWithHint
    (name : Name)
    (levelParams : List Name)
    (type value : Expr)
    (hint : ReducibilityHint) : ConstantInfo :=
  { name, levelParams, typeExpr := type, valueExpr? := some value, kind := .defn .transparent hint }

def mkDefn (name : Name) (levelParams : List Name) (type value : Expr) : ConstantInfo :=
  mkDefnWithHint name levelParams type value (.regular 0)

def mkOpaqueDefn (name : Name) (levelParams : List Name) (type value : Expr) : ConstantInfo :=
  { name, levelParams, typeExpr := type, valueExpr? := some value, kind := .defn .opaque .opaque }

def mkTheorem (name : Name) (levelParams : List Name) (type value : Expr) : ConstantInfo :=
  { name, levelParams, typeExpr := type, valueExpr? := some value, kind := .thm }

def mkInductive (name : Name) (levelParams : List Name) (info : InductiveInfo) : ConstantInfo :=
  { name, levelParams, typeExpr := info.type, kind := .inductive info }

def mkCtor (name : Name) (levelParams : List Name) (type : Expr) (indName : Name) :
    ConstantInfo :=
  { name, levelParams, typeExpr := type, kind := .ctor indName }

def mkProjection
    (name : Name)
    (levelParams : List Name)
    (type value : Expr)
    (projection : ProjectionInfo) : ConstantInfo :=
  { name, levelParams, typeExpr := type, valueExpr? := some value, kind := .projection projection }

def mkRecursor
    (name : Name)
    (levelParams : List Name)
    (type : Expr)
    (index : Nat)
    (family : RecursorFamily) : ConstantInfo :=
  { name, levelParams, typeExpr := type, kind := .primitive (.recursor index family) }

def mkPrimitive
    (name : Name)
    (levelParams : List Name)
    (type : Expr)
    (primitive : PrimitiveInfo) : ConstantInfo :=
  { name, levelParams, typeExpr := type, kind := .primitive primitive }

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
  instantiateExpr info.name "type" info.levelParams levelParams levels info.typeExpr

def value? (info : ConstantInfo) (levels : List Level) (levelParams : LevelContext := []) :
    Result (Option Expr) :=
  match info.kind, info.valueExpr? with
  | .defn .transparent _, some value =>
      some <$> instantiateExpr info.name "value" info.levelParams levelParams levels value
  | .projection _, some value =>
      some <$> instantiateExpr info.name "value" info.levelParams levelParams levels value
  | _, _ => pure none

end ConstantInfo

namespace StructureInfo

def fieldInfoFor? (info : StructureInfo) (fieldName : Name) : Option StructureFieldInfo :=
  info.fieldInfo.find? fun field => field.fieldName = fieldName

end StructureInfo

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
  | some { kind := .inductive info, .. } => some info
  | _ => none

def findCtor? (env : Env) (target : Name) : Option Name :=
  match find? env target with
  | some { kind := .ctor indName, .. } => some indName
  | _ => none

def findRecursor? (env : Env) (target : Name) : Option (Nat × RecursorFamily) :=
  match find? env target with
  | some { kind := .primitive (.recursor index family), .. } => some (index, family)
  | _ => none

def findProjection? (env : Env) (target : Name) : Option ProjectionInfo :=
  match find? env target with
  | some { kind := .projection info, .. } => some info
  | _ => none

def findStructure? (env : Env) (target : Name) : Option StructureInfo :=
  match findInductive? env target with
  | some { structureInfo? := some info, .. } => some info
  | _ => none

def updateInductiveInfo (env : Env) (target : Name) (f : InductiveInfo → InductiveInfo) :
    Result Env :=
  match env with
  | [] => .error s!"unknown inductive: {target}"
  | info :: rest =>
      if ConstantInfo.name info = target then
        match info.kind with
        | .inductive indInfo =>
            pure ({ info with kind := .inductive (f indInfo) } :: rest)
        | _ => .error s!"constant is not an inductive: {target}"
      else
        (fun rest => info :: rest) <$> updateInductiveInfo rest target f

partial def structureFieldsFlattened
    (env : Env)
    (structName : Name)
    (includeSubobjectFields : Bool := true) : Result (List Name) := do
  let some info := env.findStructure? structName
    | .error s!"unknown structure: {structName}"
  let mut fields : List Name := []
  for fieldName in info.fieldNames do
    let some fieldInfo := info.fieldInfoFor? fieldName
      | .error s!"structure {structName} has no field info for {fieldName}"
    match fieldInfo.subobject? with
    | some parentName =>
        if includeSubobjectFields then
          fields := fields ++ [fieldName]
        let parentFields ← structureFieldsFlattened env parentName includeSubobjectFields
        fields := fields ++ parentFields
    | none =>
        fields := fields ++ [fieldName]
  pure fields

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
  | some motiveLevelParam => motiveLevelParam :: family.levelParams
  | none => family.levelParams

def inductiveIsProp (spec : InductiveSpec) : Bool :=
  Level.defEq spec.level .zero

def inductiveIsData (spec : InductiveSpec) : Bool :=
  spec.level.definitelyPositive

def inductiveSupportsK (spec : InductiveSpec) : Bool :=
  inductiveIsProp spec &&
    match spec.ctors with
    | [ctor] => ctor.fields.isEmpty
    | _ => false

def inductiveIsSortPolymorphicSubsingleton (spec : InductiveSpec) : Bool :=
  !inductiveIsProp spec &&
    !inductiveIsData spec &&
    match spec.ctors with
    | [] => true
    | [ctor] => ctor.fields.isEmpty
    | _ => false

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

def eqTypeExpr (level : Level) (elem lhs rhs : Expr) : Expr :=
  Expr.mkApps (.const "Eq" [level]) [elem, lhs, rhs]

def quotientTypeExpr (level : Level) (elem rel : Expr) : Expr :=
  Expr.mkApps (.const "Quot" [level]) [elem, rel]

def quotientMkExpr (level : Level) (elem rel value : Expr) : Expr :=
  Expr.mkApps (.const "Quot.mk" [level]) [elem, rel, value]

def appendNewNames (names extra : List Name) : List Name :=
  extra.foldl
    (fun names name =>
      if names.contains name then
        names
      else
        names ++ [name])
    names

partial def exprConstants (expr : Expr) : List Name :=
  match expr with
  | .bvar _ => []
  | .sort _ => []
  | .const name _ => [name]
  | .lit lit => [lit.typeName]
  | .app fn arg => appendNewNames (exprConstants fn) (exprConstants arg)
  | .lam _ type body => appendNewNames (exprConstants type) (exprConstants body)
  | .forallE _ type body => appendNewNames (exprConstants type) (exprConstants body)
  | .proj typeName _ struct => appendNewNames [typeName] (exprConstants struct)
  | .letE _ type value body =>
      appendNewNames
        (appendNewNames (exprConstants type) (exprConstants value))
        (exprConstants body)

def telescopeConstants (tele : Telescope) : List Name :=
  tele.foldl (fun names binder => appendNewNames names (exprConstants binder.type)) []

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
  | .direct _ => true
  | .pi _ body => rawShapeHasIH body
  | .nested _ => true

def shapeHasIH : FieldShape → Bool
  | .none => false
  | .direct _ => true
  | .pi _ body => shapeHasIH body
  | .nested _ => true

def rawShapeSchemas : RawFieldShape → List TargetSchema
  | .none => []
  | .direct _ => []
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
    | .lit _ => false
    | .app fn arg => containsExprAt target depth fn || containsExprAt target depth arg
    | .lam _ ty body =>
        containsExprAt target depth ty || containsExprAt target (depth + 1) body
    | .forallE _ ty body =>
        containsExprAt target depth ty || containsExprAt target (depth + 1) body
    | .proj _ _ struct => containsExprAt target depth struct
    | .letE _ ty val body =>
        containsExprAt target depth ty ||
        containsExprAt target depth val ||
        containsExprAt target (depth + 1) body
termination_by expr

def containsAnyExprAt (targets : List Expr) (depth : Nat) (expr : Expr) : Bool :=
  targets.any fun target => containsExprAt target depth expr

def containsBVarAt (targetIndex depth : Nat) (expr : Expr) : Bool :=
  match expr with
  | .bvar index => index = targetIndex + depth
  | .sort _ => false
  | .const _ _ => false
  | .lit _ => false
  | .app fn arg => containsBVarAt targetIndex depth fn || containsBVarAt targetIndex depth arg
  | .lam _ ty body =>
      containsBVarAt targetIndex depth ty || containsBVarAt targetIndex (depth + 1) body
  | .forallE _ ty body =>
      containsBVarAt targetIndex depth ty || containsBVarAt targetIndex (depth + 1) body
  | .proj _ _ struct => containsBVarAt targetIndex depth struct
  | .letE _ ty val body =>
      containsBVarAt targetIndex depth ty ||
      containsBVarAt targetIndex depth val ||
      containsBVarAt targetIndex (depth + 1) body
termination_by expr

def containsLocalBVarAt (localCount depth : Nat) (expr : Expr) : Bool :=
  match expr with
  | .bvar index => depth <= index && index < depth + localCount
  | .sort _ => false
  | .const _ _ => false
  | .lit _ => false
  | .app fn arg => containsLocalBVarAt localCount depth fn || containsLocalBVarAt localCount depth arg
  | .lam _ ty body =>
      containsLocalBVarAt localCount depth ty || containsLocalBVarAt localCount (depth + 1) body
  | .forallE _ ty body =>
      containsLocalBVarAt localCount depth ty || containsLocalBVarAt localCount (depth + 1) body
  | .proj _ _ struct => containsLocalBVarAt localCount depth struct
  | .letE _ ty val body =>
      containsLocalBVarAt localCount depth ty ||
        containsLocalBVarAt localCount depth val ||
        containsLocalBVarAt localCount (depth + 1) body
termination_by expr

def containsLocalBVar (localCount : Nat) (expr : Expr) : Bool :=
  containsLocalBVarAt localCount 0 expr

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

structure ProjectionTarget where
  ctor : ConstructorSpec
  fieldIndex : Nat
  field : Binder
  deriving DecidableEq, Repr, Inhabited

def projectionTarget (info : InductiveInfo) (index : Nat) : Result ProjectionTarget := do
  match info.spec.ctors with
  | [ctor] =>
      let some fieldIndex := listGet? info.projectionFields index
        | .error s!"projection index {index} is out of bounds for {info.spec.name}"
      match listGet? ctor.fields fieldIndex with
      | some field => pure { ctor, fieldIndex, field }
      | none => .error s!"projection field map for {info.spec.name} points outside the constructor"
  | _ => .error s!"projection target {info.spec.name} must have exactly one constructor"

def projectionIndexForField? (projectionFields : List Nat) (fieldIndex : Nat) : Option Nat :=
  let rec loop (projectionIndex : Nat) : List Nat → Option Nat
    | [] => none
    | field :: rest =>
        if field = fieldIndex then
          some projectionIndex
        else
          loop (projectionIndex + 1) rest
  loop 0 projectionFields

def indexPositionForField? (indexFields : List (Nat × Nat)) (fieldIndex : Nat) : Option Nat :=
  match indexFields.find? (fun pair => pair.1 = fieldIndex) with
  | some pair => some pair.2
  | none => none

def projectionInfo (info : InductiveInfo) (index : Nat) : Result ProjectionInfo := do
  let target ← projectionTarget info index
  pure
    {
      structName := info.spec.name
      ctorName := target.ctor.name
      numParams := info.spec.params.length
      index
      fieldIndex := target.fieldIndex
    }

def projectionFieldTypeExpr
    (spec : InductiveSpec)
    (ctor : ConstructorSpec)
    (projectionFields : List Nat)
    (indexFields : List (Nat × Nat))
    (fieldIndex : Nat)
    (levels : List Level)
    (params : List Expr)
    (indices : List Expr)
    (struct : Expr) : Result Expr := do
  let some field := listGet? ctor.fields fieldIndex
    | .error s!"projection field index {fieldIndex} is out of bounds for {spec.name}"
  let fieldType := Expr.instantiateLevels spec.levelParams levels field.type
  let mut previousFields : List Expr := []
  for previousFieldIndex in List.range fieldIndex do
    match projectionIndexForField? projectionFields previousFieldIndex with
    | some projectionIndex =>
        previousFields := previousFields ++ [.proj spec.name projectionIndex struct]
    | none =>
        match indexPositionForField? indexFields previousFieldIndex with
        | some indexPosition =>
            match listGet? indices indexPosition with
            | some indexValue => previousFields := previousFields ++ [indexValue]
            | none => .error s!"projection index-field map for {spec.name} points outside the indices"
        | none => .error s!"constructor field {previousFieldIndex} for {spec.name} is neither projected nor index-forced"
  pure (Expr.instantiateMany (params ++ previousFields) fieldType)

def projectionFunctionType (info : InductiveInfo) (index : Nat) : Result Expr := do
  let target ← projectionTarget info index
  let spec := info.spec
  let tele := spec.params ++ spec.indices
  let vars := Expr.bvarArgs tele.length 0
  let params := vars.take spec.params.length
  let indices := vars.drop spec.params.length
  let selfType := inductiveTargetWithLevels spec.name (inductiveLevelArgs spec) (params ++ indices)
  let resultType ←
    projectionFieldTypeExpr
      spec
      target.ctor
      info.projectionFields
      info.indexFields
      target.fieldIndex
      (inductiveLevelArgs spec)
      (params.map (Expr.lift 1))
      (indices.map (Expr.lift 1))
      (.bvar 0)
  pure (Telescope.bindForall tele (.forallE "self" selfType resultType))

def projectionFunctionValue (info : InductiveInfo) (index : Nat) : Result Expr := do
  let _ ← projectionTarget info index
  let spec := info.spec
  let tele := spec.params ++ spec.indices
  let vars := Expr.bvarArgs tele.length 0
  let selfType := inductiveTargetWithLevels spec.name (inductiveLevelArgs spec) vars
  pure (Telescope.bindLambda tele (.lam "self" selfType (.proj spec.name index (.bvar 0))))

def structureSupportsEta (info : InductiveInfo) : Bool :=
  !inductiveIsProp info.spec &&
    match info.spec.ctors with
    | [ctor] => !ctor.fields.any fun field => field.type.occursConst info.spec.name
    | _ => false

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

def familyTargetName
    (blockRootName : Name)
    (recursiveNames : List Name)
    (schemas : List TargetSchema)
    (index : Nat) : Name :=
  match listGet? schemas index with
  | none => recursorName blockRootName
  | some schema =>
      if recursiveNames.contains schema.headName then
        recursorName schema.headName
      else
        let helperIndex :=
          (schemas.take (index + 1)).foldl
            (fun count schema => if recursiveNames.contains schema.headName then count else count + 1)
            0
        helperRecursorName blockRootName helperIndex

def familyRootTargetIndex? (family : RecursorFamily) : Option Nat :=
  let rec loop : Nat → List FamilyTarget → Option Nat
    | _, [] => none
    | index, target :: rest =>
        if target.schema.headName = family.rootName then
          some index
        else
          loop (index + 1) rest
  loop 0 family.targets

def familyTargetIndexByHead? (family : RecursorFamily) (headName : Name) : Option Nat :=
  let rec loop : Nat → List FamilyTarget → Option Nat
    | _, [] => none
    | index, target :: rest =>
        if target.schema.headName = headName then
          some index
        else
          loop (index + 1) rest
  loop 0 family.targets

def instantiateTargetSchema
    (params : List Expr)
    (locals : List Expr)
    (schema : TargetSchema) : Expr :=
  Expr.instantiateMany (params ++ locals) schema.target

def directOccurrenceMotiveArgs
    (family : RecursorFamily)
    (paramVars : List Expr)
    (localVars : List Expr)
    (schema : TargetSchema) : Result (Nat × FamilyTarget × Expr × List Expr) := do
  if schema.locals.length > localVars.length then
    .error
      s!"internal error: direct recursive target {schema.headName} expects at \
         least {schema.locals.length} locals, got {localVars.length}"
  let some targetIndex := familyTargetIndexByHead? family schema.headName
    | .error s!"internal error: unknown recursive target {schema.headName}"
  let some target := listGet? family.targets targetIndex
    | .error s!"internal error: invalid recursive target index {targetIndex}"
  let targetExpr := instantiateTargetSchema paramVars (localVars.take schema.locals.length) schema
  let .const headName _ := targetExpr.getAppFn
    | .error s!"internal error: direct recursive target is not a constant application: {repr targetExpr}"
  if headName != schema.headName then
    .error s!"internal error: direct recursive target head mismatch for {repr targetExpr}"
  let targetArgs := targetExpr.getAppArgs
  if targetArgs.length < target.paramCount then
    .error s!"internal error: direct recursive target has too few arguments: {repr targetExpr}"
  pure (targetIndex, target, targetExpr, targetArgs.drop target.paramCount)

structure RecursorSplit where
  params : List Expr
  motives : List Expr
  minors : List Expr
  locals : List Expr
  target : Expr
  extraArgs : List Expr

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
  let redexArgCount := paramCount + motiveCount + minorCount + localCount + 1
  if args.length < redexArgCount then
    none
  else
    let redexArgs := args.take redexArgCount
    let extraArgs := args.drop redexArgCount
    let params := redexArgs.take paramCount
    let rest := redexArgs.drop paramCount
    let motives := rest.take motiveCount
    let rest := rest.drop motiveCount
    let minors := rest.take minorCount
    let rest := rest.drop minorCount
    let locals := rest.take localCount
    match rest.drop localCount with
    | [target] => some { params, motives, minors, locals, target, extraArgs }
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
  | .direct schema =>
      let (targetIndex, _, _, motiveArgs) ←
        directOccurrenceMotiveArgs family paramVars localVars schema
      let some motive := listGet? motives targetIndex
        | .error s!"internal error: missing motive #{targetIndex}"
      pure (Expr.mkApps motive (motiveArgs ++ [fieldExpr]))
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
  | .direct schema =>
      let (_, target, _, motiveArgs) ←
        directOccurrenceMotiveArgs family paramVars localVars schema
      pure (Expr.mkApps (.const target.recName levels) (prefixArgs ++ motiveArgs ++ [fieldExpr]))
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
  let rec ihBinders
      (motives : List Expr)
      (paramVars : List Expr)
      (schemaVars : List Expr)
      (ihIndex : Nat)
      (previousFields : List Expr) :
      List FamilyField → List Expr → Result Telescope
    | [], [] => pure []
    | field :: rest, fieldExpr :: restExprs => do
        let nextIndex := if shapeHasIH field.shape then ihIndex + 1 else ihIndex
        let restBinders ←
          ihBinders motives paramVars schemaVars nextIndex (previousFields ++ [fieldExpr]) rest restExprs
        if shapeHasIH field.shape then
          let ihTy ←
            ihTypeExpr
              family
              motives
              paramVars
              (schemaVars ++ previousFields)
              field.shape
              fieldExpr
          pure ({ name := s!"ih{ihIndex}", type := ihTy } :: restBinders)
        else
          pure restBinders
    | _, _ => .error "internal error: minor-premise field arity mismatch"
  let minorResult
      (motives : List Expr)
      (paramVars : List Expr)
      (schemaVars : List Expr)
      (fieldVars : List Expr) : Result Expr := do
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
  let rec bindFields
      (motives : List Expr)
      (paramVars : List Expr)
      (schemaVars : List Expr)
      (fieldVars : List Expr) :
      List FamilyField → Result Expr
    | [] => do
        let binders ← ihBinders motives paramVars schemaVars 0 [] ctor.fields fieldVars
        let body ← minorResult motives paramVars schemaVars fieldVars
        pure (Telescope.bindIndependentForallLiftingBody binders body)
    | field :: rest => do
        let fieldTy :=
          Expr.instantiateMany (paramVars ++ schemaVars ++ fieldVars) field.binder.type
        let body ←
          bindFields
            (motives.map (Expr.lift 1))
            (paramVars.map (Expr.lift 1))
            (schemaVars.map (Expr.lift 1))
            (fieldVars.map (Expr.lift 1) ++ [.bvar 0])
            rest
        pure (.forallE field.binder.name fieldTy body)
  bindFields motives paramVars schemaVars [] ctor.fields

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

partial def inferProjection
    (env : Env)
    (ctx : Context)
    (typeName : Name)
    (index : Nat)
    (struct : Expr)
    (levelParams : LevelContext := []) : Result Expr := do
  let structTy ← infer env ctx struct (levelParams := levelParams)
  let structTyWhnf ← whnf env structTy (levelParams := levelParams)
  let some (headName, info, levels, args) := decomposeInductiveApp env structTyWhnf
    | .error s!"projection target must have an inductive type, got {repr structTyWhnf}"
  if headName != typeName then
    .error s!"projection expected {typeName}, got {headName}"
  else
    let target ← projectionTarget info index
    let params := args.take info.spec.params.length
    let indices := args.drop info.spec.params.length
    let resultType ←
      projectionFieldTypeExpr
        info.spec
        target.ctor
        info.projectionFields
        info.indexFields
        target.fieldIndex
        levels
        params
        indices
        struct
    if inductiveIsProp info.spec then
      let resultLevel ← inferSort env ctx resultType (levelParams := levelParams)
      if Level.defEq resultLevel .zero then
        pure resultType
      else
        .error s!"projection cannot extract non-propositional field {index} from {typeName}"
    else
      pure resultType

partial def reduceProjection
    (env : Env)
    (typeName : Name)
    (index : Nat)
    (struct : Expr)
    (levelParams : LevelContext := []) : Result (Option Expr) := do
  let some info := env.findInductive? typeName
    | .error s!"unknown projection type: {typeName}"
  let target ← projectionTarget info index
  let structWhnf ← whnf env struct (levelParams := levelParams)
  let .const ctorName _ := structWhnf.getAppFn
    | pure none
  if ctorName != target.ctor.name then
    match env.findCtor? ctorName with
    | some _ => .error s!"projection target constructor does not match {typeName}"
    | none => pure none
  else
    let args := structWhnf.getAppArgs
    let expectedArity := info.spec.params.length + target.ctor.fields.length
    if args.length != expectedArity then
      .error s!"projection target constructor has wrong arity for {typeName}"
    else
      match listGet? (args.drop info.spec.params.length) target.fieldIndex with
      | some value => pure (some value)
      | none => .error s!"projection index {index} is out of bounds for {typeName}"

partial def isStructureEtaExpansion
    (env : Env)
    (ctx : Context)
    (expanded other : Expr)
    (levelParams : LevelContext := []) : Result Bool := do
  let head := expanded.getAppFn
  let .const ctorName ctorLevels := head
    | pure false
  let some indName := env.findCtor? ctorName
    | pure false
  let some info := env.findInductive? indName
    | pure false
  if !structureSupportsEta info then
    pure false
  else
    match info.spec.ctors with
    | [ctor] =>
      if ctor.name != ctorName then
        pure false
      else
      let args := expanded.getAppArgs
      let paramCount := info.spec.params.length
      let fieldCount := ctor.fields.length
      if args.length != paramCount + fieldCount then
        pure false
      else
        let otherTy ← infer env ctx other (levelParams := levelParams)
        let otherTyWhnf ← whnf env otherTy (levelParams := levelParams)
        match decomposeInductiveApp env otherTyWhnf with
        | some (otherIndName, _, otherLevels, otherArgs) =>
            if otherIndName != indName || !levelsDefEq ctorLevels otherLevels then
              pure false
            else
              let ctorParams := args.take paramCount
              let fields := args.drop paramCount
              let ctorTarget ← constructorTargetExpr info.spec ctor
              let ctorTarget := Expr.instantiateLevels info.spec.levelParams ctorLevels ctorTarget
              let instantiatedTarget := Expr.instantiateMany (ctorParams ++ fields) ctorTarget
              let targetArgs := instantiatedTarget.getAppArgs
              let otherIndices := otherArgs.drop paramCount
              let mut ok := true
              if targetArgs.length != otherArgs.length then
                ok := false
              for pair in List.zip targetArgs otherArgs do
                try
                  let _ ← checkDefEqIn env ctx pair.1 pair.2 (levelParams := levelParams)
                  pure ()
                catch _ =>
                  ok := false
              for pair in List.zip (List.range fieldCount) fields do
                match projectionIndexForField? info.projectionFields pair.1 with
                | some projectionIndex =>
                    try
                      let _ ←
                        checkDefEqIn
                          env
                          ctx
                          pair.2
                          (.proj indName projectionIndex other)
                          (levelParams := levelParams)
                      pure ()
                    catch _ =>
                      ok := false
                    | none =>
                        match indexPositionForField? info.indexFields pair.1 with
                        | some indexPosition =>
                            match listGet? otherIndices indexPosition with
                            | some indexValue =>
                                try
                                  let _ ← checkDefEqIn env ctx pair.2 indexValue (levelParams := levelParams)
                                  pure ()
                                catch _ =>
                                  ok := false
                            | none => ok := false
                        | none => ok := false
              pure ok
        | none => pure false
    | _ => pure false

partial def proofIrrelevantAlphaEqIn
    (env : Env)
    (ctx : Context)
    (left right : Expr)
    (levelParams : LevelContext := []) : Result Unit := do
  if left.alphaEq right then
    pure ()
  else
    match left, right with
    | .sort leftLevel, .sort rightLevel =>
        if Level.defEq leftLevel rightLevel then pure () else .error "sort levels differ"
    | .const leftName leftLevels, .const rightName rightLevels =>
        if leftName = rightName &&
            leftLevels.length = rightLevels.length &&
            (List.zip leftLevels rightLevels).all fun pair => Level.defEq pair.1 pair.2 then
          pure ()
        else
          checkProofIrrelevantExprEq env ctx left right (levelParams := levelParams)
    | .lit leftLit, .lit rightLit =>
        if leftLit = rightLit then pure () else .error "literals differ"
    | .app leftFn leftArg, .app rightFn rightArg =>
        let _ ← proofIrrelevantAlphaEqIn env ctx leftFn rightFn (levelParams := levelParams)
        proofIrrelevantAlphaEqIn env ctx leftArg rightArg (levelParams := levelParams)
    | .lam name leftTy leftBody, .lam _ rightTy rightBody =>
        let _ ← proofIrrelevantAlphaEqIn env ctx leftTy rightTy (levelParams := levelParams)
        proofIrrelevantAlphaEqIn
          env
          ({ name, type := leftTy } :: ctx)
          leftBody
          rightBody
          (levelParams := levelParams)
    | .forallE name leftTy leftBody, .forallE _ rightTy rightBody =>
        let _ ← proofIrrelevantAlphaEqIn env ctx leftTy rightTy (levelParams := levelParams)
        proofIrrelevantAlphaEqIn
          env
          ({ name, type := leftTy } :: ctx)
          leftBody
          rightBody
          (levelParams := levelParams)
    | .proj leftName leftIndex leftStruct, .proj rightName rightIndex rightStruct =>
        if leftName = rightName && leftIndex = rightIndex then
          proofIrrelevantAlphaEqIn env ctx leftStruct rightStruct (levelParams := levelParams)
        else
          checkProofIrrelevantExprEq env ctx left right (levelParams := levelParams)
    | .letE name leftTy leftVal leftBody, .letE _ rightTy rightVal rightBody =>
        let _ ← proofIrrelevantAlphaEqIn env ctx leftTy rightTy (levelParams := levelParams)
        let _ ← proofIrrelevantAlphaEqIn env ctx leftVal rightVal (levelParams := levelParams)
        proofIrrelevantAlphaEqIn
          env
          ({ name, type := leftTy } :: ctx)
          leftBody
          rightBody
          (levelParams := levelParams)
    | .bvar leftIndex, .bvar rightIndex =>
        if leftIndex = rightIndex then
          pure ()
        else
          checkProofIrrelevantExprEq env ctx left right (levelParams := levelParams)
    | _, _ =>
        checkProofIrrelevantExprEq env ctx left right (levelParams := levelParams)

partial def checkProofIrrelevantExprEq
    (env : Env)
    (ctx : Context)
    (left right : Expr)
    (levelParams : LevelContext := []) : Result Unit := do
  let leftTy ← infer env ctx left (levelParams := levelParams)
  let rightTy ← infer env ctx right (levelParams := levelParams)
  let leftLevel ← inferSort env ctx leftTy (levelParams := levelParams)
  let rightLevel ← inferSort env ctx rightTy (levelParams := levelParams)
  if Level.defEq leftLevel .zero && Level.defEq rightLevel .zero then
    let _ ← checkDefEqIn env ctx leftTy rightTy (levelParams := levelParams)
    pure ()
  else
    .error "not proof irrelevant"

partial def checkFunctionEtaExpansion
    (env : Env)
    (ctx : Context)
    (expanded other : Expr)
    (levelParams : LevelContext := []) : Result Unit := do
  match expanded with
  | .lam name domain body =>
      let otherTy ← infer env ctx other (levelParams := levelParams)
      match ← whnf env otherTy (levelParams := levelParams) with
      | .forallE _ expectedDomain _ =>
          let _ ← checkDefEqIn env ctx domain expectedDomain (levelParams := levelParams)
          let etaBody := .app (Expr.lift 1 other) (.bvar 0)
          checkDefEqIn
            env
            ({ name, type := domain } :: ctx)
            body
            etaBody
            (levelParams := levelParams)
      | _ => .error "eta target is not a function"
  | _ => .error "eta expansion is not a lambda"

partial def natValue?
    (env : Env)
    (expr : Expr)
    (levelParams : LevelContext := []) : Result (Option Nat) := do
  match ← whnf env expr (levelParams := levelParams) with
  | .lit (.natVal value) => pure (some value)
  | .const "Nat.zero" [] => pure (some 0)
  | .app (.const "Nat.succ" []) pred => do
      match ← natValue? env pred (levelParams := levelParams) with
      | some value => pure (some (value + 1))
      | none => pure none
  | _ => pure none

partial def checkStructuralDefEqIn
    (env : Env)
    (ctx : Context)
    (left right : Expr)
    (levelParams : LevelContext := []) : Result Unit := do
  match ← natValue? env left (levelParams := levelParams), ← natValue? env right (levelParams := levelParams) with
  | some leftValue, some rightValue =>
      if leftValue = rightValue then pure () else .error "natural literal values differ"
  | _, _ =>
      match left, right with
      | .bvar leftIndex, .bvar rightIndex =>
          if leftIndex = rightIndex then pure () else .error "bound variables differ"
      | .sort leftLevel, .sort rightLevel =>
          if Level.defEq leftLevel rightLevel then pure () else .error "sort levels differ"
      | .const leftName leftLevels, .const rightName rightLevels =>
          if leftName = rightName &&
              leftLevels.length = rightLevels.length &&
              (List.zip leftLevels rightLevels).all fun pair => Level.defEq pair.1 pair.2 then
            pure ()
          else
            .error "constants differ"
      | .lit leftLit, .lit rightLit =>
          if leftLit = rightLit then pure () else .error "literals differ"
      | .app leftFn leftArg, .app rightFn rightArg =>
          let _ ← checkDefEqIn env ctx leftFn rightFn (levelParams := levelParams)
          checkDefEqIn env ctx leftArg rightArg (levelParams := levelParams)
      | .lam name leftTy leftBody, .lam _ rightTy rightBody =>
          let _ ← checkDefEqIn env ctx leftTy rightTy (levelParams := levelParams)
          checkDefEqIn
            env
            ({ name, type := leftTy } :: ctx)
            leftBody
            rightBody
            (levelParams := levelParams)
      | .forallE name leftTy leftBody, .forallE _ rightTy rightBody =>
          let _ ← checkDefEqIn env ctx leftTy rightTy (levelParams := levelParams)
          checkDefEqIn
            env
            ({ name, type := leftTy } :: ctx)
            leftBody
            rightBody
            (levelParams := levelParams)
      | .proj leftName leftIndex leftStruct, .proj rightName rightIndex rightStruct =>
          if leftName = rightName && leftIndex = rightIndex then
            checkDefEqIn env ctx leftStruct rightStruct (levelParams := levelParams)
          else
            .error "projections differ"
      | .letE name leftTy leftVal leftBody, .letE _ rightTy rightVal rightBody =>
          let _ ← checkDefEqIn env ctx leftTy rightTy (levelParams := levelParams)
          let _ ← checkDefEqIn env ctx leftVal rightVal (levelParams := levelParams)
          checkDefEqIn
            env
            ({ name, type := leftTy } :: ctx)
            leftBody
            rightBody
            (levelParams := levelParams)
      | _, _ => .error "different expression forms"

partial def checkDefEqIn
    (env : Env)
    (ctx : Context)
    (left right : Expr)
    (levelParams : LevelContext := []) : Result Unit := do
  if left.alphaEq right then
    pure ()
  else
    let leftWhnf ← whnf env left (levelParams := levelParams)
    let rightWhnf ← whnf env right (levelParams := levelParams)
    if leftWhnf.alphaEq rightWhnf then
      pure ()
    else
      let originalError := s!"definitional equality failed: {repr leftWhnf} vs {repr rightWhnf}"
      let congruent := checkStructuralDefEqIn env ctx leftWhnf rightWhnf (levelParams := levelParams)
      if congruent.isOk then
        pure ()
      else
        let leftEta ← isStructureEtaExpansion env ctx leftWhnf rightWhnf (levelParams := levelParams)
        if leftEta then
          pure ()
        else
          let rightEta ← isStructureEtaExpansion env ctx rightWhnf leftWhnf (levelParams := levelParams)
          if rightEta then
            pure ()
          else
            match checkFunctionEtaExpansion env ctx leftWhnf rightWhnf (levelParams := levelParams) with
            | .ok _ => pure ()
            | .error _ =>
                match checkFunctionEtaExpansion env ctx rightWhnf leftWhnf (levelParams := levelParams) with
                | .ok _ => pure ()
                | .error _ =>
                    match checkProofIrrelevantExprEq env ctx left right (levelParams := levelParams) with
                    | .ok _ => pure ()
                    | .error _ => .error originalError

partial def checkDefEq
    (env : Env)
    (left right : Expr)
    (levelParams : LevelContext := []) : Result Unit :=
  checkDefEqIn env [] left right (levelParams := levelParams)

partial def checkHasTypeIn
    (env : Env)
    (ctx : Context)
    (expr expected : Expr)
    (levelParams : LevelContext := []) : Result Unit := do
  let expectedWhnf ← whnf env expected (levelParams := levelParams)
  match expr, expectedWhnf with
  | .lam name domain body, .forallE _ expectedDomain expectedBody =>
      let _ ← inferSort env ctx domain (levelParams := levelParams)
      let _ ← checkDefEqIn env ctx domain expectedDomain (levelParams := levelParams)
      checkHasTypeIn
        env
        ({ name, type := domain } :: ctx)
        body
        expectedBody
        (levelParams := levelParams)
  | _, _ => do
      let actual ← infer env ctx expr (levelParams := levelParams)
      checkDefEqIn env ctx actual expected (levelParams := levelParams)

partial def checkHasType
    (env : Env)
    (expr expected : Expr)
    (levelParams : LevelContext := []) : Result Unit :=
  checkHasTypeIn env [] expr expected (levelParams := levelParams)

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
  let reduceKLike : Result (Option Expr) := do
    if !family.k then
      pure none
    else
      match targetInfo.ctors with
      | [ctor] =>
          if !ctor.fields.isEmpty then
            pure none
          else
            let targetExpr := instantiateTargetSchema split.params split.locals targetInfo.schema
            let minorLocalArgs :=
              if targetInfo.bindLocalsInMinors then
                split.locals
              else
                []
            let ctorTarget := Expr.instantiateMany (split.params ++ minorLocalArgs) ctor.target
            if !ctorTarget.getAppFn.alphaEq targetExpr.getAppFn then
              pure none
            else
              match
                  checkRecursorTargetArgs
                    env
                    recName
                    ctorTarget.getAppArgs
                    targetExpr.getAppArgs
                    (levelParams := levelParams) with
              | .error _ => pure none
              | .ok _ =>
                  let some minor := lookupMinorExpr? family split.minors targetIndex ctor.name
                    | .error s!"internal error: missing minor premise for {ctor.name}"
                  pure (some (Expr.mkApps (Expr.mkApps minor minorLocalArgs) split.extraArgs))
      | _ => pure none
  let targetWhnf ← whnf env split.target (levelParams := levelParams)
  let reduceCtorTarget
      (ctor : FamilyCtor)
      (ctorLevels : List Level)
      (ctorArgs : List Expr) : Result (Option Expr) := do
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
        let mut ihArgs : List Expr := []
        for pair in List.zip ctor.fields fieldArgs do
          let field := pair.1
          let fieldArg := pair.2
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
            ihArgs := ihArgs ++ [ih]
          previousFields := previousFields ++ [fieldArg]
        let some minor := lookupMinorExpr? family split.minors targetIndex ctor.name
          | .error s!"internal error: missing minor premise for {ctor.name}"
        let minorArgs := minorLocalArgs ++ fieldArgs ++ ihArgs
        pure (some (Expr.mkApps (Expr.mkApps minor minorArgs) split.extraArgs))
  let reduceNatLiteralTarget (value : Nat) : Result (Option Expr) := do
    if targetInfo.schema.headName != "Nat" then
      pure none
    else
      match value with
      | 0 =>
          let some ctor := targetInfo.ctors.find? fun ctor => ctor.name = "Nat.zero"
            | .error s!"internal error: missing Nat.zero minor premise for {recName}"
          reduceCtorTarget ctor [] []
      | pred + 1 =>
          let some ctor := targetInfo.ctors.find? fun ctor => ctor.name = "Nat.succ"
            | .error s!"internal error: missing Nat.succ minor premise for {recName}"
          reduceCtorTarget ctor [] [.lit (.natVal pred)]
  match targetWhnf with
  | .lit (.natVal value) =>
      match ← reduceNatLiteralTarget value with
      | some reduced => pure (some reduced)
      | none => reduceKLike
  | _ =>
    let head := targetWhnf.getAppFn
    let ctorArgs := targetWhnf.getAppArgs
    let .const ctorName ctorLevels := head
      | reduceKLike
    let some ctor := targetInfo.ctors.find? fun ctor => ctor.name = ctorName
      | reduceKLike
    reduceCtorTarget ctor ctorLevels ctorArgs

partial def reduceQuotLiftApp
    (env : Env)
    (levels : List Level)
    (args : List Expr)
    (levelParams : LevelContext := []) : Result (Option Expr) := do
  if levels.length != 2 || args.length != 6 then
    pure none
  else
    let elem := args[0]!
    let rel := args[1]!
    let fn := args[3]!
    let quot := args[5]!
    let quotWhnf ← whnf env quot (levelParams := levelParams)
    let .const ctorName ctorLevels := quotWhnf.getAppFn
      | pure none
    if ctorName != "Quot.mk" then
      pure none
    else if !levelsDefEq ctorLevels [levels[0]!] then
      .error "Quot.lift target constructor universe does not match"
    else
      match quotWhnf.getAppArgs with
      | [ctorElem, ctorRel, value] =>
          let _ ← checkDefEqIn env [] elem ctorElem (levelParams := levelParams)
          let _ ← checkDefEqIn env [] rel ctorRel (levelParams := levelParams)
          pure (some (.app fn value))
      | _ => pure none

partial def natAddPrimitiveType : Expr :=
  .forallE "a" (.const "Nat" []) (.forallE "b" (.const "Nat" []) (.const "Nat" []))

partial def natBinaryNatPrimitiveType : Expr :=
  .forallE "a" (.const "Nat" []) (.forallE "b" (.const "Nat" []) (.const "Nat" []))

partial def natBinaryBoolPrimitiveType : Expr :=
  .forallE "a" (.const "Nat" []) (.forallE "b" (.const "Nat" []) (.const "Bool" []))

partial def checkNatAddPrimitiveDeclaration (info : ConstantInfo) : Result Unit := do
  if !info.levelParams.isEmpty then
    .error "Nat.add primitive reduction requires no universe parameters"
  else if !info.typeExpr.alphaEq natAddPrimitiveType then
    .error "Nat.add primitive reduction requires the specified Nat → Nat → Nat type"
  else
    match info.kind, info.valueExpr? with
    | .defn .transparent _, some _ => pure ()
    | _, _ => .error "Nat.add primitive reduction requires a transparent definition"

partial def checkNatBinaryNatPrimitiveDeclaration (name : Name) (info : ConstantInfo) : Result Unit := do
  if !info.levelParams.isEmpty then
    .error s!"{name} primitive reduction requires no universe parameters"
  else if !info.typeExpr.alphaEq natBinaryNatPrimitiveType then
    .error s!"{name} primitive reduction requires the specified Nat → Nat → Nat type"
  else
    match info.kind, info.valueExpr? with
    | .defn .transparent _, some _ => pure ()
    | _, _ => .error s!"{name} primitive reduction requires a transparent definition"

partial def checkNatBinaryBoolPrimitiveDeclaration (name : Name) (info : ConstantInfo) : Result Unit := do
  if !info.levelParams.isEmpty then
    .error s!"{name} primitive reduction requires no universe parameters"
  else if !info.typeExpr.alphaEq natBinaryBoolPrimitiveType then
    .error s!"{name} primitive reduction requires the specified Nat → Nat → Bool type"
  else
    match info.kind, info.valueExpr? with
    | .defn .transparent _, some _ => pure ()
    | _, _ => .error s!"{name} primitive reduction requires a transparent definition"

partial def requireConstant (env : Env) (name : Name) : Result Unit :=
  if env.contains name then
    pure ()
  else
    .error s!"unknown constant required by primitive literal: {name}"

partial def boolCtorExpr (env : Env) (value : Bool) : Result Expr := do
  let name := if value then "Bool.true" else "Bool.false"
  match env.findCtor? name with
  | some "Bool" =>
      let expr := .const name []
      let ty ← infer env [] expr
      let _ ← checkDefEq env ty (.const "Bool" [])
      pure expr
  | some indName =>
      .error s!"{name} primitive reduction requires a Bool constructor, got {indName}"
  | none =>
      .error s!"{name} primitive reduction requires a Bool constructor"

partial def reduceNatAddApp
    (env : Env)
    (info : ConstantInfo)
    (levels : List Level)
    (args : List Expr)
    (levelParams : LevelContext := []) : Result (Option Expr) := do
  if !levels.isEmpty || args.length != 2 then
    pure none
  else
    let _ ← checkNatAddPrimitiveDeclaration info
    let left := args[0]!
    let right ← whnf env args[1]! (levelParams := levelParams)
    match right with
    | .lit (.natVal 0) => pure (some left)
    | .lit (.natVal (pred + 1)) =>
        pure (some (Expr.app (.const "Nat.succ" []) (Expr.mkApps (.const "Nat.add" []) [left, .lit (.natVal pred)])))
    | _ =>
        match right.getAppFn, right.getAppArgs with
        | .const "Nat.zero" [], [] => pure (some left)
        | .const "Nat.succ" [], [pred] =>
            pure (some (Expr.app (.const "Nat.succ" []) (Expr.mkApps (.const "Nat.add" []) [left, pred])))
        | _, _ => pure none

partial def reduceNatBinaryNatApp
    (env : Env)
    (info : ConstantInfo)
    (name : Name)
    (args : List Expr)
    (op : Nat → Nat → Nat)
    (levelParams : LevelContext := []) : Result (Option Expr) := do
  if args.length != 2 then
    pure none
  else
    let _ ← checkNatBinaryNatPrimitiveDeclaration name info
    match
        ← natValue? env args[0]! (levelParams := levelParams),
        ← natValue? env args[1]! (levelParams := levelParams) with
    | some left, some right => pure (some (.lit (.natVal (op left right))))
    | _, _ => pure none

partial def reduceNatBinaryBoolApp
    (env : Env)
    (info : ConstantInfo)
    (name : Name)
    (args : List Expr)
    (op : Nat → Nat → Bool)
    (levelParams : LevelContext := []) : Result (Option Expr) := do
  if args.length != 2 then
    pure none
  else
    let _ ← checkNatBinaryBoolPrimitiveDeclaration name info
    match
        ← natValue? env args[0]! (levelParams := levelParams),
        ← natValue? env args[1]! (levelParams := levelParams) with
    | some left, some right => pure (some (← boolCtorExpr env (op left right)))
    | _, _ => pure none

partial def reduceKernelOverrideApp
    (env : Env)
    (info : ConstantInfo)
    (name : Name)
    (levels : List Level)
    (args : List Expr)
    (levelParams : LevelContext := []) : Result (Option Expr) := do
  match name with
  | "Nat.add" => reduceNatAddApp env info levels args (levelParams := levelParams)
  | "Nat.beq" =>
      if !levels.isEmpty then
        pure none
      else
        reduceNatBinaryBoolApp env info name args (fun left right => left = right) (levelParams := levelParams)
  | "Nat.ble" =>
      if !levels.isEmpty then
        pure none
      else
        reduceNatBinaryBoolApp env info name args (fun left right => left <= right) (levelParams := levelParams)
  | "Nat.mul" =>
      if !levels.isEmpty then
        pure none
      else
        reduceNatBinaryNatApp env info name args (fun left right => left * right) (levelParams := levelParams)
  | "Nat.pow" =>
      if !levels.isEmpty then
        pure none
      else
        reduceNatBinaryNatApp env info name args (fun left right => Nat.pow left right) (levelParams := levelParams)
  | _ => pure none

partial def reducePrimitiveApp
    (env : Env)
    (name : Name)
    (primitive : PrimitiveInfo)
    (levels : List Level)
    (args : List Expr)
    (levelParams : LevelContext := []) : Result (Option Expr) := do
  match primitive with
  | .recursor _ _ => reduceRecursorApp env name levels args (levelParams := levelParams)
  | .quotLift => reduceQuotLiftApp env levels args (levelParams := levelParams)
  | .quotType | .quotMk | .quotInd | .quotSound => pure none

partial def requireNatLiteralConstructors (env : Env) : Nat → Result Unit
  | 0 => requireConstant env "Nat.zero"
  | _ + 1 => do
      let _ ← requireConstant env "Nat.zero"
      requireConstant env "Nat.succ"

partial def natLiteralConstructorExpr (env : Env) : Nat → Result Expr
  | 0 => do
      let _ ← requireNatLiteralConstructors env 0
      pure (.const "Nat.zero" [])
  | n + 1 => do
      let _ ← requireNatLiteralConstructors env (n + 1)
      pure (Expr.mkApps (.const "Nat.succ" []) [.lit (.natVal n)])

partial def whnf (env : Env) (expr : Expr) (levelParams : LevelContext := []) : Result Expr := do
  match expr with
  | .lit _ => pure expr
  | .proj typeName index struct => do
      match ← reduceProjection env typeName index struct (levelParams := levelParams) with
      | some reduced => whnf env reduced (levelParams := levelParams)
      | none =>
          let structWhnf ← whnf env struct (levelParams := levelParams)
          pure (.proj typeName index structWhnf)
  | .app _ _ =>
      let head := expr.getAppFn
      let args := expr.getAppArgs
      let overrideReduced? ←
        match head with
        | .const name levels =>
            match env.find? name with
            | some info =>
                let _ ← info.checkLevelsIn levelParams levels
                reduceKernelOverrideApp env info name levels args (levelParams := levelParams)
            | none => .error s!"unknown constant: {name}"
        | _ => pure none
      match overrideReduced? with
      | some value => whnf env value (levelParams := levelParams)
      | none =>
          let headWhnf ← whnf env head (levelParams := levelParams)
          let rebuilt := Expr.mkApps headWhnf args
          match headWhnf with
          | .lam _ _ body =>
              match args with
              | [] => pure rebuilt
              | arg :: rest =>
                  whnf env (Expr.mkApps (Expr.instantiate1 arg body) rest) (levelParams := levelParams)
          | .const name levels =>
              match env.find? name with
              | some info =>
                  let _ ← info.checkLevelsIn levelParams levels
                  match ← reduceKernelOverrideApp env info name levels args (levelParams := levelParams) with
                  | some value => whnf env value (levelParams := levelParams)
                  | none =>
                      match ← info.value? levels (levelParams := levelParams) with
                      | some value => whnf env (Expr.mkApps value args) (levelParams := levelParams)
                      | none =>
                          match info.kind with
                          | .primitive primitive =>
                              match ← reducePrimitiveApp env name primitive levels args (levelParams := levelParams) with
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
  | .lit _ => pure reduced
  | .lam name ty body => do
      let ty' ← normalize env ty (levelParams := levelParams)
      let body' ← normalize env body (levelParams := levelParams)
      pure (.lam name ty' body')
  | .forallE name ty body => do
      let ty' ← normalize env ty (levelParams := levelParams)
      let body' ← normalize env body (levelParams := levelParams)
      pure (.forallE name ty' body')
  | .proj typeName index struct => do
      let struct' ← normalize env struct (levelParams := levelParams)
      let rebuilt := .proj typeName index struct'
      let whnfRebuilt ← whnf env rebuilt (levelParams := levelParams)
      if whnfRebuilt = rebuilt then
        pure rebuilt
      else
        normalize env whnfRebuilt (levelParams := levelParams)
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
  | .lit literal => do
      let type := Expr.literalType literal
      let _ ← inferSort env ctx type (levelParams := levelParams)
      match literal with
      | .natVal value => requireNatLiteralConstructors env value
      | .strVal _ => pure ()
      pure type
  | .app _ _ => inferApp env ctx expr (levelParams := levelParams)
  | .lam name type body => do
      let _ ← inferSort env ctx type (levelParams := levelParams)
      let bodyTy ← infer env ({ name, type } :: ctx) body (levelParams := levelParams)
      pure (.forallE name type bodyTy)
  | .forallE name domain body => do
      let domainLevel ← inferSort env ctx domain (levelParams := levelParams)
      let bodyLevel ← inferSort env ({ name, type := domain } :: ctx) body (levelParams := levelParams)
      pure (.sort (inferSortOfPi domainLevel bodyLevel))
  | .proj typeName index struct =>
      inferProjection env ctx typeName index struct (levelParams := levelParams)
  | .letE _ type value body => do
      let _ ← inferSort env ctx type (levelParams := levelParams)
      let valueTy ← infer env ctx value (levelParams := levelParams)
      let _ ← checkDefEqIn env ctx valueTy type (levelParams := levelParams)
      infer env ctx (Expr.instantiate1 value body) (levelParams := levelParams)

end

def normalizeForInductiveAnalysis
    (env : Env)
    (expr : Expr)
    (levelParams : LevelContext := []) : Result Expr :=
  whnf env expr (levelParams := levelParams)

partial def positiveParamOccurrence
    (env : Env)
    (self : InductiveSpec)
    (selfPositive : List Bool)
    (openPositive : List (Name × List Bool))
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
    | .lit _ => pure false
    | .letE _ _ _ _ =>
        .error s!"unexpected let-expression in positivity check: {repr expr}"
    | .lam _ _ _ =>
        .error s!"unexpected lambda in positivity check: {repr expr}"
    | .proj _ _ struct =>
        positiveParamOccurrence
          env
          self
          selfPositive
          (openPositive := openPositive)
          targetIndex
          depth
          struct
          (levelParams := levelParams)
    | .forallE _ dom body =>
        if containsBVarAt targetIndex depth dom then
          .error s!"non-positive parameter occurrence in {repr expr}"
        else
          positiveParamOccurrence
            env
            self
            selfPositive
            (openPositive := openPositive)
            targetIndex
            (depth + 1)
            body
            (levelParams := levelParams)
    | .app _ _ =>
        match decomposeInductiveApp env expr with
        | some (headName, info, _, args) =>
            let positiveFlags :=
              match openPositive.find? (fun entry => entry.1 = headName) with
              | some (_, flags) => flags
              | none =>
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
                let arg ← normalizeForInductiveAnalysis env arg (levelParams := levelParams)
                let occurs := containsBVarAt targetIndex depth arg
                if !isPositive then
                  if occurs then
                    .error s!"parameter occurs in a non-positive argument of {headName}"
                else
                  let nested ←
                    positiveParamOccurrence
                      env
                      self
                      selfPositive
                      (openPositive := openPositive)
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

def positiveFlagsFor
    (flags : List (Name × List Bool))
    (name : Name) : Result (List Bool) :=
  match flags.find? (fun entry => entry.1 = name) with
  | some (_, values) => pure values
  | none => .error s!"internal error: missing positive-parameter facts for {name}"

def computePositiveParamsInBlock
    (env : Env)
    (specs : List InductiveSpec) : Result (List (Name × List Bool)) := do
  let initial :=
    specs.map fun spec => (spec.name, List.replicate spec.params.length true)
  let totalParams := specs.foldl (fun total spec => total + spec.params.length) 0
  let rec computeForSpec
      (flags : List (Name × List Bool))
      (spec : InductiveSpec) : Result (Name × List Bool) := do
    let selfPositive ← positiveFlagsFor flags spec.name
    let paramCount := spec.params.length
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
                selfPositive
                (openPositive := flags)
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
    pure (spec.name, next)
  let rec iterate (flags : List (Name × List Bool)) : Nat → Result (List (Name × List Bool))
    | 0 => pure flags
    | fuel + 1 => do
        let next ← specs.mapM (computeForSpec flags)
        if next = flags then
          pure next
        else
          iterate next fuel
  iterate initial (totalParams + 1)

partial def analyzeRecursiveShape
    (env : Env)
    (root : InductiveInfo)
    (recursiveInfos : List InductiveInfo)
    (locals : Telescope)
    (expr : Expr)
    (levelParams : LevelContext := []) : Result RawFieldShape := do
  let expr ← normalizeForInductiveAnalysis env expr (levelParams := levelParams)
  let recursiveInfos :=
    if recursiveInfos.isEmpty then
      [root]
    else
      recursiveInfos
  let recursiveTargets := recursiveInfos.map fun info => recursiveTargetExpr info.spec
  let analyzeInductiveApp
      (headName : Name)
      (info : InductiveInfo)
      (levels : List Level)
      (args : List Expr) :
      Result RawFieldShape := do
    match recursiveInfos.find? (fun recursiveInfo => recursiveInfo.spec.name = headName) with
    | some recursiveInfo =>
      if !levelsDefEq levels (inductiveLevelArgs recursiveInfo.spec) then
        .error s!"recursive occurrence must use the universe parameters of {headName}"
      else
        let paramCount := recursiveInfo.spec.params.length
        let paramArgs ←
          (args.take paramCount).mapM fun arg =>
            normalizeForInductiveAnalysis env arg (levelParams := levelParams)
        let indexArgs ←
          (args.drop paramCount).mapM fun arg =>
            normalizeForInductiveAnalysis env arg (levelParams := levelParams)
        let expr := Expr.mkApps (.const headName levels) (paramArgs ++ indexArgs)
        let expectedParams := Expr.bvarArgs paramCount locals.length
        if !((List.zip paramArgs expectedParams).all fun pair => pair.1.alphaEq pair.2) then
          .error s!"recursive occurrence must use the inductive parameters of {headName}"
        else if indexArgs.any fun arg =>
            containsAnyExprAt recursiveTargets locals.length arg then
          .error s!"recursive occurrence appears inside an index of {headName}"
        else
          pure (.direct { locals, target := expr, headName })
    | none =>
      let mut found := false
      for pair in List.zip args info.positiveParams do
        let arg := pair.1
        let isPositive := pair.2
        let occurs := containsAnyExprAt recursiveTargets locals.length arg
        if occurs then
          let arg ← normalizeForInductiveAnalysis env arg (levelParams := levelParams)
          let occurs := containsAnyExprAt recursiveTargets locals.length arg
          if !isPositive then
            if occurs then
              .error s!"recursive occurrence appears in a non-positive argument of {headName}"
          else
            let shape ←
              analyzeRecursiveShape
                env
                root
                (recursiveInfos := recursiveInfos)
                locals
                arg
                (levelParams := levelParams)
            if rawShapeHasIH shape then
              found := true
      for arg in args.drop info.spec.params.length do
        if containsAnyExprAt recursiveTargets locals.length arg then
          let arg ← normalizeForInductiveAnalysis env arg (levelParams := levelParams)
          if containsAnyExprAt recursiveTargets locals.length arg then
            .error s!"recursive occurrence appears in an index argument of {headName}"
      if found then
        let mut targetArgs : List Expr := []
        for arg in args.take info.spec.params.length do
          let argForSchema ←
            if containsAnyExprAt recursiveTargets locals.length arg || containsLocalBVar locals.length arg then
              normalizeForInductiveAnalysis env arg (levelParams := levelParams)
            else
              pure arg
          targetArgs := targetArgs ++ [argForSchema]
          if containsLocalBVar locals.length argForSchema then
            .error s!"nested inductive parameters cannot contain local variables in {headName}"
        targetArgs := targetArgs ++ args.drop info.spec.params.length
        let expr := Expr.mkApps (.const headName levels) targetArgs
        pure (.nested { locals, target := expr, headName })
      else
        pure .none
  match expr with
  | .bvar _ => pure .none
  | .sort _ => pure .none
  | .lit _ => pure .none
  | .const _ _ =>
      match decomposeInductiveApp env expr with
      | some (headName, info, levels, args) => analyzeInductiveApp headName info levels args
      | none => pure .none
  | .letE _ _ _ _ =>
      .error s!"unexpected let-expression in positivity check: {repr expr}"
  | .lam _ _ _ =>
      .error s!"unexpected lambda in positivity check: {repr expr}"
  | .proj _ _ struct =>
      analyzeRecursiveShape
        env
        root
        (recursiveInfos := recursiveInfos)
        locals
        struct
        (levelParams := levelParams)
  | .forallE name dom body =>
      let dom ← normalizeForInductiveAnalysis env dom (levelParams := levelParams)
      if containsAnyExprAt recursiveTargets locals.length dom then
        .error s!"non-positive recursive occurrence in {repr expr}"
      else
        let binder : Binder := { name, type := dom }
        let bodyShape ←
          analyzeRecursiveShape
            env
            root
            (recursiveInfos := recursiveInfos)
            (locals ++ [binder])
            body
            (levelParams := levelParams)
        match bodyShape with
        | .none => pure .none
        | _ => pure (.pi binder bodyShape)
  | .app _ _ =>
      match decomposeInductiveApp env expr with
      | some (headName, info, levels, args) => analyzeInductiveApp headName info levels args
      | none =>
          if containsAnyExprAt recursiveTargets locals.length expr then
            .error s!"non-positive recursive occurrence in {repr expr}"
          else
            pure .none

partial def internFieldShape
    (schemas : List TargetSchema)
    (shape : RawFieldShape) : Result (FieldShape × List TargetSchema) := do
  match shape with
  | .none => pure (.none, schemas)
  | .direct schema => do
      let schema ← trimTargetSchema schema
      pure (.direct schema, schemas)
  | .pi binder body => do
      let (bodyShape, schemas) ← internFieldShape schemas body
      pure (.pi binder bodyShape, schemas)
  | .nested schema =>
      let schema ← trimTargetSchema schema
      let (index, schemas) := internSchema schemas schema
      pure (.nested index, schemas)

partial def buildRecursorFamily
    (env : Env)
    (root : InductiveInfo)
    (recursiveInfos : List InductiveInfo) : Result RecursorFamily := do
  let rootLevelParams := root.spec.levelParams
  let blockRootName := root.spec.name
  let recursiveNames := recursiveInfos.map (·.spec.name)
  let recursorParams ←
    root.spec.params.mapM fun param => do
      let type ← normalizeForInductiveAnalysis env param.type (levelParams := rootLevelParams)
      pure { param with type }
  let initialSchemas ←
    recursiveInfos.mapM fun info => do
      let target ←
        normalizeForInductiveAnalysis
          env
          (recursiveTargetExpr info.spec)
          (levelParams := rootLevelParams)
      pure { locals := info.spec.indices, target, headName := info.spec.name }
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
        let targetName := familyTargetName blockRootName recursiveNames schemas index
        let targetParamCount := info.spec.params.length
        let bindLocalsInMinors := !(recursiveNames.contains schema.headName)
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
                  recursiveInfos
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
              let (fields, currentSchemas) ← buildFields currentSchemas initialFieldLocals instantiated
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
  let targets ← loop initialSchemas []
  pure
    {
      rootName := root.spec.name
      levelParams := root.spec.levelParams
      motiveLevelParam? :=
        if root.allowsLargeElim then
          some (recursorMotiveLevelParam root.spec)
        else
          none
      k := inductiveSupportsK root.spec
      params := recursorParams
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

def checkNameListUnique (what : String) : List Name → Result Unit
  | [] => pure ()
  | name :: rest =>
      if rest.contains name then
        .error s!"duplicate name in {what}: {name}"
      else
        checkNameListUnique what rest

def checkLevelAtMost
    (what : String)
    (actual bound : Level) : Result Unit :=
  if Level.le actual bound then
    pure ()
  else
    .error
      s!"{what} requires universe {repr (Level.normalize actual)}, \
         but the inductive result is only {repr (Level.normalize bound)}"

def constructorFieldVar? (fieldCount fieldIndex : Nat) : Option Expr :=
  if fieldIndex < fieldCount then
    some (.bvar (fieldCount - 1 - fieldIndex))
  else
    none

def constructorIndexArgs (spec : InductiveSpec) (target : Expr) : List Expr :=
  target.getAppArgs.drop spec.params.length

partial def constructorFieldIsTargetIndex
    (env : Env)
    (ctx : Context)
    (spec : InductiveSpec)
    (ctor : ConstructorSpec)
    (target : Expr)
    (fieldIndex : Nat) : Result (Option Nat) := do
  let some fieldVar := constructorFieldVar? ctor.fields.length fieldIndex
    | .error s!"internal error: invalid constructor field index {fieldIndex}"
  let mut found : Option Nat := none
  for pair in List.zip (List.range spec.indices.length) (constructorIndexArgs spec target) do
    try
      let _ ← checkDefEqIn env ctx fieldVar pair.2 (levelParams := spec.levelParams)
      found := some pair.1
    catch _ =>
      pure ()
  pure found

partial def constructorFieldIsTargetIndexBool
    (env : Env)
    (ctx : Context)
    (spec : InductiveSpec)
    (ctor : ConstructorSpec)
    (target : Expr)
    (fieldIndex : Nat) : Result Bool := do
  pure (← constructorFieldIsTargetIndex env ctx spec ctor target fieldIndex).isSome

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
  pure (ConstantInfo.mkAxiom name levelParams type :: env)

def addAxiom (env : Env) (name : Name) (type : Expr) : Result Env :=
  addAxiomWithLevels env name [] type

def addDefinitionWithHintWithLevels
    (env : Env)
    (name : Name)
    (levelParams : LevelContext)
    (type value : Expr)
    (hint : ReducibilityHint) : Result Env := do
  let _ ← checkLevelParamsUnique levelParams
  let _ ← checkFreshName env name
  let _ ← checkClosedIn levelParams s!"definition {name} type" type
  let _ ← checkClosedIn levelParams s!"definition {name} value" value
  let _ ← inferSort env [] type (levelParams := levelParams)
  let _ ← checkHasType env value type (levelParams := levelParams)
  pure (ConstantInfo.mkDefnWithHint name levelParams type value hint :: env)

def addDefinitionWithLevels
    (env : Env)
    (name : Name)
    (levelParams : LevelContext)
    (type value : Expr) : Result Env :=
  addDefinitionWithHintWithLevels env name levelParams type value (.regular 0)

def addDefinition (env : Env) (name : Name) (type value : Expr) : Result Env :=
  addDefinitionWithLevels env name [] type value

def addDefinitionWithHint
    (env : Env)
    (name : Name)
    (type value : Expr)
    (hint : ReducibilityHint) : Result Env :=
  addDefinitionWithHintWithLevels env name [] type value hint

def addAbbrevWithLevels
    (env : Env)
    (name : Name)
    (levelParams : LevelContext)
    (type value : Expr) : Result Env :=
  addDefinitionWithHintWithLevels env name levelParams type value .abbrev

def addAbbrev (env : Env) (name : Name) (type value : Expr) : Result Env :=
  addAbbrevWithLevels env name [] type value

def addOpaqueDefinitionWithLevels
    (env : Env)
    (name : Name)
    (levelParams : LevelContext)
    (type value : Expr) : Result Env := do
  let _ ← checkLevelParamsUnique levelParams
  let _ ← checkFreshName env name
  let _ ← checkClosedIn levelParams s!"opaque definition {name} type" type
  let _ ← checkClosedIn levelParams s!"opaque definition {name} value" value
  let _ ← inferSort env [] type (levelParams := levelParams)
  let _ ← checkHasType env value type (levelParams := levelParams)
  pure (ConstantInfo.mkOpaqueDefn name levelParams type value :: env)

def addOpaqueDefinition (env : Env) (name : Name) (type value : Expr) : Result Env :=
  addOpaqueDefinitionWithLevels env name [] type value

def addTheoremWithLevels
    (env : Env)
    (name : Name)
    (levelParams : LevelContext)
    (type value : Expr) : Result Env := do
  let _ ← checkLevelParamsUnique levelParams
  let _ ← checkFreshName env name
  let _ ← checkClosedIn levelParams s!"theorem {name} type" type
  let _ ← checkClosedIn levelParams s!"theorem {name} value" value
  let typeSort ← inferSort env [] type (levelParams := levelParams)
  if !Level.defEq typeSort .zero then
    .error s!"theorem {name} type must be a proposition"
  let _ ← checkHasType env value type (levelParams := levelParams)
  pure (ConstantInfo.mkTheorem name levelParams type value :: env)

def addTheorem (env : Env) (name : Name) (type value : Expr) : Result Env :=
  addTheoremWithLevels env name [] type value

def addProjection (env : Env) (name structName : Name) (index : Nat) : Result Env := do
  let _ ← checkFreshName env name
  let some info := env.findInductive? structName
    | .error s!"unknown projection structure: {structName}"
  let projection ← projectionInfo info index
  let type ← projectionFunctionType info index
  let value ← projectionFunctionValue info index
  let levelParams := info.spec.levelParams
  let _ ← checkClosedIn levelParams s!"projection {name} type" type
  let _ ← checkClosedIn levelParams s!"projection {name} value" value
  let _ ← inferSort env [] type (levelParams := levelParams)
  let _ ← checkHasType env value type (levelParams := levelParams)
  pure (ConstantInfo.mkProjection name levelParams type value projection :: env)

def projectionBodyAfterLambdas? : Nat → Expr → Option Expr
  | 0, body => some body
  | count + 1, .lam _ _ body => projectionBodyAfterLambdas? count body
  | _, _ => none

def forallDomainsAndBody? : Nat → Expr → Option (List Expr × Expr)
  | 0, body => some ([], body)
  | count + 1, .forallE _ domain body => do
      let (domains, result) ← forallDomainsAndBody? count body
      some (domain :: domains, result)
  | _, _ => none

def projectionValueIndex? (structName : Name) (paramCount : Nat) (value : Expr) : Option Nat := do
  match (← projectionBodyAfterLambdas? (paramCount + 1) value) with
  | .proj projectedName index (.bvar 0) =>
      if projectedName = structName then
        some index
      else
        none
  | _ => none

def constantProjectionIndex?
    (env : Env)
    (structName projFn : Name)
    (paramCount : Nat) : Option Nat :=
  match env.find? projFn with
  | some { kind := .projection projection, .. } =>
      if projection.structName = structName then
        some projection.index
      else
        none
  | some { valueExpr? := some value, .. } => projectionValueIndex? structName paramCount value
  | _ => none

def checkStructureFieldProjection
    (env : Env)
    (structName projFn : Name)
    (paramCount expectedIndex : Nat) : Result Unit := do
  let some index := constantProjectionIndex? env structName projFn paramCount
    | .error s!"structure field projection is not a checked projection for {structName}: {projFn}"
  if index = expectedIndex then
    pure ()
  else
    .error
      s!"structure field projection {projFn} points to field {index}, \
         but metadata lists it at field {expectedIndex}"

def checkStructureParentSubobject
    (info : StructureInfo)
    (parentInfo : StructureParentInfo) : Result Unit := do
  if parentInfo.subobject then
    let hasMatch :=
      info.fieldInfo.any fun field =>
        field.projFn = parentInfo.projFn && (field.subobject? = some parentInfo.structName)
    if hasMatch then
      pure ()
    else
      .error
        s!"structure parent {parentInfo.structName} is marked as a subobject, \
           but no matching subobject field uses {parentInfo.projFn}"
  else
    pure ()

def checkStructureParentProjection
    (env : Env)
    (childName : Name)
    (paramCount : Nat)
    (parentInfo : StructureParentInfo) : Result Unit := do
  let some projectionInfo := env.find? parentInfo.projFn
    | .error s!"structure parent projection is unknown: {parentInfo.projFn}"
  if projectionInfo.valueExpr?.isNone then
    .error s!"structure parent projection has no checked value: {parentInfo.projFn}"
  let some (domains, resultType) := forallDomainsAndBody? (paramCount + 1) projectionInfo.typeExpr
    | .error
        s!"structure parent projection {parentInfo.projFn} is not a function \
           from {childName} to {parentInfo.structName}"
  let some selfType := listGet? domains paramCount
    | .error s!"structure parent projection {parentInfo.projFn} has no structure argument"
  match selfType.getAppFn with
  | .const sourceName _ =>
      if sourceName = childName then
        pure ()
      else
        .error
          s!"structure parent projection {parentInfo.projFn} takes {sourceName}, \
             not {childName}"
  | _ =>
      .error
        s!"structure parent projection {parentInfo.projFn} does not take \
           {childName}"
  match resultType.getAppFn with
  | .const resultName _ =>
      if resultName = parentInfo.structName then
        pure ()
      else
        .error
          s!"structure parent projection {parentInfo.projFn} returns {resultName}, \
             not {parentInfo.structName}"
  | _ =>
      .error
        s!"structure parent projection {parentInfo.projFn} does not return \
           {parentInfo.structName}"

def checkStructureFields
    (env : Env)
    (info : StructureInfo)
    (paramCount : Nat) : Nat → List Name → Result Unit
  | _, [] => pure ()
  | index, fieldName :: rest => do
      let some fieldInfo := info.fieldInfoFor? fieldName
        | .error s!"structure {info.structName} has no field info for {fieldName}"
      checkStructureFieldProjection env info.structName fieldInfo.projFn paramCount index
      match fieldInfo.subobject? with
      | some parentName =>
          if (env.findStructure? parentName).isNone then
            .error s!"structure field parent is unknown: {parentName}"
      | none => pure ()
      checkStructureFields env info paramCount (index + 1) rest

def registerStructure (env : Env) (info : StructureInfo) : Result Env := do
  let some indInfo := env.findInductive? info.structName
    | .error s!"unknown structure inductive: {info.structName}"
  match indInfo.spec.ctors with
  | [_] => pure ()
  | _ => .error s!"structure {info.structName} must have exactly one constructor"
  let _ ← checkNameListUnique s!"structure {info.structName} fields" info.fieldNames
  let _ ← checkNameListUnique s!"structure {info.structName} field info" (info.fieldInfo.map (·.fieldName))
  let _ ← checkNameListUnique s!"structure {info.structName} parents" (info.parentInfo.map (·.structName))
  let _ ← checkStructureFields env info indInfo.spec.params.length 0 info.fieldNames
  for fieldInfo in info.fieldInfo do
    if !info.fieldNames.contains fieldInfo.fieldName then
      .error s!"structure field info is not listed as a field: {fieldInfo.fieldName}"
  for parentInfo in info.parentInfo do
    if (env.findStructure? parentInfo.structName).isNone then
      .error s!"structure parent is unknown: {parentInfo.structName}"
    checkStructureParentProjection env info.structName indInfo.spec.params.length parentInfo
    checkStructureParentSubobject info parentInfo
  Env.updateInductiveInfo env info.structName fun indInfo =>
    { indInfo with structureInfo? := some info }

def quotientRelationType : Expr :=
  .forallE "a" (.bvar 0) (.forallE "b" (.bvar 1) (.sort .zero))

def quotientTypeFormerType : Expr :=
  Telescope.bindForall
    [
      { name := "α", type := .sort (.param "u") },
      { name := "r", type := quotientRelationType }
    ]
    (.sort (.param "u"))

def quotientMkType : Expr :=
  Telescope.bindForall
    [
      { name := "α", type := .sort (.param "u") },
      { name := "r", type := quotientRelationType },
      { name := "a", type := .bvar 1 }
    ]
    (quotientTypeExpr (.param "u") (.bvar 2) (.bvar 1))

def quotientLiftRespType : Expr :=
  .forallE
    "a"
    (.bvar 3)
    (.forallE
      "b"
      (.bvar 4)
      (.forallE
        "h"
        (Expr.mkApps (.bvar 4) [.bvar 1, .bvar 0])
        (eqTypeExpr
          (.param "v")
          (.bvar 4)
          (.app (.bvar 3) (.bvar 2))
          (.app (.bvar 3) (.bvar 1)))))

def quotientLiftType : Expr :=
  Telescope.bindForall
    [
      { name := "α", type := .sort (.param "u") },
      { name := "r", type := quotientRelationType },
      { name := "β", type := .sort (.param "v") },
      { name := "f", type := .forallE "a" (.bvar 2) (.bvar 1) },
      { name := "resp", type := quotientLiftRespType },
      { name := "q", type := quotientTypeExpr (.param "u") (.bvar 4) (.bvar 3) }
    ]
    (.bvar 3)

def quotientIndType : Expr :=
  Telescope.bindForall
    [
      { name := "α", type := .sort (.param "u") },
      { name := "r", type := quotientRelationType },
      {
        name := "motive"
        type := .forallE "q" (quotientTypeExpr (.param "u") (.bvar 1) (.bvar 0)) (.sort .zero)
      },
      {
        name := "mk"
        type :=
          .forallE
            "a"
            (.bvar 2)
            (.app (.bvar 1) (quotientMkExpr (.param "u") (.bvar 3) (.bvar 2) (.bvar 0)))
      },
      { name := "q", type := quotientTypeExpr (.param "u") (.bvar 3) (.bvar 2) }
    ]
    (.app (.bvar 2) (.bvar 0))

def quotientSoundType : Expr :=
  Telescope.bindForall
    [
      { name := "α", type := .sort (.param "u") },
      { name := "r", type := quotientRelationType },
      { name := "a", type := .bvar 1 },
      { name := "b", type := .bvar 2 },
      { name := "h", type := Expr.mkApps (.bvar 2) [.bvar 1, .bvar 0] }
    ]
    (eqTypeExpr
      (.param "u")
      (quotientTypeExpr (.param "u") (.bvar 4) (.bvar 3))
      (quotientMkExpr (.param "u") (.bvar 4) (.bvar 3) (.bvar 2))
      (quotientMkExpr (.param "u") (.bvar 4) (.bvar 3) (.bvar 1)))

def addPrimitive
    (env : Env)
    (name : Name)
    (levelParams : LevelContext)
    (type : Expr)
    (primitive : PrimitiveInfo) : Result Env := do
  let _ ← checkLevelParamsUnique levelParams
  let _ ← checkFreshName env name
  let _ ← checkClosedIn levelParams s!"primitive {name}" type
  let _ ← inferSort env [] type (levelParams := levelParams)
  pure (ConstantInfo.mkPrimitive name levelParams type primitive :: env)

def addQuotPrimitives (env : Env) : Result Env := do
  let env ← addPrimitive env "Quot" ["u"] quotientTypeFormerType .quotType
  let env ← addPrimitive env "Quot.mk" ["u"] quotientMkType .quotMk
  let env ← addPrimitive env "Quot.lift" ["u", "v"] quotientLiftType .quotLift
  let env ← addPrimitive env "Quot.ind" ["u"] quotientIndType .quotInd
  addPrimitive env "Quot.sound" ["u"] quotientSoundType .quotSound

def telescopeTypesAlphaEq (left right : Telescope) : Bool :=
  left.length = right.length &&
    (List.zip left right).all fun pair => pair.1.type.alphaEq pair.2.type

def checkBlockNames (env : Env) (specs : List InductiveSpec) : Result (List Name) := do
  let mut seenNames : List Name := []
  for spec in specs do
    for name in [spec.name, recursorName spec.name] do
      if seenNames.contains name then
        .error s!"duplicate name in inductive block: {name}"
      let _ ← checkFreshName env name
      seenNames := name :: seenNames
    for ctor in spec.ctors do
      if seenNames.contains ctor.name then
        .error s!"duplicate name in inductive block: {ctor.name}"
      let _ ← checkFreshName env ctor.name
      seenNames := ctor.name :: seenNames
  pure seenNames

def checkInductiveHeader
    (env : Env)
    (block : InductiveBlockSpec)
    (sharedParams : Telescope)
    (spec : InductiveSpec) : Result Unit := do
  if spec.levelParams != block.levelParams then
    .error s!"inductive {spec.name} must use the block universe parameters"
  if !telescopeTypesAlphaEq spec.params sharedParams then
    .error s!"inductive {spec.name} must use the block parameter telescope"
  if !spec.level.closedIn block.levelParams then
    .error s!"inductive result universe must be closed under its universe parameters: {repr spec.level}"
  if !inductiveIsProp spec && !inductiveIsData spec && !inductiveIsSortPolymorphicSubsingleton spec then
    .error
      s!"inductive result universe is neither Prop, data, nor a supported \
         sort-polymorphic subsingleton: {repr spec.level}"
  let _ ← checkTelescope env spec.params (levelParams := block.levelParams)
  let paramCtx := Telescope.toContext spec.params
  let _ ← checkTelescopeFrom env paramCtx spec.indices (levelParams := block.levelParams)

def checkDataUniverseBounds
    (tempEnv : Env)
    (spec : InductiveSpec) : Result Unit := do
  let paramCtx := Telescope.toContext spec.params
  if !inductiveIsProp spec then
    for ctor in spec.ctors do
      let rec checkFieldLevels (ctx : Context) : Telescope → Result Unit
        | [] => pure ()
        | field :: rest => do
            let level ← inferSort tempEnv ctx field.type (levelParams := spec.levelParams)
            let _ ← checkLevelAtMost s!"field {ctor.name}.{field.name}" level spec.level
            checkFieldLevels (Telescope.withBinder ctx field) rest
      let _ ← checkFieldLevels paramCtx ctor.fields

def checkConstructorTargets (tempEnv : Env) (spec : InductiveSpec) : Result Unit := do
  let paramCtx := Telescope.toContext spec.params
  for ctor in spec.ctors do
    let fieldCtx ← checkTelescopeFrom tempEnv paramCtx ctor.fields (levelParams := spec.levelParams)
    let target ← constructorTargetExpr spec ctor
    let _ ← checkConstructorTargetExpr spec ctor target
    let _ ← inferSort tempEnv fieldCtx target (levelParams := spec.levelParams)

def computeAllowsLargeElim
    (tempEnv : Env)
    (spec : InductiveSpec) : Result Bool := do
  if !inductiveIsProp spec then
    pure true
  else
    match spec.ctors with
    | [] => pure true
    | [ctor] =>
        let paramCtx := Telescope.toContext spec.params
        let target ← constructorTargetExpr spec ctor
        let allFieldCtx ← checkTelescopeFrom tempEnv paramCtx ctor.fields (levelParams := spec.levelParams)
        let rec checkFields (ctx : Context) (fieldIndex : Nat) : Telescope → Result Bool
          | [] => pure true
          | field :: rest => do
              let fieldSort ← inferSort tempEnv ctx field.type (levelParams := spec.levelParams)
              let isIndex ←
                constructorFieldIsTargetIndexBool
                  tempEnv
                  allFieldCtx
                  spec
                  ctor
                  target
                  fieldIndex
              if Level.defEq fieldSort .zero || isIndex then
                checkFields (Telescope.withBinder ctx field) (fieldIndex + 1) rest
              else
                pure false
        checkFields paramCtx 0 ctor.fields
    | _ => pure false

def computeProjectionFields
    (tempEnv : Env)
    (spec : InductiveSpec) : Result (List Nat × List (Nat × Nat)) := do
  match spec.ctors with
  | [ctor] =>
      let paramCtx := Telescope.toContext spec.params
      let target ← constructorTargetExpr spec ctor
      let allFieldCtx ← checkTelescopeFrom tempEnv paramCtx ctor.fields (levelParams := spec.levelParams)
      let mut projectionFields : List Nat := []
      let mut indexFields : List (Nat × Nat) := []
      for fieldIndex in List.range ctor.fields.length do
        match ← constructorFieldIsTargetIndex tempEnv allFieldCtx spec ctor target fieldIndex with
        | some indexPosition => indexFields := indexFields ++ [(fieldIndex, indexPosition)]
        | none => projectionFields := projectionFields ++ [fieldIndex]
      pure (projectionFields, indexFields)
  | _ => pure ([], [])

def addInductiveBlock (env : Env) (block : InductiveBlockSpec) : Result Env := do
  let _ ← checkLevelParamsUnique block.levelParams
  let firstSpec ←
    match block.specs with
    | [] => .error "inductive block must contain at least one inductive"
    | spec :: _ => pure spec
  let mut seenNames ← checkBlockNames env block.specs
  for spec in block.specs do
    let _ ← checkInductiveHeader env block firstSpec.params spec
  let provisionalInfos : List InductiveInfo :=
    block.specs.map fun spec =>
      {
        type := inductiveTypeExpr spec
        spec
        positiveParams := List.replicate spec.params.length true
        allowsLargeElim := !inductiveIsProp spec
      }
  let provisionalEnv :=
    (List.zip block.specs provisionalInfos).map
      (fun pair => ConstantInfo.mkInductive pair.1.name block.levelParams pair.2) ++ env
  for spec in block.specs do
    let _ ← checkConstructorTargets provisionalEnv spec
    let _ ← checkDataUniverseBounds provisionalEnv spec
  let positiveFacts ← computePositiveParamsInBlock provisionalEnv block.specs
  let finalInfos ←
    block.specs.mapM fun spec => do
      let positiveParams ← positiveFlagsFor positiveFacts spec.name
      let allowsLargeElim ← computeAllowsLargeElim provisionalEnv spec
      let (projectionFields, indexFields) ← computeProjectionFields provisionalEnv spec
      pure
        {
          type := inductiveTypeExpr spec
          spec
          positiveParams
          allowsLargeElim
          projectionFields
          indexFields
        }
  let infoEnv :=
    (List.zip block.specs finalInfos).map
      (fun pair => ConstantInfo.mkInductive pair.1.name block.levelParams pair.2) ++ env
  let blockFamily ←
    match finalInfos with
    | [] => .error "inductive block must contain at least one inductive"
    | rootInfo :: _ => buildRecursorFamily infoEnv rootInfo finalInfos
  let recursiveNames := finalInfos.map (·.spec.name)
  for target in blockFamily.targets do
    if !(recursiveNames.contains target.schema.headName) then
      if seenNames.contains target.recName then
        .error s!"duplicate name in inductive block: {target.recName}"
      let _ ← checkFreshName env target.recName
      seenNames := target.recName :: seenNames
  let mut ctorInfos : List ConstantInfo := []
  for spec in block.specs do
    for ctor in spec.ctors do
      let ctorType ← constructorTypeExpr spec ctor
      let _ ←
        validateGeneratedType
          infoEnv
          s!"generated constructor {ctor.name} type"
          block.levelParams
          ctorType
      ctorInfos := ConstantInfo.mkCtor ctor.name block.levelParams ctorType spec.name :: ctorInfos
  let ctorEnv := ctorInfos ++ infoEnv
  let mut recInfos : List ConstantInfo := []
  for pair in List.zip (List.range blockFamily.targets.length) blockFamily.targets do
    let recType ← buildRecursorType blockFamily pair.1
    let recLevelParams := recursorLevelParamsForFamily blockFamily
    let _ ←
      validateGeneratedType
        ctorEnv
        s!"generated recursor {pair.2.recName} type"
        recLevelParams
        recType
    recInfos :=
      ConstantInfo.mkRecursor pair.2.recName recLevelParams recType pair.1 blockFamily :: recInfos
  let inductiveInfos :=
    (List.zip block.specs finalInfos).map
      (fun pair => ConstantInfo.mkInductive pair.1.name block.levelParams pair.2)
  pure (recInfos ++ ctorInfos ++ inductiveInfos ++ env)

def addInductive (env : Env) (spec : InductiveSpec) : Result Env :=
  addInductiveBlock env { levelParams := spec.levelParams, specs := [spec] }

def decomposeForalls : Expr → Telescope × Expr
  | .forallE name type body =>
      let (binders, result) := decomposeForalls body
      ({ name, type } :: binders, result)
  | expr => ([], expr)

def splitAt? (n : Nat) (xs : List α) : Option (List α × List α) :=
  if n <= xs.length then
    some (xs.take n, xs.drop n)
  else
    none

def kernelInductiveHeaderToSpec
    (decl : KernelInductiveDecl)
    (typeDecl : KernelInductiveTypeDecl) : Result InductiveSpec := do
  let (binders, result) := decomposeForalls typeDecl.type
  let some (params, indices) := splitAt? decl.numParams binders
    | .error s!"kernel inductive {typeDecl.name} has fewer parameters than declared"
  let .sort level := result
    | .error s!"kernel inductive {typeDecl.name} type must end in a sort"
  pure
    {
      name := typeDecl.name
      levelParams := decl.levelParams
      params
      indices
      level
      ctors := []
    }

def kernelConstructorToSpec
    (decl : KernelInductiveDecl)
    (spec : InductiveSpec)
    (ctor : KernelConstructorDecl) : Result ConstructorSpec := do
  let (binders, target) := decomposeForalls ctor.type
  let some (params, fields) := splitAt? decl.numParams binders
    | .error s!"kernel constructor {ctor.name} has fewer parameters than declared"
  if !telescopeTypesAlphaEq params spec.params then
    .error s!"kernel constructor {ctor.name} parameter telescope does not match {spec.name}"
  pure { name := ctor.name, fields, target? := some target }

def kernelInductiveDeclToBlock (decl : KernelInductiveDecl) : Result InductiveBlockSpec := do
  match decl.types with
  | [] => .error "kernel inductive declaration must contain at least one type"
  | firstType :: restTypes => do
      let firstSpec ← kernelInductiveHeaderToSpec decl firstType
      let restSpecs ← restTypes.mapM (kernelInductiveHeaderToSpec decl)
      for spec in restSpecs do
        if !telescopeTypesAlphaEq spec.params firstSpec.params then
          .error s!"kernel inductive {spec.name} parameter telescope does not match the block"
      let allTypes := firstType :: restTypes
      let allSpecs := firstSpec :: restSpecs
      let specs ←
        (List.zip allTypes allSpecs).mapM fun pair => do
          let ctors ← pair.1.ctors.mapM (kernelConstructorToSpec decl pair.2)
          pure { pair.2 with ctors }
      pure { levelParams := decl.levelParams, specs }

def addKernelInductive (env : Env) (decl : KernelInductiveDecl) : Result Env := do
  let block ← kernelInductiveDeclToBlock decl
  addInductiveBlock env block

def exportedGeneratedTypeMatches
    (actualParams exportedParams : LevelContext)
    (actualType exportedType : Expr) : Result Bool := do
  if actualParams.length != exportedParams.length then
    pure false
  else
    let renamedExportedType :=
      Expr.instantiateLevels exportedParams (actualParams.map Level.param) exportedType
    pure (actualType.alphaEq renamedExportedType)

def checkGeneratedConstructor
    (env : Env)
    (name : Name)
    (levelParams : LevelContext)
    (type : Expr)
    (indName : Name) : Result Env := do
  let some info := env.find? name
    | .error s!"generated constructor is missing: {name}"
  match info.kind with
  | .ctor actualIndName =>
      if actualIndName != indName then
        .error s!"generated constructor {name} belongs to {actualIndName}, not {indName}"
      if !(← exportedGeneratedTypeMatches info.levelParams levelParams info.typeExpr type) then
        .error s!"generated constructor {name} type does not match"
      pure env
  | _ => .error s!"constant is not a generated constructor: {name}"

def checkGeneratedRecursor
    (env : Env)
    (name : Name)
    (levelParams : LevelContext)
    (type : Expr) : Result Env := do
  let some info := env.find? name
    | .error s!"generated recursor is missing: {name}"
  match info.kind with
  | .primitive (.recursor _ _) =>
      if !(← exportedGeneratedTypeMatches info.levelParams levelParams info.typeExpr type) then
        .error s!"generated recursor {name} type does not match: expected {repr info.typeExpr}, exported {repr type}"
      pure env
  | _ => .error s!"constant is not a generated recursor: {name}"

def generatedRecursorBlockNames (family : RecursorFamily) : List Name :=
  family.targets.foldl
    (fun names target =>
      if target.recName = recursorName target.schema.headName then
        appendNewNames names [target.schema.headName]
      else
        names)
    []

def recursorCommonBinders (family : RecursorFamily) : Result Telescope := do
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
  pure (family.params ++ motiveBinders ++ minorBinders)

partial def expectedRecursorRuleRhs
    (family : RecursorFamily)
    (targetIndex : Nat)
    (target : FamilyTarget)
    (ctor : FamilyCtor) : Result Expr := do
  if target.bindLocalsInMinors && !target.schema.locals.isEmpty then
    .error s!"cannot synthesize recursor rule RHS for helper target with explicit locals: {target.recName}"
  let commonBinders ← recursorCommonBinders family
  let paramCount := family.params.length
  let motiveCount := family.targets.length
  let minorEntries := familyMinorEntries family
  let minorCount := minorEntries.length
  let levels := (recursorLevelParamsForFamily family).map Level.param
  let rec bindFields
      (paramVars motiveVars minorVars previousFields fieldVars : List Expr) :
      List FamilyField → Result Expr
    | [] => do
        let some minor := lookupMinorExpr? family minorVars targetIndex ctor.name
          | .error s!"internal error: missing minor premise for {ctor.name}"
        let prefixArgs := paramVars ++ motiveVars ++ minorVars
        let mut ihArgs : List Expr := []
        let mut previousFields : List Expr := []
        for pair in List.zip ctor.fields fieldVars do
          let field := pair.1
          let fieldArg := pair.2
          if shapeHasIH field.shape then
            let ih ←
              ihTerm
                family
                levels
                prefixArgs
                paramVars
                previousFields
                field.shape
                fieldArg
            ihArgs := ihArgs ++ [ih]
          previousFields := previousFields ++ [fieldArg]
        pure (Expr.mkApps minor (fieldVars ++ ihArgs))
    | field :: rest => do
        let fieldTy := Expr.instantiateMany (paramVars ++ previousFields) field.binder.type
        let body ←
          bindFields
            (paramVars.map (Expr.lift 1))
            (motiveVars.map (Expr.lift 1))
            (minorVars.map (Expr.lift 1))
            (previousFields.map (Expr.lift 1) ++ [.bvar 0])
            (fieldVars.map (Expr.lift 1) ++ [.bvar 0])
            rest
        pure (.lam field.binder.name fieldTy body)
  let body ←
    bindFields
      (Expr.bvarArgs paramCount (motiveCount + minorCount))
      (Expr.bvarArgs motiveCount minorCount)
      (Expr.bvarArgs minorCount 0)
      []
      []
      ctor.fields
  pure (Telescope.bindLambda commonBinders body)

def expectedRecursorRuleInfo
    (family : RecursorFamily)
    (targetIndex : Nat)
    (target : FamilyTarget)
    (ctor : FamilyCtor) : GeneratedRecursorRuleInfo :=
  let rhs? :=
    match expectedRecursorRuleRhs family targetIndex target ctor with
    | .ok rhs => some rhs
    | .error _ => none
  { ctor := ctor.name, nfields := ctor.fields.length, rhs? }

def expectedGeneratedRecursorInfo
    (targetIndex : Nat)
    (family : RecursorFamily) : Result GeneratedRecursorInfo := do
  let some target := listGet? family.targets targetIndex
    | .error s!"internal error: invalid recursor target index {targetIndex}"
  pure
    {
      all := generatedRecursorBlockNames family
      numParams := family.params.length
      numIndices := target.schema.locals.length
      numMotives := family.targets.length
      numMinors := familyMinorCount family
      k := family.k
      rules := target.ctors.map (expectedRecursorRuleInfo family targetIndex target)
    }

def recursorRuleHeaderEq (left right : GeneratedRecursorRuleInfo) : Bool :=
  left.ctor = right.ctor && left.nfields = right.nfields

def checkGeneratedRecursorInfo
    (name : Name)
    (actualLevelParams exportedLevelParams : LevelContext)
    (actual expected : GeneratedRecursorInfo) : Result Unit := do
  if actual.all != expected.all then
    .error s!"generated recursor {name} block members do not match"
  if actual.numParams != expected.numParams then
    .error s!"generated recursor {name} parameter count does not match"
  if actual.numIndices != expected.numIndices then
    .error s!"generated recursor {name} index count does not match"
  if actual.numMotives != expected.numMotives then
    .error s!"generated recursor {name} motive count does not match"
  if actual.numMinors != expected.numMinors then
    .error s!"generated recursor {name} minor count does not match"
  if actual.k != expected.k then
    .error s!"generated recursor {name} K-reduction flag does not match"
  if actual.rules.length != expected.rules.length ||
      !(List.zip actual.rules expected.rules).all (fun pair => recursorRuleHeaderEq pair.1 pair.2) then
    .error s!"generated recursor {name} rule headers do not match"
  for pair in List.zip actual.rules expected.rules do
    match pair.1.rhs?, pair.2.rhs? with
    | some actualRhs, some expectedRhs =>
        if !(← exportedGeneratedTypeMatches actualLevelParams exportedLevelParams expectedRhs actualRhs) then
          .error s!"generated recursor {name} rule RHS for {pair.1.ctor} does not match"
    | some _, none =>
        .error s!"generated recursor {name} has no local RHS for {pair.1.ctor}"
    | none, _ => pure ()

def checkGeneratedRecursorWithInfo
    (env : Env)
    (name : Name)
    (levelParams : LevelContext)
    (type : Expr)
    (metadata : GeneratedRecursorInfo) : Result Env := do
  let some info := env.find? name
    | .error s!"generated recursor is missing: {name}"
  match info.kind with
  | .primitive (.recursor targetIndex family) =>
      if !(← exportedGeneratedTypeMatches info.levelParams levelParams info.typeExpr type) then
        .error s!"generated recursor {name} type does not match: expected {repr info.typeExpr}, exported {repr type}"
      let expected ← expectedGeneratedRecursorInfo targetIndex family
      let _ ← checkGeneratedRecursorInfo name info.levelParams levelParams metadata expected
      pure env
  | _ => .error s!"constant is not a generated recursor: {name}"

def checkPrimitiveDeclaration
    (env : Env)
    (name : Name)
    (levelParams : LevelContext)
    (type : Expr)
    (primitive : PrimitiveInfo) : Result Env := do
  let some info := env.find? name
    | .error s!"unknown primitive declaration: {name}"
  match info.kind with
  | .primitive actual =>
      if actual != primitive then
        .error s!"primitive kind does not match for {name}"
      else if !(← exportedGeneratedTypeMatches info.levelParams levelParams info.typeExpr type) then
        .error s!"primitive {name} type does not match: expected {repr info.typeExpr}, exported {repr type}"
      else
        pure env
  | _ => .error s!"constant is not a primitive declaration: {name}"

def addDeclaration (env : Env) : Declaration → Result Env
  | .axiom name levelParams type => addAxiomWithLevels env name levelParams type
  | .definition name levelParams type value =>
      addDefinitionWithLevels env name levelParams type value
  | .definitionWithHint name levelParams hint type value =>
      addDefinitionWithHintWithLevels env name levelParams type value hint
  | .opaqueDefinition name levelParams type value =>
      addOpaqueDefinitionWithLevels env name levelParams type value
  | .theorem name levelParams type value => addTheoremWithLevels env name levelParams type value
  | .inductive spec => addInductive env spec
  | .inductiveBlock block => addInductiveBlock env block
  | .kernelInductive decl => addKernelInductive env decl
  | .generatedConstructor name levelParams type indName =>
      checkGeneratedConstructor env name levelParams type indName
  | .generatedRecursor name levelParams type =>
      checkGeneratedRecursor env name levelParams type
  | .generatedRecursorWithInfo name levelParams type metadata =>
      checkGeneratedRecursorWithInfo env name levelParams type metadata
  | .structureInfo info => registerStructure env info
  | .projection name structName index => addProjection env name structName index
  | .quotientPrimitives => addQuotPrimitives env
  | .primitiveCheck name levelParams type primitive =>
      checkPrimitiveDeclaration env name levelParams type primitive

namespace Declaration

def inductiveDefinedNames (spec : InductiveSpec) : List Name :=
  spec.name :: recursorName spec.name :: spec.ctors.map (·.name)

def definedNames : Declaration → List Name
  | .axiom name .. => [name]
  | .definition name .. => [name]
  | .definitionWithHint name .. => [name]
  | .opaqueDefinition name .. => [name]
  | .theorem name .. => [name]
  | .inductive spec => inductiveDefinedNames spec
  | .inductiveBlock block => block.specs.foldl (fun names spec => appendNewNames names (inductiveDefinedNames spec)) []
  | .kernelInductive decl =>
      decl.types.foldl
        (fun names typeDecl =>
          appendNewNames
            names
            (typeDecl.name :: recursorName typeDecl.name :: typeDecl.ctors.map (·.name)))
        []
  | .generatedConstructor .. => []
  | .generatedRecursor .. => []
  | .generatedRecursorWithInfo .. => []
  | .structureInfo .. => []
  | .projection name .. => [name]
  | .quotientPrimitives => ["Quot", "Quot.mk", "Quot.lift", "Quot.ind", "Quot.sound"]
  | .primitiveCheck .. => []

def constructorSpecConstants (ctor : ConstructorSpec) : List Name :=
  let fieldConstants := telescopeConstants ctor.fields
  match ctor.target? with
  | some target => appendNewNames fieldConstants (exprConstants target)
  | none => fieldConstants

def inductiveSpecConstants (spec : InductiveSpec) : List Name :=
  let base := appendNewNames (telescopeConstants spec.params) (telescopeConstants spec.indices)
  spec.ctors.foldl
    (fun names ctor => appendNewNames names (constructorSpecConstants ctor))
    base

def kernelInductiveTypeConstants (typeDecl : KernelInductiveTypeDecl) : List Name :=
  typeDecl.ctors.foldl
    (fun names ctor => appendNewNames names (exprConstants ctor.type))
    (exprConstants typeDecl.type)

def structureInfoConstants (info : StructureInfo) : List Name :=
  let fieldConstants :=
    info.fieldInfo.foldl
      (fun names field =>
        appendNewNames
          names
          (field.projFn :: field.subobject?.toList))
      []
  let parentConstants :=
    info.parentInfo.foldl
      (fun names parent => appendNewNames names [parent.structName, parent.projFn])
      []
  appendNewNames (info.structName :: fieldConstants) parentConstants

def usedConstants : Declaration → List Name
  | .axiom _ _ type => exprConstants type
  | .definition _ _ type value => appendNewNames (exprConstants type) (exprConstants value)
  | .definitionWithHint _ _ _ type value => appendNewNames (exprConstants type) (exprConstants value)
  | .opaqueDefinition _ _ type value => appendNewNames (exprConstants type) (exprConstants value)
  | .theorem _ _ type value => appendNewNames (exprConstants type) (exprConstants value)
  | .inductive spec => inductiveSpecConstants spec
  | .inductiveBlock block =>
      block.specs.foldl (fun names spec => appendNewNames names (inductiveSpecConstants spec)) []
  | .kernelInductive decl =>
      decl.types.foldl (fun names typeDecl => appendNewNames names (kernelInductiveTypeConstants typeDecl)) []
  | .generatedConstructor name _ type indName =>
      appendNewNames [name, indName] (exprConstants type)
  | .generatedRecursor name _ type =>
      appendNewNames [name] (exprConstants type)
  | .generatedRecursorWithInfo name _ type metadata =>
      let ruleConstants := metadata.rules.map (·.ctor)
      appendNewNames (name :: metadata.all) (appendNewNames ruleConstants (exprConstants type))
  | .structureInfo info => structureInfoConstants info
  | .projection _ structName _ => [structName]
  | .quotientPrimitives => ["Eq"]
  | .primitiveCheck name _ type _ => appendNewNames [name] (exprConstants type)

end Declaration

def declarationReplayNames : Declaration → List Name
  | .structureInfo info => [info.structName]
  | .generatedConstructor name .. => [name]
  | .generatedRecursor name .. => [name]
  | .generatedRecursorWithInfo name .. => [name]
  | .primitiveCheck name .. => [name]
  | declaration => declaration.definedNames

def structureFieldReady (env : Env) (field : StructureFieldInfo) : Bool :=
  env.contains field.projFn &&
    match field.subobject? with
    | some parentName => (env.findStructure? parentName).isSome
    | none => true

def structureParentReady (env : Env) (parent : StructureParentInfo) : Bool :=
  (env.findStructure? parent.structName).isSome && env.contains parent.projFn

def structureInfoReady (env : Env) (info : StructureInfo) : Bool :=
  env.contains info.structName &&
    info.fieldInfo.all (structureFieldReady env) &&
    info.parentInfo.all (structureParentReady env)

def declarationReady (env : Env) (decl : Declaration) : Bool :=
  match decl with
  | .structureInfo info => structureInfoReady env info
  | _ =>
      let localNames := decl.definedNames
      decl.usedConstants.all fun name => env.contains name || localNames.contains name

def declarationsDefinedNames (declarations : List Declaration) : List Name :=
  declarations.foldl
    (fun names declaration => appendNewNames names (declarationReplayNames declaration))
    []

partial def replayDeclarationsWithFuel
    (fuel : Nat)
    (env : Env)
    (declarations : List Declaration) : Result Env := do
  match declarations with
  | [] => pure env
  | _ =>
      match fuel with
      | 0 => .error s!"unresolved declaration dependencies: {repr (declarationsDefinedNames declarations)}"
      | fuel + 1 =>
          let mut env := env
          let mut remaining : List Declaration := []
          let mut progressed := false
          for declaration in declarations do
            if declarationReady env declaration then
              env ←
                match addDeclaration env declaration with
                | .ok newEnv => pure newEnv
                | .error err =>
                    .error s!"while replaying {repr (declarationReplayNames declaration)}: {err}"
              progressed := true
            else
              remaining := remaining ++ [declaration]
          if !progressed then
            .error s!"unresolved declaration dependencies: {repr (declarationsDefinedNames remaining)}"
          replayDeclarationsWithFuel fuel env remaining

def replayDeclarations (env : Env) (declarations : List Declaration) : Result Env :=
  replayDeclarationsWithFuel (declarations.length + 1) env declarations

def addDeclarations : Env → List Declaration → Result Env
  | env, [] => pure env
  | env, declaration :: rest => do
      let env ← addDeclaration env declaration
      addDeclarations env rest

end LeanLean
