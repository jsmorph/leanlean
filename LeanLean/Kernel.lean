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

inductive FieldShape where
  | none : FieldShape
  | direct : FieldShape
  | pi : String → Expr → FieldShape → FieldShape
  | nested : Expr → FieldShape
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
  typeExpr : Expr
  headName : Name
  ctors : List FamilyCtor
  deriving DecidableEq, Repr, Inhabited

structure RecursorFamily where
  rootName : Name
  params : List Binder
  targets : List FamilyTarget
  deriving DecidableEq, Repr, Inhabited

structure InductiveInfo where
  type : Expr
  spec : InductiveSpec
  positiveParams : List Bool
  deriving DecidableEq, Repr, Inhabited

inductive ConstantInfo where
  | axiom : Name → Expr → ConstantInfo
  | defn : Name → Expr → Expr → ConstantInfo
  | inductive : Name → InductiveInfo → ConstantInfo
  | ctor : Name → Expr → Name → ConstantInfo
  | recursor : Name → Nat → RecursorFamily → ConstantInfo
  deriving DecidableEq, Repr, Inhabited

abbrev Context := List Binder
abbrev Env := List ConstantInfo
abbrev Result := Except String

namespace ConstantInfo

def name : ConstantInfo → Name
  | .axiom name _ => name
  | .defn name _ _ => name
  | .inductive name _ => name
  | .ctor name _ _ => name
  | .recursor name _ _ => name

def type? : ConstantInfo → Option Expr
  | .axiom _ type => some type
  | .defn _ type _ => some type
  | .inductive _ info => some info.type
  | .ctor _ type _ => some type
  | .recursor _ _ _ => none

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
  | some (.inductive _ info) => some info
  | _ => none

def findCtor? (env : Env) (target : Name) : Option Name :=
  match find? env target with
  | some (.ctor _ _ indName) => some indName
  | _ => none

def findRecursor? (env : Env) (target : Name) : Option (Nat × RecursorFamily) :=
  match find? env target with
  | some (.recursor _ index family) => some (index, family)
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
  Level.normalize (.max domain codomain)

def withBinder (ctx : Context) (binder : Binder) : Context :=
  binder :: ctx

def instantiateBinderType (values : List Expr) (binder : Binder) : Expr :=
  Expr.instantiateMany values binder.type

def recursiveTargetExpr (spec : InductiveSpec) : Expr :=
  inductiveTarget spec.name (Expr.bvarArgs spec.params.length 0)

def helperRecursorName (indName : Name) (index : Nat) : Name :=
  recursorName indName ++ "_" ++ toString index

def shapeHasIH : FieldShape → Bool
  | .none => false
  | .direct => true
  | .pi _ _ body => shapeHasIH body
  | .nested _ => true

def shapeNestedTargets : FieldShape → List Expr
  | .none => []
  | .direct => []
  | .pi _ _ body => shapeNestedTargets body
  | .nested expr => [expr]

def containsExprAt (target : Expr) (depth : Nat) (expr : Expr) : Bool :=
  if expr = Expr.lift depth target then
    true
  else
    match expr with
    | .bvar _ => false
    | .sort _ => false
    | .const _ => false
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
  | .const _ => false
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
  | .const name =>
      match env.findInductive? name with
      | some info =>
          if args.length = info.spec.params.length then
            some (name, info, args)
          else
            none
      | none => none
  | _ => none

partial def positiveParamOccurrence
    (env : Env)
    (self : InductiveSpec)
    (selfPositive : List Bool)
    (targetIndex depth : Nat)
    (expr : Expr) : Result Bool := do
  if expr = Expr.bvar (targetIndex + depth) then
    pure true
  else
    match expr with
    | .bvar _ => pure false
    | .sort _ => pure false
    | .const _ => pure false
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
                | .ok occurs =>
                    if !occurs && containsBVarAt baseIndex 0 field.type then
                      positive := false
                | .error _ =>
                    positive := false
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
    (depth : Nat)
    (expr : Expr) : Result FieldShape := do
  let target := Expr.lift depth (recursiveTargetExpr root.spec)
  if expr = target then
    pure .direct
  else
    match expr with
    | .bvar _ => pure .none
    | .sort _ => pure .none
    | .const _ => pure .none
    | .letE _ _ _ _ =>
        .error s!"unexpected let-expression in positivity check: {repr expr}"
    | .lam _ _ _ =>
        .error s!"unexpected lambda in positivity check: {repr expr}"
    | .forallE name dom body =>
        if containsExprAt (recursiveTargetExpr root.spec) depth dom then
          .error s!"non-positive recursive occurrence in {repr expr}"
        else
          let bodyShape ← analyzeRecursiveShape env root (depth + 1) body
          match bodyShape with
          | .none => pure .none
          | _ => pure (.pi name dom bodyShape)
    | .app _ _ =>
        match decomposeInductiveApp env expr with
        | some (headName, info, args) =>
            if headName = root.spec.name then
              .error s!"recursive occurrence must be {repr target}"
            let mut found := false
            for pair in List.zip args info.positiveParams do
              let arg := pair.1
              let isPositive := pair.2
              let occurs := containsExprAt (recursiveTargetExpr root.spec) depth arg
              if occurs then
                if !isPositive then
                  .error s!"recursive occurrence appears in a non-positive argument of {headName}"
                let shape ← analyzeRecursiveShape env root depth arg
                if shapeHasIH shape then
                  found := true
            if found then
              let some lowered := expr.lower depth
                | .error s!"failed to lower nested target {repr expr}"
              pure (.nested lowered)
            else
              pure .none
        | none =>
            if containsExprAt (recursiveTargetExpr root.spec) depth expr then
              .error s!"non-positive recursive occurrence in {repr expr}"
            else
              pure .none

structure RecursorSplit where
  params : List Expr
  motives : List Expr
  minors : List Expr
  target : Expr

def familyMinorCount (family : RecursorFamily) : Nat :=
  family.targets.foldl (fun count target => count + target.ctors.length) 0

def splitFamilyRecursorArgs
    (family : RecursorFamily)
    (args : List Expr) : Option RecursorSplit :=
  let paramCount := family.params.length
  let motiveCount := family.targets.length
  let minorCount := familyMinorCount family
  if args.length != paramCount + motiveCount + minorCount + 1 then
    none
  else
    let params := args.take paramCount
    let rest := args.drop paramCount
    let motives := rest.take motiveCount
    let rest := rest.drop motiveCount
    let minors := rest.take minorCount
    match rest.drop minorCount with
    | [target] => some { params, motives, minors, target }
    | _ => none

def lookupFamilyTarget? (family : RecursorFamily) (expr : Expr) : Option FamilyTarget :=
  family.targets.find? fun target => target.typeExpr.alphaEq expr

def lookupFamilyTargetIndex? (family : RecursorFamily) (expr : Expr) : Option Nat :=
  let rec loop (index : Nat) : List FamilyTarget → Option Nat
    | [] => none
    | target :: rest =>
        if target.typeExpr.alphaEq expr then
          some index
        else
          loop (index + 1) rest
  loop 0 family.targets

def listGet? : List α → Nat → Option α
  | [], _ => none
  | value :: _, 0 => some value
  | _ :: rest, index + 1 => listGet? rest index

def familyMinorEntries (family : RecursorFamily) : List (FamilyTarget × FamilyCtor) :=
  family.targets.foldr
    (fun target rest => target.ctors.map (fun ctor => (target, ctor)) ++ rest)
    []

def lookupMinorExpr?
    (family : RecursorFamily)
    (minors : List Expr)
    (targetExpr : Expr)
    (ctorName : Name) : Option Expr := do
  let entries := familyMinorEntries family
  let index ← entries.findIdx? fun entry =>
    entry.1.typeExpr.alphaEq targetExpr && entry.2.name = ctorName
  listGet? minors index

def mkCtorApp
    (target : FamilyTarget)
    (ctor : FamilyCtor)
    (fieldVars : List Expr) : Expr :=
  Expr.mkApps (.const ctor.name) (target.typeExpr.getAppArgs ++ fieldVars)

def lookupTargetMotive?
    (family : RecursorFamily)
    (motives : List Expr)
    (targetExpr : Expr) : Option Expr := do
  let index ← lookupFamilyTargetIndex? family targetExpr
  listGet? motives index

def lookupTargetRecName?
    (family : RecursorFamily)
    (targetExpr : Expr) : Option Name := do
  let target ← lookupFamilyTarget? family targetExpr
  pure target.recName

partial def ihTypeExpr
    (family : RecursorFamily)
    (motives : List Expr)
    (liftAmount : Nat)
    (shape : FieldShape)
    (fieldExpr : Expr) : Result Expr := do
  match shape with
  | .none => .error "internal error: missing induction hypothesis"
  | .direct =>
      let some motive := listGet? motives 0
        | .error "internal error: missing root motive"
      pure (.app (Expr.lift liftAmount motive) fieldExpr)
  | .nested targetExpr =>
      let some motive := lookupTargetMotive? family motives targetExpr
        | .error s!"internal error: unknown nested target {repr targetExpr}"
      pure (.app (Expr.lift liftAmount motive) fieldExpr)
  | .pi name dom body => do
      let bodyField := .app (Expr.lift 1 fieldExpr) (.bvar 0)
      let bodyTy ← ihTypeExpr family motives (liftAmount + 1) body bodyField
      pure (.forallE name (Expr.lift liftAmount dom) bodyTy)

partial def ihTerm
    (family : RecursorFamily)
    (prefixArgs : List Expr)
    (shape : FieldShape)
    (fieldExpr : Expr) : Result Expr := do
  match shape with
  | .none => .error "internal error: missing induction hypothesis term"
  | .direct =>
      let some firstTarget := listGet? family.targets 0
        | .error "internal error: missing root target"
      let recName := firstTarget.recName
      pure (Expr.mkApps (.const recName) (prefixArgs ++ [fieldExpr]))
  | .nested targetExpr =>
      let some recName := lookupTargetRecName? family targetExpr
        | .error s!"internal error: unknown nested target {repr targetExpr}"
      pure (Expr.mkApps (.const recName) (prefixArgs ++ [fieldExpr]))
  | .pi name dom body => do
      let bodyField := .app (Expr.lift 1 fieldExpr) (.bvar 0)
      let bodyTerm ← ihTerm family prefixArgs body bodyField
      pure (.lam name dom bodyTerm)

def familyRecName (rootName : Name) (index : Nat) : Name :=
  if index = 0 then
    recursorName rootName
  else
    helperRecursorName rootName index

partial def buildRecursorFamily
    (env : Env)
    (root : InductiveInfo) : Result RecursorFamily := do
  let rootTarget := recursiveTargetExpr root.spec
  let rec loop
      (seen : List Expr)
      (queue : List Expr)
      (built : List FamilyTarget) : Result (List FamilyTarget) := do
    match queue with
    | [] => pure built
    | typeExpr :: rest =>
        let some (headName, info, args) := decomposeInductiveApp env typeExpr
          | .error s!"internal error: invalid family target {repr typeExpr}"
        let index := built.length
        let targetName := familyRecName root.spec.name index
        let ctors ←
          info.spec.ctors.mapM fun ctor => do
            let specialized :=
              ctor.fields.map fun field =>
                { field with type := Expr.instantiateMany args field.type }
            let fields ←
              specialized.mapM fun field => do
                let shape ← analyzeRecursiveShape env root 0 field.type
                pure { binder := field, shape }
            pure { name := ctor.name, fields }
        let target : FamilyTarget :=
          { recName := targetName, typeExpr, headName, ctors }
        let nested :=
          ctors.foldr
            (fun ctor rest =>
              ctor.fields.foldr
                (fun field inner => shapeNestedTargets field.shape ++ inner)
                rest)
            []
        let mut newSeen := seen
        let mut newQueue := rest
        for nestedTarget in nested do
          let already :=
            newSeen.any fun seenTarget => seenTarget.alphaEq nestedTarget
          if !already then
            newSeen := nestedTarget :: newSeen
            newQueue := newQueue ++ [nestedTarget]
        loop newSeen newQueue (built ++ [target])
  let targets ← loop [rootTarget] [rootTarget] []
  pure { rootName := root.spec.name, params := root.spec.params, targets }

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

partial def checkLevelDefEq (left right : Level) : Result Unit :=
  if Level.defEq left right then
    pure ()
  else
    .error s!"motive universes differ: {repr (Level.normalize left)} vs {repr (Level.normalize right)}"

partial def instantiateTargetExpr (params : List Expr) (target : FamilyTarget) : Expr :=
  Expr.instantiateMany params target.typeExpr

partial def familyCtorMinorType
    (family : RecursorFamily)
    (params : List Expr)
    (motives : List Expr)
    (target : FamilyTarget)
    (ctor : FamilyCtor) : Result Expr := do
  let some motive := lookupTargetMotive? family motives target.typeExpr
    | .error s!"internal error: missing motive for {repr target.typeExpr}"
  let targetExpr := instantiateTargetExpr params target
  let fieldBinders :=
    ctor.fields.map fun field =>
      { field.binder with type := Expr.instantiateMany params field.binder.type }
  let fieldVarsForIH := Expr.bvarArgs fieldBinders.length 0
  let mut ihBinders : List Binder := []
  let mut ihIndex := 0
  for pair in List.zip ctor.fields fieldVarsForIH do
    let field := pair.1
    let fieldVar := pair.2
    if shapeHasIH field.shape then
      let ihTy ← ihTypeExpr family motives 0 field.shape fieldVar
      ihBinders := ihBinders ++ [{ name := s!"ih{ihIndex}", type := ihTy }]
      ihIndex := ihIndex + 1
  let totalBinders := fieldBinders.length + ihBinders.length
  let liftedMotive := Expr.lift totalBinders motive
  let liftedTargetArgs := targetExpr.getAppArgs.map (Expr.lift totalBinders)
  let fieldVars := Expr.bvarArgs fieldBinders.length ihBinders.length
  let body :=
    .app liftedMotive (Expr.mkApps (.const ctor.name) (liftedTargetArgs ++ fieldVars))
  let withIhs := bindIndependentForall ihBinders body
  pure (bindIndependentForall fieldBinders withIhs)

partial def reduceRecursorApp
    (env : Env)
    (recName : Name)
    (args : List Expr) : Result (Option Expr) := do
  let some (targetIndex, family) := env.findRecursor? recName
    | .error s!"unknown recursor: {recName}"
  let some split := splitFamilyRecursorArgs family args
    | pure none
  let some targetInfo := listGet? family.targets targetIndex
    | .error s!"internal error: invalid recursor index for {recName}"
  let targetWhnf ← whnf env split.target
  let head := targetWhnf.getAppFn
  let ctorArgs := targetWhnf.getAppArgs
  let .const ctorName := head
    | pure none
  let some ctor := targetInfo.ctors.find? fun ctor => ctor.name = ctorName
    | pure none
  let targetExpr := instantiateTargetExpr split.params targetInfo
  if ctorArgs.length != targetExpr.getAppArgs.length + ctor.fields.length then
    pure none
  else
    let fieldArgs := ctorArgs.drop targetExpr.getAppArgs.length
    let prefixArgs := split.params ++ split.motives ++ split.minors
    let mut ihTerms : List Expr := []
    for pair in List.zip ctor.fields fieldArgs do
      let field := pair.1
      let fieldArg := pair.2
      if shapeHasIH field.shape then
        let ih ← ihTerm family prefixArgs field.shape fieldArg
        ihTerms := ihTerms ++ [ih]
    let some minor := lookupMinorExpr? family split.minors targetInfo.typeExpr ctor.name
      | .error s!"internal error: missing minor premise for {ctor.name}"
    pure (some (Expr.mkApps minor (fieldArgs ++ ihTerms)))

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
          | some (.recursor _ _ _) =>
              match ← reduceRecursorApp env name args with
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
    (recName : Name)
    (args : List Expr) : Result Expr := do
  let some (targetIndex, family) := env.findRecursor? recName
    | .error s!"unknown recursor: {recName}"
  let some split := splitFamilyRecursorArgs family args
    | .error s!"recursor {recName} expects a saturated application"
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
    | _, _ => .error s!"invalid parameter list for {family.rootName}"
  let _ ← checkParams [] family.params split.params
  let mut motiveLevels : List Level := []
  for pair in List.zip family.targets split.motives do
    let targetInfo := pair.1
    let motive := pair.2
    let motiveTy ← infer env ctx motive
    let motiveWhnf ← whnf env motiveTy
    let .forallE _ motiveDomain motiveBody := motiveWhnf
      | .error s!"motive for {recName} must be a dependent function"
    let expectedTarget := instantiateTargetExpr split.params targetInfo
    let _ ← checkDefEq env motiveDomain expectedTarget
    let level ← inferSort env ({ name := "_target", type := expectedTarget } :: ctx) motiveBody
    motiveLevels := motiveLevels ++ [level]
  match motiveLevels with
  | first :: rest =>
      for level in rest do
        let _ ← checkLevelDefEq first level
  | [] => pure ()
  let minorEntries := familyMinorEntries family
  for pair in List.zip minorEntries split.minors do
    let targetInfo := pair.1.1
    let ctor := pair.1.2
    let minorExpr := pair.2
    let expectedMinor ← familyCtorMinorType family split.params split.motives targetInfo ctor
    let actualMinor ← infer env ctx minorExpr
    let _ ← checkDefEq env actualMinor expectedMinor
  let some targetInfo := listGet? family.targets targetIndex
    | .error s!"internal error: invalid recursor index for {recName}"
  let actualTarget ← infer env ctx split.target
  let expectedTarget := instantiateTargetExpr split.params targetInfo
  let _ ← checkDefEq env actualTarget expectedTarget
  let some motive := listGet? split.motives targetIndex
    | .error s!"internal error: missing motive for {recName}"
  pure (.app motive split.target)

partial def inferApp (env : Env) (ctx : Context) (expr : Expr) : Result Expr := do
  let head := expr.getAppFn
  let args := expr.getAppArgs
  match head with
  | .const name =>
      match env.find? name with
      | some (.recursor _ _ _) => inferRecursorApp env ctx name args
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
  | .sort level => pure (.sort (.succ level))
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
  let tempEnv := .inductive spec.name provisionalInfo :: env
  let paramCtx := spec.params.reverse
  if !spec.ctors.isEmpty then
    let rec checkParamLevels (ctx : Context) : List Binder → Result Unit
      | [] => pure ()
      | binder :: rest => do
          let level ← inferBinderUniverse env ctx binder.type
          let _ ←
            checkLevelAtMost
              s!"parameter {binder.name}"
              level
              spec.level
          checkParamLevels (withBinder ctx binder) rest
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
  let infoEnv := .inductive spec.name info :: env
  let family ← buildRecursorFamily infoEnv info
  for target in family.targets.drop 1 do
    if seenNames.contains target.recName then
      .error s!"duplicate name in inductive declaration: {target.recName}"
    let _ ← checkFreshName env target.recName
    seenNames := target.recName :: seenNames
  let ctorInfos :=
    spec.ctors.map fun ctor =>
      .ctor ctor.name (constructorTypeExpr spec ctor) spec.name
  let recInfos :=
    (List.zip (List.range family.targets.length) family.targets).map fun pair =>
      .recursor pair.2.recName pair.1 family
  pure (recInfos.reverse ++ ctorInfos.reverse ++ (.inductive spec.name info :: env))

end LeanLean
