import MPC.Packages.Inductive.Basic

namespace MPC

partial def containsConst (target : Name) : Expr → Bool
  | .bvar _ => false
  | .sort _ => false
  | .const name _ => name == target
  | .lit _ => false
  | .app fn arg => containsConst target fn || containsConst target arg
  | .lam _ type body => containsConst target type || containsConst target body
  | .forallE _ type body => containsConst target type || containsConst target body
  | .letE _ type value body =>
      containsConst target type || containsConst target value || containsConst target body
  | .proj _ _ projectionTarget => containsConst target projectionTarget

partial def containsAnyConst (targets : List Name) : Expr → Bool
  | .bvar _ => false
  | .sort _ => false
  | .const name _ => targets.contains name
  | .lit _ => false
  | .app fn arg => containsAnyConst targets fn || containsAnyConst targets arg
  | .lam _ type body => containsAnyConst targets type || containsAnyConst targets body
  | .forallE _ type body => containsAnyConst targets type || containsAnyConst targets body
  | .letE _ type value body =>
      containsAnyConst targets type ||
        containsAnyConst targets value ||
        containsAnyConst targets body
  | .proj _ _ projectionTarget => containsAnyConst targets projectionTarget

def getAppHeadName? (expr : Expr) : Option Name :=
  match expr.getAppFnArgs.1 with
  | .const name _ => some name
  | _ => none

structure CovariantContainerInfo where
  positiveArgs : List Bool
  deriving BEq, Repr, Inhabited

def lean429CovariantContainerInfo? : Name → Option CovariantContainerInfo
  | "Array" => some { positiveArgs := [true] }
  | "List" => some { positiveArgs := [true] }
  | "Vec" => some { positiveArgs := [true, false] }
  | _ => none

def availableFixedCovariantContainer? (manifest : Manifest) (env : Env) (name : Name) :
    Option CovariantContainerInfo :=
  if !manifest.supportsLean429NestedContainers then
    none
  else
    match lean429CovariantContainerInfo? name, env.find? name with
    | some info, some { kind := .inductiveType .., .. } => some info
    | some info, some { kind := .indexedInductiveType .., .. } => some info
    | _, _ => none

partial def containsBVarAt (target : Nat) : Expr → Bool
  | .bvar index => index == target
  | .sort _ => false
  | .const _ _ => false
  | .lit _ => false
  | .app fn arg => containsBVarAt target fn || containsBVarAt target arg
  | .lam _ type body => containsBVarAt target type || containsBVarAt (target + 1) body
  | .forallE _ type body => containsBVarAt target type || containsBVarAt (target + 1) body
  | .letE _ type value body =>
      containsBVarAt target type || containsBVarAt target value || containsBVarAt (target + 1) body
  | .proj _ _ projectionTarget => containsBVarAt target projectionTarget

def listAllIdx (p : Nat → α → Bool) : Nat → List α → Bool
  | _, [] => true
  | index, value :: rest => p index value && listAllIdx p (index + 1) rest

def listGetD [Inhabited α] : List α → Nat → α
  | [], _ => default
  | value :: _, 0 => value
  | _ :: rest, index + 1 => listGetD rest index

def listTakeD [Inhabited α] (values : List α) (count : Nat) : List α :=
  (List.range count).map fun index => listGetD values index

def boolFlagsEqual (left right : List Bool) : Bool :=
  left.length == right.length &&
    (left.zip right).all fun pair => pair.1 == pair.2

def computeCovariantFlags (paramCount : Nat) (check : List Bool → Nat → Bool) : List Bool :=
  let rec loop : Nat → List Bool → List Bool
    | 0, flags => flags
    | fuel + 1, flags =>
        let next :=
          (List.range paramCount).map fun index =>
            listGetD flags index && check flags index
        if boolFlagsEqual flags next then
          flags
        else
          loop fuel next
  loop (paramCount + 1) (List.replicate paramCount true)

mutual

partial def bvarStrictlyPositive (manifest : Manifest) (env : Env) (selfName : Name)
    (selfPositive : List Bool) (target : Nat) (expr : Expr) : Bool :=
  match expr with
  | .bvar _ => true
  | .forallE _ domain body =>
      !containsBVarAt target domain &&
        bvarStrictlyPositive manifest env selfName selfPositive (target + 1) body
  | _ =>
      let (head, args) := expr.getAppFnArgs
      match head with
      | .const name _ =>
          if name == selfName then
            args.length == selfPositive.length &&
              listAllIdx (fun index arg =>
                if listGetD selfPositive index then
                  bvarStrictlyPositive manifest env selfName selfPositive target arg
                else
                  !containsBVarAt target arg)
                0
                args
          else
            match availableCovariantContainer? manifest env name with
            | some info =>
                args.length == info.positiveArgs.length &&
                  listAllIdx (fun index arg =>
                    if listGetD info.positiveArgs index then
                      bvarStrictlyPositive manifest env selfName selfPositive target arg
                    else
                      !containsBVarAt target arg)
                    0
                    args
            | none => !containsBVarAt target expr
      | _ => !containsBVarAt target expr

partial def simpleCovariantContainer? (manifest : Manifest) (env : Env)
    (spec : SimpleInductiveSpec) : Option CovariantContainerInfo :=
  if spec.params.isEmpty then
    none
  else
    let flags :=
      computeCovariantFlags spec.params.length fun selfFlags paramIndex =>
        spec.constructors.all fun ctor =>
          let fieldCount := ctor.fields.length
          let target := fieldCount + spec.params.length - 1 - paramIndex
          listAllIdx (fun fieldIndex field =>
            let type := fieldTypeUnderAllFields fieldCount fieldIndex field.type
            bvarStrictlyPositive manifest env spec.name selfFlags target type)
            0
            ctor.fields
    if flags.any id then some { positiveArgs := flags } else none

partial def indexedCovariantContainer? (manifest : Manifest) (env : Env)
    (spec : IndexedInductiveSpec) : Option CovariantContainerInfo :=
  if spec.params.isEmpty then
    none
  else
    let flags :=
      computeCovariantFlags spec.params.length fun selfParamFlags paramIndex =>
        let selfFlags := selfParamFlags ++ List.replicate spec.indices.length false
        spec.constructors.all fun ctor =>
          let fieldCount := ctor.fields.length
          let target := fieldCount + spec.params.length - 1 - paramIndex
          ctor.targetIndices.all (fun index => !containsBVarAt target index) &&
            listAllIdx (fun fieldIndex field =>
              let type := fieldTypeUnderAllFields fieldCount fieldIndex field.type
              bvarStrictlyPositive manifest env spec.name selfFlags target type)
              0
              ctor.fields
    if flags.any id then
      some { positiveArgs := flags ++ List.replicate spec.indices.length false }
    else
      none

partial def availableCovariantContainer? (manifest : Manifest) (env : Env) (name : Name) :
    Option CovariantContainerInfo :=
  match availableFixedCovariantContainer? manifest env name with
  | some info => some info
  | none =>
      if !manifest.supportsLean429NestedContainers then
        none
      else
        match env.find? name with
        | some { kind := .inductiveType spec, .. } =>
            simpleCovariantContainer? manifest env spec
        | some { kind := .indexedInductiveType spec, .. } =>
            indexedCovariantContainer? manifest env spec
        | _ => none

end

partial def simpleStrictlyPositive (manifest : Manifest) (env : Env) (target : Name)
    (expr : Expr) : Bool :=
  if getAppHeadName? expr == some target then
    true
  else
    let (head, args) := expr.getAppFnArgs
    match head with
    | .const name _ =>
        match availableCovariantContainer? manifest env name with
        | some info =>
            let rec argsStrictlyPositive : Nat → List Expr → Bool
              | _, [] => true
              | index, arg :: rest =>
                  let ok :=
                    if listGetD info.positiveArgs index then
                      simpleStrictlyPositive manifest env target arg
                    else
                      !containsConst target arg
                  ok && argsStrictlyPositive (index + 1) rest
            args.length == info.positiveArgs.length && argsStrictlyPositive 0 args
        | none =>
            match expr with
            | .forallE _ domain body =>
                !containsConst target domain && simpleStrictlyPositive manifest env target body
            | _ => !containsConst target expr
    | _ =>
        match expr with
        | .forallE _ domain body =>
            !containsConst target domain && simpleStrictlyPositive manifest env target body
        | _ => !containsConst target expr

partial def mutualStrictlyPositive (manifest : Manifest) (env : Env) (targets : List Name)
    (expr : Expr) : Bool :=
  match getAppHeadName? expr with
  | some name =>
      if targets.contains name then
        true
      else
        checkHead
  | none => checkHead
where
  checkHead : Bool :=
    let (head, args) := expr.getAppFnArgs
    match head with
    | .const name _ =>
        match availableCovariantContainer? manifest env name with
        | some info =>
            let rec argsStrictlyPositive : Nat → List Expr → Bool
              | _, [] => true
              | index, arg :: rest =>
                  let ok :=
                    if listGetD info.positiveArgs index then
                      mutualStrictlyPositive manifest env targets arg
                    else
                      !containsAnyConst targets arg
                  ok && argsStrictlyPositive (index + 1) rest
            args.length == info.positiveArgs.length && argsStrictlyPositive 0 args
        | none =>
            match expr with
            | .forallE _ domain body =>
                !containsAnyConst targets domain &&
                  mutualStrictlyPositive manifest env targets body
            | _ => !containsAnyConst targets expr
    | _ =>
        match expr with
        | .forallE _ domain body =>
            !containsAnyConst targets domain && mutualStrictlyPositive manifest env targets body
        | _ => !containsAnyConst targets expr

end MPC
