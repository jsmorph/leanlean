import MPC.Packages.Inductive.Reduction

namespace MPC

def natTypeExpr : Expr :=
  .const "Nat" []

def boolTypeExpr : Expr :=
  .const "Bool" []

def natBinaryNatPrimitiveType : Expr :=
  .forallE "a" natTypeExpr (.forallE "b" natTypeExpr natTypeExpr)

def natBinaryBoolPrimitiveType : Expr :=
  .forallE "a" natTypeExpr (.forallE "b" natTypeExpr boolTypeExpr)

def checkNatBinaryNatPrimitiveDeclaration (name : Name) (info : ConstantInfo) :
    Result Unit := do
  if !info.levelParams.isEmpty then
    fail s!"{name} primitive reduction requires no universe parameters"
  else if !info.type.alphaEq natBinaryNatPrimitiveType then
    fail s!"{name} primitive reduction requires the specified Nat -> Nat -> Nat type"
  else
    match info.kind, info.value? with
    | .definition, some _ => pure ()
    | _, _ => fail s!"{name} primitive reduction requires a transparent definition"

def checkNatBinaryBoolPrimitiveDeclaration (name : Name) (info : ConstantInfo) :
    Result Unit := do
  if !info.levelParams.isEmpty then
    fail s!"{name} primitive reduction requires no universe parameters"
  else if !info.type.alphaEq natBinaryBoolPrimitiveType then
    fail s!"{name} primitive reduction requires the specified Nat -> Nat -> Bool type"
  else
    match info.kind, info.value? with
    | .definition, some _ => pure ()
    | _, _ => fail s!"{name} primitive reduction requires a transparent definition"

def boolCtorExpr (env : Env) (value : Bool) : Result Expr := do
  let name := if value then "Bool.true" else "Bool.false"
  match env.find? name with
  | some { kind := .constructor inductiveName _ fieldCount, levelParams, type, .. } =>
      if inductiveName != "Bool" then
        fail s!"{name} primitive reduction requires a Bool constructor, got {inductiveName}"
      else if fieldCount != 0 then
        fail s!"{name} primitive reduction requires a nullary Bool constructor"
      else if !levelParams.isEmpty || !type.alphaEq boolTypeExpr then
        fail s!"{name} primitive reduction requires Bool constructor type"
      else
        pure (.const name [])
  | some _ => fail s!"{name} primitive reduction requires a Bool constructor"
  | none => fail s!"{name} primitive reduction requires a Bool constructor"

mutual

partial def natValue? (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (expr : Expr) : Result (Option Nat) := do
  match ← whnf manifest env levelParams expr with
  | .lit (.nat value) => pure (some value)
  | .const "Nat.zero" [] => pure (some 0)
  | .app (.const "Nat.succ" []) pred => do
      match ← natValue? manifest env levelParams pred with
      | some value => pure (some (value + 1))
      | none => pure none
  | _ => pure none

partial def reduceNatAdd? (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (info : ConstantInfo) (levels : List Level) (args : List Expr) :
    Result (Option Expr) := do
  if !manifest.supportsNatPrimitiveReductions || !levels.isEmpty || args.length != 2 then
    pure none
  else
    checkNatBinaryNatPrimitiveDeclaration "Nat.add" info
    let some left := listGet? args 0
      | pure none
    let some rightArg := listGet? args 1
      | pure none
    let right ← whnf manifest env levelParams rightArg
    match right with
    | .lit (.nat 0) => pure (some left)
    | .lit (.nat (pred + 1)) =>
        pure (some (.app (.const "Nat.succ" []) (Expr.mkApps (.const "Nat.add" []) [left, .lit (.nat pred)])))
    | _ =>
        match right.getAppFnArgs with
        | (.const "Nat.zero" [], []) => pure (some left)
        | (.const "Nat.succ" [], [pred]) =>
            pure (some (.app (.const "Nat.succ" []) (Expr.mkApps (.const "Nat.add" []) [left, pred])))
        | _ => pure none

partial def reduceNatBinaryNat? (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (name : Name) (info : ConstantInfo) (levels : List Level) (args : List Expr)
    (op : Nat → Nat → Nat) : Result (Option Expr) := do
  if !manifest.supportsNatPrimitiveReductions || !levels.isEmpty || args.length != 2 then
    pure none
  else
    checkNatBinaryNatPrimitiveDeclaration name info
    let some leftArg := listGet? args 0
      | pure none
    let some rightArg := listGet? args 1
      | pure none
    match
        ← natValue? manifest env levelParams leftArg,
        ← natValue? manifest env levelParams rightArg with
    | some left, some right => pure (some (.lit (.nat (op left right))))
    | _, _ => pure none

partial def reduceNatBinaryNatRightZero? (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (name : Name) (info : ConstantInfo) (levels : List Level) (args : List Expr)
    (op : Nat → Nat → Nat) (rightZero : Expr → Expr) : Result (Option Expr) := do
  if !manifest.supportsNatPrimitiveReductions || !levels.isEmpty || args.length != 2 then
    pure none
  else
    checkNatBinaryNatPrimitiveDeclaration name info
    let some leftArg := listGet? args 0
      | pure none
    let some rightArg := listGet? args 1
      | pure none
    match ← natValue? manifest env levelParams rightArg with
    | some 0 => pure (some (rightZero leftArg))
    | some right =>
        match ← natValue? manifest env levelParams leftArg with
        | some left => pure (some (.lit (.nat (op left right))))
        | none => pure none
    | none => pure none

partial def reduceNatBinaryBool? (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (name : Name) (info : ConstantInfo) (levels : List Level) (args : List Expr)
    (op : Nat → Nat → Bool) : Result (Option Expr) := do
  if !manifest.supportsNatPrimitiveReductions || !levels.isEmpty || args.length != 2 then
    pure none
  else
    checkNatBinaryBoolPrimitiveDeclaration name info
    let some leftArg := listGet? args 0
      | pure none
    let some rightArg := listGet? args 1
      | pure none
    match
        ← natValue? manifest env levelParams leftArg,
        ← natValue? manifest env levelParams rightArg with
    | some left, some right => pure (some (← boolCtorExpr env (op left right)))
    | _, _ => pure none

partial def reduceNatPrimitive? (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (name : Name) (info : ConstantInfo) (levels : List Level) (args : List Expr) :
    Result (Option Expr) := do
  match name with
  | "Nat.add" => reduceNatAdd? manifest env levelParams info levels args
  | "Nat.mul" =>
      reduceNatBinaryNatRightZero? manifest env levelParams name info levels args
        (fun left right => left * right)
        (fun _ => .lit (.nat 0))
  | "Nat.pow" =>
      reduceNatBinaryNatRightZero? manifest env levelParams name info levels args
        (fun left right => Nat.pow left right)
        (fun _ => .lit (.nat 1))
  | "Nat.sub" =>
      reduceNatBinaryNatRightZero? manifest env levelParams name info levels args
        (fun left right => left - right)
        (fun left => left)
  | "Nat.beq" => reduceNatBinaryBool? manifest env levelParams name info levels args (fun left right => left == right)
  | "Nat.ble" => reduceNatBinaryBool? manifest env levelParams name info levels args (fun left right => left <= right)
  | _ => pure none

partial def reduceProjection? (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (structureName : Name) (fieldIndex : Nat) (target : Expr) : Result (Option Expr) := do
  if !manifest.supportsProjections then
    pure none
  else
    let targetWhnf ← whnf manifest env levelParams target
    let (head, args) := targetWhnf.getAppFnArgs
    match head with
    | Expr.const ctorName _ =>
        match env.find? ctorName with
        | some { kind := .constructor inductiveName _ fieldCount, .. } =>
            if inductiveName != structureName || fieldIndex >= fieldCount then
              pure none
            else
              match env.find? structureName with
              | some { kind := .inductiveType spec, .. } =>
                  match spec.constructors with
                  | [_] =>
                      pure (listGet? (args.drop spec.params.length) fieldIndex)
                  | _ => pure none
              | _ => pure none
        | _ => pure none
    | _ => pure none

partial def reduceQuotLift? (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (_levels : List Level) (args : List Expr) : Result (Option Expr) := do
  if !manifest.supportsQuotients then
    pure none
  else
    let required := 6
    if args.length < required then
      pure none
    else
      let some typeArg := listGet? args 0
        | pure none
      let some relationArg := listGet? args 1
        | pure none
      let some fnArg := listGet? args 3
        | pure none
      let some quotientArg := listGet? args 5
        | pure none
      let trailing := args.drop required
      let quotientWhnf ← whnf manifest env levelParams quotientArg
      let (quotientHead, quotientArgs) := quotientWhnf.getAppFnArgs
      match quotientHead with
      | Expr.const mkName _ =>
          match env.find? mkName with
          | some { kind := .quotientMk, .. } =>
              let some mkTypeArg := listGet? quotientArgs 0
                | pure none
              let some mkRelationArg := listGet? quotientArgs 1
                | pure none
              let some valueArg := listGet? quotientArgs 2
                | pure none
              if mkTypeArg.alphaEq typeArg && mkRelationArg.alphaEq relationArg then
                pure (some (Expr.mkApps (.app fnArg valueArg) trailing))
              else
                pure none
          | _ => pure none
      | _ => pure none

partial def reduceEqRec? (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (args : List Expr) : Result (Option Expr) := do
  if !manifest.supportsEquality then
    pure none
  else
    let required := 6
    if args.length < required then
      pure none
    else
      let some typeArg := listGet? args 0
        | pure none
      let some aArg := listGet? args 1
        | pure none
      let some minorArg := listGet? args 3
        | pure none
      let some bArg := listGet? args 4
        | pure none
      let some proofArg := listGet? args 5
        | pure none
      let trailing := args.drop required
      let proofWhnf ← whnf manifest env levelParams proofArg
      let (proofHead, proofArgs) := proofWhnf.getAppFnArgs
      let reduceToMinorIfEndpointsMatch : Result (Option Expr) := do
        let aWhnf ← whnf manifest env levelParams aArg
        let bWhnf ← whnf manifest env levelParams bArg
        if aWhnf.alphaEq bWhnf then
          pure (some (Expr.mkApps minorArg trailing))
        else
          pure none
      match proofHead with
      | Expr.const reflName _ =>
          match env.find? reflName with
          | some { kind := .equalityRefl, .. } =>
              let some reflTypeArg := listGet? proofArgs 0
                | pure none
              let some reflValueArg := listGet? proofArgs 1
                | pure none
              if reflTypeArg == typeArg && reflValueArg == aArg && bArg == aArg then
                pure (some (Expr.mkApps minorArg trailing))
              else
                reduceToMinorIfEndpointsMatch
          | _ => reduceToMinorIfEndpointsMatch
      | _ => reduceToMinorIfEndpointsMatch

partial def whnf (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (expr : Expr) : Result Expr := do
  match expr with
  | .letE _ _ value body =>
      whnf manifest env levelParams (Expr.instantiate1 body value)
  | .proj structureName fieldIndex target => do
      match ← reduceProjection? manifest env levelParams structureName fieldIndex target with
      | some reduced => whnf manifest env levelParams reduced
      | none => pure (.proj structureName fieldIndex target)
  | .app fn arg =>
      let appExpr := Expr.app fn arg
      let (head, args) := Expr.getAppFnArgs appExpr
      let primitiveReduction? ←
        match head with
        | .const name levels =>
            match env.find? name with
            | some info => reduceNatPrimitive? manifest env levelParams name info levels args
            | none => pure none
        | _ => pure none
      match primitiveReduction? with
      | some reduced => whnf manifest env levelParams reduced
      | none =>
          let head ← whnf manifest env levelParams head
          match head with
          | Expr.const name levels =>
              match env.find? name with
              | some { kind := .recursor info, .. } =>
                  match ← reduceSimpleRecursor? whnf manifest env levelParams name info levels args with
                  | some reduced => whnf manifest env levelParams reduced
                  | none => pure (Expr.mkApps head args)
              | some { kind := .mutualRecursor info, .. } =>
                  match ← reduceMutualRecursor? whnf manifest env levelParams name info levels args with
                  | some reduced => whnf manifest env levelParams reduced
                  | none => pure (Expr.mkApps head args)
              | some { kind := .indexedRecursor info, .. } =>
                  match ← reduceIndexedRecursor? whnf manifest env levelParams name info levels args with
                  | some reduced => whnf manifest env levelParams reduced
                  | none => pure (Expr.mkApps head args)
              | some { kind := .nestedRecursor info, .. } =>
                  match ← reduceNestedRecursor? whnf manifest env levelParams name info levels args with
                  | some reduced => whnf manifest env levelParams reduced
                  | none => pure (Expr.mkApps head args)
              | some { kind := .quotientLift, .. } =>
                  match ← reduceQuotLift? manifest env levelParams levels args with
                  | some reduced => whnf manifest env levelParams reduced
                  | none => pure (Expr.mkApps head args)
              | some { kind := .equalityRec, .. } =>
                  match ← reduceEqRec? manifest env levelParams args with
                  | some reduced => whnf manifest env levelParams reduced
                  | none => pure (Expr.mkApps head args)
              | some { kind := .equalityNdRec, .. } =>
                  match ← reduceEqRec? manifest env levelParams args with
                  | some reduced => whnf manifest env levelParams reduced
                  | none => pure (Expr.mkApps head args)
              | _ => pure (Expr.mkApps head args)
          | .lam _ _ body =>
              match args with
              | first :: rest =>
                  whnf manifest env levelParams (Expr.mkApps (Expr.instantiate1 body first) rest)
              | [] => pure head
          | _ => pure (Expr.mkApps head args)
  | .const name levels =>
      match env.find? name with
      | some info =>
          match info.kind, info.instantiateValue? levels with
          | .definition, some value =>
              whnf manifest env levelParams value
          | _, _ => pure (.const name levels)
      | none => pure (.const name levels)
  | _ => pure expr

end

partial def normalize (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (expr : Expr) : Result Expr := do
  let expr ← whnf manifest env levelParams expr
  match expr with
  | .app fn arg => pure (.app (← normalize manifest env levelParams fn) (← normalize manifest env levelParams arg))
  | .lam name type body =>
      pure (.lam name (← normalize manifest env levelParams type) (← normalize manifest env levelParams body))
  | .forallE name type body =>
      pure (.forallE name (← normalize manifest env levelParams type) (← normalize manifest env levelParams body))
  | .letE name type value body =>
      pure
        (.letE name
          (← normalize manifest env levelParams type)
          (← normalize manifest env levelParams value)
          (← normalize manifest env levelParams body))
  | .proj structureName fieldIndex target =>
      pure (.proj structureName fieldIndex (← normalize manifest env levelParams target))
  | _ => pure expr

end MPC
