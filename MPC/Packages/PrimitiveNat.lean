import MPC.Env

namespace MPC.Packages.PrimitiveNat

open MPC

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

-- Avoid an exported sparse matcher with a large `Nat.hasNotBit` catch-all proof.
set_option backward.match.sparseCases false in
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

partial def natValue? (whnfFn : Manifest → Env → LevelContext → Expr → Result Expr)
    (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (expr : Expr) : Result (Option Nat) := do
  match ← whnfFn manifest env levelParams expr with
  | .lit (.nat value) => pure (some value)
  | .const "Nat.zero" [] => pure (some 0)
  | .app (.const "Nat.succ" []) pred => do
      match ← natValue? whnfFn manifest env levelParams pred with
      | some value => pure (some (value + 1))
      | none => pure none
  | _ => pure none

partial def reduceNatAdd? (whnfFn : Manifest → Env → LevelContext → Expr → Result Expr)
    (manifest : Manifest) (env : Env) (levelParams : LevelContext)
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
    let right ← whnfFn manifest env levelParams rightArg
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

partial def reduceNatBinaryNat? (whnfFn : Manifest → Env → LevelContext → Expr → Result Expr)
    (manifest : Manifest) (env : Env) (levelParams : LevelContext)
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
        ← natValue? whnfFn manifest env levelParams leftArg,
        ← natValue? whnfFn manifest env levelParams rightArg with
    | some left, some right => pure (some (.lit (.nat (op left right))))
    | _, _ => pure none

partial def reduceNatBinaryNatRightZero?
    (whnfFn : Manifest → Env → LevelContext → Expr → Result Expr)
    (manifest : Manifest) (env : Env) (levelParams : LevelContext)
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
    match ← natValue? whnfFn manifest env levelParams rightArg with
    | some 0 => pure (some (rightZero leftArg))
    | some right =>
        match ← natValue? whnfFn manifest env levelParams leftArg with
        | some left => pure (some (.lit (.nat (op left right))))
        | none => pure none
    | none => pure none

partial def reduceNatBinaryBool? (whnfFn : Manifest → Env → LevelContext → Expr → Result Expr)
    (manifest : Manifest) (env : Env) (levelParams : LevelContext)
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
        ← natValue? whnfFn manifest env levelParams leftArg,
        ← natValue? whnfFn manifest env levelParams rightArg with
    | some left, some right => pure (some (← boolCtorExpr env (op left right)))
    | _, _ => pure none

partial def reduce? (whnfFn : Manifest → Env → LevelContext → Expr → Result Expr)
    (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (name : Name) (info : ConstantInfo) (levels : List Level) (args : List Expr) :
    Result (Option Expr) := do
  match name with
  | "Nat.add" => reduceNatAdd? whnfFn manifest env levelParams info levels args
  | "Nat.mul" =>
      reduceNatBinaryNatRightZero? whnfFn manifest env levelParams name info levels args
        (fun left right => left * right)
        (fun _ => .lit (.nat 0))
  | "Nat.pow" =>
      reduceNatBinaryNatRightZero? whnfFn manifest env levelParams name info levels args
        (fun left right => Nat.pow left right)
        (fun _ => .lit (.nat 1))
  | "Nat.sub" =>
      reduceNatBinaryNatRightZero? whnfFn manifest env levelParams name info levels args
        (fun left right => left - right)
        (fun left => left)
  | "Nat.beq" => reduceNatBinaryBool? whnfFn manifest env levelParams name info levels args (fun left right => left == right)
  | "Nat.ble" => reduceNatBinaryBool? whnfFn manifest env levelParams name info levels args (fun left right => left <= right)
  | _ => pure none

end

end MPC.Packages.PrimitiveNat
