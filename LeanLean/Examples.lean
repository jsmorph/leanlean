import LeanLean.Kernel

namespace LeanLean

def boolType : Expr :=
  .const "Bool"

def natType : Expr :=
  .const "Nat"

def listType (elem : Expr) : Expr :=
  Expr.mkApps (.const "List") [elem]

def boolSpec : InductiveSpec :=
  {
    name := "Bool"
    params := []
    level := 0
    ctors :=
      [
        { name := "Bool.false", fields := [] },
        { name := "Bool.true", fields := [] }
      ]
  }

def natSpec : InductiveSpec :=
  {
    name := "Nat"
    params := []
    level := 0
    ctors :=
      [
        { name := "Nat.zero", fields := [] },
        { name := "Nat.succ", fields := [{ name := "n", type := .const "Nat" }] }
      ]
  }

def listSpec : InductiveSpec :=
  {
    name := "List"
    params := [{ name := "α", type := .sort 0 }]
    level := 0
    ctors :=
      [
        { name := "List.nil", fields := [] },
        {
          name := "List.cons"
          fields :=
            [
              { name := "head", type := .bvar 0 },
              { name := "tail", type := Expr.mkApps (.const "List") [.bvar 0] }
            ]
        }
      ]
  }

def sampleEnv : Result Env := do
  let env ← addInductive [] boolSpec
  let env ← addInductive env natSpec
  let env ← addInductive env listSpec
  let one := Expr.mkApps (.const "Nat.succ") [.const "Nat.zero"]
  addDefinition env "one" natType one

def natSucc (value : Expr) : Expr :=
  Expr.mkApps (.const "Nat.succ") [value]

def boolFalse : Expr :=
  .const "Bool.false"

def boolTrue : Expr :=
  .const "Bool.true"

def natZero : Expr :=
  .const "Nat.zero"

def listNil (elem : Expr) : Expr :=
  Expr.mkApps (.const "List.nil") [elem]

def listCons (elem head tail : Expr) : Expr :=
  Expr.mkApps (.const "List.cons") [elem, head, tail]

def natToBoolMotive : Expr :=
  .lam "n" natType boolType

def natIsZeroOnOne : Expr :=
  Expr.mkApps
    (.const "Nat.rec")
    [
      natToBoolMotive,
      boolTrue,
      .lam "n" natType (.lam "ih" boolType boolFalse),
      .const "one"
    ]

def singletonTrue : Expr :=
  listCons boolType boolTrue (listNil boolType)

def demoReport : Result (List String) := do
  let env ← sampleEnv
  let oneTy ← infer env [] (.const "one")
  let _ ← checkDefEq env oneTy natType
  let natRecTy ← infer env [] natIsZeroOnOne
  let _ ← checkDefEq env natRecTy boolType
  let natRecNf ← normalize env natIsZeroOnOne
  if natRecNf != boolFalse then
    .error s!"unexpected normal form for Nat.rec example: {repr natRecNf}"
  else
    pure ()
  let singletonTy ← infer env [] singletonTrue
  let _ ← checkDefEq env singletonTy (listType boolType)
  pure
    [
      "definition one : Nat checks",
      "Nat.rec on one normalizes to Bool.false",
      "List Bool constructor application checks"
    ]

end LeanLean
