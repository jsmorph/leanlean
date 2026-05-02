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

def sortBoxSpec : InductiveSpec :=
  {
    name := "SortBox"
    params := []
    level := 1
    ctors :=
      [
        { name := "SortBox.mk", fields := [{ name := "α", type := .sort 0 }] }
      ]
  }

def spuriousSpec : InductiveSpec :=
  {
    name := "Spurious"
    params := [{ name := "α", type := .sort 3 }]
    level := 0
    ctors := []
  }

def badSpuriousSpec : InductiveSpec :=
  {
    name := "BadSpurious"
    params := [{ name := "α", type := .sort 3 }]
    level := 0
    ctors :=
      [
        { name := "BadSpurious.mk", fields := [{ name := "x", type := .bvar 0 }] }
      ]
  }

def lowSortBoxSpec : InductiveSpec :=
  {
    name := "LowSortBox"
    params := []
    level := 0
    ctors :=
      [
        { name := "LowSortBox.mk", fields := [{ name := "α", type := .sort 0 }] }
      ]
  }

def badParamSpec : InductiveSpec :=
  {
    name := "BadParam"
    params := [{ name := "α", type := .sort 0 }]
    level := 0
    ctors :=
      [
        {
          name := "BadParam.mk"
          fields := [{ name := "f", type := .forallE "x" (.bvar 0) natType }]
        }
      ]
  }

def badWrapSpec : InductiveSpec :=
  {
    name := "BadWrap"
    params := []
    level := 0
    ctors :=
      [
        {
          name := "BadWrap.mk"
          fields := [{ name := "x", type := Expr.mkApps (.const "BadParam") [.const "BadWrap"] }]
        }
      ]
  }

def natListTreeSpec : InductiveSpec :=
  {
    name := "NatListTree"
    params := []
    level := 0
    ctors :=
      [
        { name := "NatListTree.leaf", fields := [{ name := "n", type := natType }] },
        {
          name := "NatListTree.node"
          fields :=
            [{ name := "children", type := Expr.mkApps (.const "List") [.const "NatListTree"] }]
        }
      ]
  }

def sampleEnv : Result Env := do
  let env ← addInductive [] boolSpec
  let env ← addInductive env natSpec
  let env ← addInductive env listSpec
  let env ← addInductive env sortBoxSpec
  let env ← addInductive env spuriousSpec
  let env ← addInductive env badParamSpec
  let env ← addInductive env natListTreeSpec
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

def natListTreeType : Expr :=
  .const "NatListTree"

def leafZero : Expr :=
  Expr.mkApps (.const "NatListTree.leaf") [natZero]

def leafList : Expr :=
  listCons natListTreeType leafZero (listNil natListTreeType)

def nodeLeafList : Expr :=
  Expr.mkApps (.const "NatListTree.node") [leafList]

def natListTreeMotive : Expr :=
  .lam "t" natListTreeType natType

def natListMotive : Expr :=
  .lam "ts" (listType natListTreeType) natType

def natListTreeLeafCase : Expr :=
  .lam "n" natType (natSucc natZero)

def natListTreeNodeCase : Expr :=
  .lam "ts" (listType natListTreeType) (.lam "ih" natType (.bvar 0))

def natListTreeNilCase : Expr :=
  natZero

def natListTreeConsCase : Expr :=
  .lam
    "head"
    natListTreeType
    (.lam
      "tail"
      (listType natListTreeType)
      (.lam "ihHead" natType (.lam "ihTail" natType (natSucc (.bvar 0)))))

def natListTreeRecOnNode : Expr :=
  Expr.mkApps
    (.const "NatListTree.rec")
    [
      natListTreeMotive,
      natListMotive,
      natListTreeLeafCase,
      natListTreeNodeCase,
      natListTreeNilCase,
      natListTreeConsCase,
      nodeLeafList
    ]

def natListTreeRecOnList : Expr :=
  Expr.mkApps
    (.const "NatListTree.rec_1")
    [
      natListTreeMotive,
      natListMotive,
      natListTreeLeafCase,
      natListTreeNodeCase,
      natListTreeNilCase,
      natListTreeConsCase,
      leafList
    ]

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
  let treeRecTy ← infer env [] natListTreeRecOnNode
  let _ ← checkDefEq env treeRecTy natType
  let treeRecNf ← normalize env natListTreeRecOnNode
  let _ ← checkDefEq env treeRecNf (natSucc natZero)
  let listRecTy ← infer env [] natListTreeRecOnList
  let _ ← checkDefEq env listRecTy natType
  let listRecNf ← normalize env natListTreeRecOnList
  let _ ← checkDefEq env listRecNf (natSucc natZero)
  match addInductive env badSpuriousSpec with
  | .ok _ => .error "BadSpurious should fail the universe check"
  | .error _ => pure ()
  match addInductive env lowSortBoxSpec with
  | .ok _ => .error "LowSortBox should fail the universe check"
  | .error _ => pure ()
  match addInductive env badWrapSpec with
  | .ok _ => .error "BadWrap should fail the positivity check"
  | .error _ => pure ()
  pure
    [
      "definition one : Nat checks",
      "Nat.rec on one normalizes to Bool.false",
      "List Bool constructor application checks",
      "NatListTree.rec uses a nested helper recursor through List",
      "constructorless inductives may sit below parameter universes",
      "constructor and field universes are rejected when they exceed the result universe",
      "non-positive nested uses of inductive parameters are rejected"
    ]

end LeanLean
