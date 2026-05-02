import LeanLean.Kernel

namespace LeanLean

def const0 (name : Name) : Expr :=
  .const name []

def recConst (name : Name) : Expr :=
  .const name [0]

def boolType : Expr :=
  const0 "Bool"

def natType : Expr :=
  const0 "Nat"

def listType (elem : Expr) : Expr :=
  Expr.mkApps (const0 "List") [elem]

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
        { name := "Nat.succ", fields := [{ name := "n", type := const0 "Nat" }] }
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
              { name := "tail", type := Expr.mkApps (const0 "List") [.bvar 0] }
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
          fields := [{ name := "x", type := Expr.mkApps (const0 "BadParam") [const0 "BadWrap"] }]
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
            [{ name := "children", type := Expr.mkApps (const0 "List") [const0 "NatListTree"] }]
        }
      ]
  }

def letTreeSpec : InductiveSpec :=
  {
    name := "LetTree"
    params := []
    level := 0
    ctors :=
      [
        { name := "LetTree.leaf", fields := [{ name := "n", type := natType }] },
        {
          name := "LetTree.node"
          fields :=
            [
              {
                name := "children"
                type := .letE "T" (.sort 0) (const0 "LetTree") (Expr.mkApps (const0 "List") [.bvar 0])
              }
            ]
        }
      ]
  }

def harmlessWrapSpec : InductiveSpec :=
  {
    name := "HarmlessWrap"
    params := [{ name := "α", type := .sort 0 }]
    level := 0
    ctors :=
      [
        {
          name := "HarmlessWrap.mk"
          fields := [{ name := "x", type := .letE "y" (.sort 0) (.bvar 0) natType }]
        }
      ]
  }

def nestThroughHarmlessWrapSpec : InductiveSpec :=
  {
    name := "NestThroughHarmlessWrap"
    params := []
    level := 0
    ctors :=
      [
        {
          name := "NestThroughHarmlessWrap.mk"
          fields :=
            [{ name := "x", type := Expr.mkApps (const0 "HarmlessWrap") [const0 "NestThroughHarmlessWrap"] }]
        }
      ]
  }

def harmlessBadParamSpec : InductiveSpec :=
  {
    name := "HarmlessBadParam"
    params := []
    level := 0
    ctors :=
      [
        {
          name := "HarmlessBadParam.mk"
          fields :=
            [
              {
                name := "x"
                type := Expr.mkApps (const0 "BadParam") [.letE "y" (.sort 0) (const0 "HarmlessBadParam") natType]
              }
            ]
        }
      ]
  }

def dupHelperSpec : InductiveSpec :=
  {
    name := "DupHelper"
    params := []
    level := 0
    ctors :=
      [
        {
          name := "DupHelper.mk"
          fields :=
            [
              { name := "a", type := Expr.mkApps (const0 "List") [const0 "DupHelper"] },
              {
                name := "b"
                type := Expr.mkApps (const0 "List") [.letE "T" (.sort 0) (const0 "DupHelper") (.bvar 0)]
              }
            ]
        }
      ]
  }

def wrapAtSpec : InductiveSpec :=
  {
    name := "WrapAt"
    params :=
      [
        { name := "n", type := natType },
        { name := "α", type := .sort 0 }
      ]
    level := 0
    ctors :=
      [
        {
          name := "WrapAt.mk"
          fields := [{ name := "x", type := .bvar 0 }]
        }
      ]
  }

def depNestSpec : InductiveSpec :=
  {
    name := "DepNest"
    params := []
    level := 0
    ctors :=
      [
        {
          name := "DepNest.mk"
          fields :=
            [
              {
                name := "f"
                type :=
                  .forallE
                    "n"
                    natType
                    (Expr.mkApps (const0 "WrapAt") [.bvar 0, const0 "DepNest"])
              }
            ]
        }
      ]
  }

def depNestPSpec : InductiveSpec :=
  {
    name := "DepNestP"
    params := [{ name := "β", type := .sort 0 }]
    level := 0
    ctors :=
      [
        {
          name := "DepNestP.mk"
          fields :=
            [
              {
                name := "f"
                type :=
                  .forallE
                    "n"
                    natType
                    (Expr.mkApps (const0 "WrapAt") [.bvar 0, Expr.mkApps (const0 "DepNestP") [.bvar 1]])
              }
            ]
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
  let env ← addInductive env letTreeSpec
  let one := Expr.mkApps (const0 "Nat.succ") [const0 "Nat.zero"]
  addDefinition env "one" natType one

def natSucc (value : Expr) : Expr :=
  Expr.mkApps (const0 "Nat.succ") [value]

def boolFalse : Expr :=
  const0 "Bool.false"

def boolTrue : Expr :=
  const0 "Bool.true"

def natZero : Expr :=
  const0 "Nat.zero"

def listNil (elem : Expr) : Expr :=
  Expr.mkApps (const0 "List.nil") [elem]

def listCons (elem head tail : Expr) : Expr :=
  Expr.mkApps (const0 "List.cons") [elem, head, tail]

def natToBoolMotive : Expr :=
  .lam "n" natType boolType

def natRecStepType : Expr :=
  .forallE "n" natType (.forallE "ih" boolType boolType)

def natRecPartial : Expr :=
  Expr.mkApps (recConst "Nat.rec") [natToBoolMotive, boolTrue]

def natRecMissingLevel : Expr :=
  Expr.mkApps
    (const0 "Nat.rec")
    [
      natToBoolMotive,
      boolTrue,
      .lam "n" natType (.lam "ih" boolType boolFalse),
      const0 "one"
    ]

def natRecExtraLevels : Expr :=
  Expr.mkApps
    (.const "Nat.rec" [0, 1])
    [
      natToBoolMotive,
      boolTrue,
      .lam "n" natType (.lam "ih" boolType boolFalse),
      const0 "one"
    ]

def natIsZeroOnOne : Expr :=
  Expr.mkApps
    (recConst "Nat.rec")
    [
      natToBoolMotive,
      boolTrue,
      .lam "n" natType (.lam "ih" boolType boolFalse),
      const0 "one"
    ]

def listRecParamMismatch : Expr :=
  Expr.mkApps
    (recConst "List.rec")
    [
      natType,
      .lam "xs" (listType natType) boolType,
      boolFalse,
      .lam "head" natType (.lam "tail" (listType natType) (.lam "ih" boolType boolTrue)),
      listNil boolType
    ]

def singletonTrue : Expr :=
  listCons boolType boolTrue (listNil boolType)

def natListTreeType : Expr :=
  const0 "NatListTree"

def leafZero : Expr :=
  Expr.mkApps (const0 "NatListTree.leaf") [natZero]

def leafList : Expr :=
  listCons natListTreeType leafZero (listNil natListTreeType)

def nodeLeafList : Expr :=
  Expr.mkApps (const0 "NatListTree.node") [leafList]

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
    (recConst "NatListTree.rec")
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
    (recConst "NatListTree.rec_1")
    [
      natListTreeMotive,
      natListMotive,
      natListTreeLeafCase,
      natListTreeNodeCase,
      natListTreeNilCase,
      natListTreeConsCase,
      leafList
    ]

def depNestType : Expr :=
  const0 "DepNest"

def wrapAtType (index elem : Expr) : Expr :=
  Expr.mkApps (const0 "WrapAt") [index, elem]

def wrapAtMk (index elem value : Expr) : Expr :=
  Expr.mkApps (const0 "WrapAt.mk") [index, elem, value]

def wrapAtZeroBoolType : Expr :=
  wrapAtType natZero boolType

def wrapAtTrueZero : Expr :=
  wrapAtMk natZero boolType boolTrue

def wrapAtBoolMotive : Expr :=
  .lam "t" wrapAtZeroBoolType natType

def wrapAtBoolCase : Expr :=
  .lam "x" boolType natZero

def wrapAtRecOnTrueZero : Expr :=
  Expr.mkApps
    (recConst "WrapAt.rec")
    [
      natZero,
      boolType,
      wrapAtBoolMotive,
      wrapAtBoolCase,
      wrapAtTrueZero
    ]

def depNestFieldType : Expr :=
  .forallE "n" natType (wrapAtType (.bvar 0) depNestType)

def depNestMotive : Expr :=
  .lam "t" depNestType boolType

def wrapAtDepNestMotive : Expr :=
  .lam "n" natType (.lam "t" (wrapAtType (.bvar 0) depNestType) boolType)

def depNestRootCase : Expr :=
  .lam "f" depNestFieldType (.lam "ih" (.forallE "n" natType boolType) boolFalse)

def depNestWrapCase : Expr :=
  .lam "n" natType (.lam "x" depNestType (.lam "ih" boolType boolTrue))

def depNestSeedName : Name :=
  "depNestSeed"

def depNestSeed : Expr :=
  const0 depNestSeedName

def wrapAtSeedZero : Expr :=
  wrapAtMk natZero depNestType depNestSeed

def depNestHelperRecOnSeed : Expr :=
  Expr.mkApps
    (recConst "DepNest.rec_1")
    [
      depNestMotive,
      wrapAtDepNestMotive,
      depNestRootCase,
      depNestWrapCase,
      natZero,
      wrapAtSeedZero
    ]

def depNestPType (param : Expr) : Expr :=
  Expr.mkApps (const0 "DepNestP") [param]

def depNestPBoolType : Expr :=
  depNestPType boolType

def depNestPFieldType : Expr :=
  .forallE "n" natType (wrapAtType (.bvar 0) depNestPBoolType)

def depNestPMotive : Expr :=
  .lam "t" depNestPBoolType boolType

def wrapAtDepNestPMotive : Expr :=
  .lam "n" natType (.lam "t" (wrapAtType (.bvar 0) depNestPBoolType) boolType)

def depNestPRootCase : Expr :=
  .lam "f" depNestPFieldType (.lam "ih" (.forallE "n" natType boolType) boolFalse)

def depNestPWrapCase : Expr :=
  .lam "n" natType (.lam "x" depNestPBoolType (.lam "ih" boolType boolTrue))

def depNestPSeedName : Name :=
  "depNestPSeed"

def depNestPSeed : Expr :=
  const0 depNestPSeedName

def wrapAtDepNestPSeedZero : Expr :=
  wrapAtMk natZero depNestPBoolType depNestPSeed

def depNestPHelperRecOnSeed : Expr :=
  Expr.mkApps
    (recConst "DepNestP.rec_1")
    [
      boolType,
      depNestPMotive,
      wrapAtDepNestPMotive,
      depNestPRootCase,
      depNestPWrapCase,
      natZero,
      wrapAtDepNestPSeedZero
    ]

def demoReport : Result (List String) := do
  let env ← sampleEnv
  let oneTy ← infer env [] (const0 "one")
  let _ ← checkDefEq env oneTy natType
  let _ ← infer env [] (recConst "Nat.rec")
  let natRecPartialTy ← infer env [] natRecPartial
  let _ ←
    checkDefEq
      env
      natRecPartialTy
      (.forallE "step" natRecStepType (.forallE "t" natType boolType))
  let _ ← infer env [] (recConst "LetTree.rec_1")
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
  let env ← addInductive env harmlessWrapSpec
  match env.findInductive? "HarmlessWrap" with
  | some info =>
      if info.positiveParams != [true] then
        .error s!"HarmlessWrap should record its parameter as positive, got {repr info.positiveParams}"
      else
        pure ()
  | none => .error "HarmlessWrap should be present in the environment"
  let env ← addInductive env nestThroughHarmlessWrapSpec
  let env ← addInductive env harmlessBadParamSpec
  let env ← addInductive env dupHelperSpec
  let _ ← infer env [] (recConst "DupHelper.rec_1")
  match env.findRecursor? "DupHelper.rec" with
  | some (_, family) =>
      if family.targets.length != 2 then
        .error s!"DupHelper should have exactly two family targets, got {family.targets.length}"
      else
        pure ()
  | none => .error "DupHelper.rec should be present in the environment"
  match env.find? "DupHelper.rec_2" with
  | some _ => .error "DupHelper should not generate a duplicate helper recursor"
  | none => pure ()
  let env ← addInductive env wrapAtSpec
  let wrapAtRecTy ← infer env [] wrapAtRecOnTrueZero
  let _ ← checkDefEq env wrapAtRecTy natType
  let wrapAtRecNf ← normalize env wrapAtRecOnTrueZero
  let _ ← checkDefEq env wrapAtRecNf natZero
  let env ← addInductive env depNestSpec
  let env ← addAxiom env depNestSeedName depNestType
  let _ ← infer env [] (recConst "DepNest.rec_1")
  match env.findRecursor? "DepNest.rec" with
  | some (_, family) =>
      if family.targets.length != 2 then
        .error s!"DepNest should have exactly two family targets, got {family.targets.length}"
      else
        match listGet? family.targets 1 with
        | some target =>
            if target.schema.locals.length != 1 then
              .error
                s!"DepNest helper target should carry one local binder, got {target.schema.locals.length}"
            else
              pure ()
        | none => .error "DepNest should expose a helper recursor target"
  | none => .error "DepNest.rec should be present in the environment"
  let depNestHelperTy ← infer env [] depNestHelperRecOnSeed
  let _ ← checkDefEq env depNestHelperTy boolType
  let depNestHelperNf ← normalize env depNestHelperRecOnSeed
  if depNestHelperNf != boolTrue then
    .error s!"unexpected normal form for DepNest.rec_1 example: {repr depNestHelperNf}"
  else
    pure ()
  let env ← addInductive env depNestPSpec
  let env ← addAxiom env depNestPSeedName depNestPBoolType
  let depNestPHelperTy ← infer env [] depNestPHelperRecOnSeed
  let _ ← checkDefEq env depNestPHelperTy boolType
  let depNestPHelperNf ← normalize env depNestPHelperRecOnSeed
  if depNestPHelperNf != boolTrue then
    .error s!"unexpected normal form for DepNestP.rec_1 example: {repr depNestPHelperNf}"
  else
    pure ()
  match normalize env natRecMissingLevel with
  | .ok _ => .error "Nat.rec without a universe argument should not normalize"
  | .error _ => pure ()
  match normalize env natRecExtraLevels with
  | .ok _ => .error "Nat.rec with extra universe arguments should not normalize"
  | .error _ => pure ()
  match infer env [] listRecParamMismatch with
  | .ok _ => .error "List.rec with mismatched target parameters should not type-check"
  | .error _ => pure ()
  match normalize env listRecParamMismatch with
  | .ok _ => .error "List.rec with mismatched target parameters should not normalize"
  | .error _ => pure ()
  match infer env [] (const0 "Nat.rec") with
  | .ok _ => .error "Nat.rec should require an explicit universe argument"
  | .error _ => pure ()
  match infer env [] (.const "Nat.rec" [.param "v"]) with
  | .ok _ => .error "Nat.rec should reject open universe arguments"
  | .error _ => pure ()
  match infer env [] (.sort (.param "u")) with
  | .ok _ => .error "Sort expressions should reject open universe levels"
  | .error _ => pure ()
  pure
    [
      "definition one : Nat checks",
      "recursor constants type-check and support partial application",
      "Nat.rec on one normalizes to Bool.false",
      "List Bool constructor application checks",
      "NatListTree.rec uses a nested helper recursor through List",
      "WrapAt.rec respects inductive parameters",
      "let-bound field types are normalized before positivity analysis",
      "helper-recursion targets are deduplicated by canonical form",
      "helper recursors support binder-dependent nested targets",
      "helper recursors support targets that depend on parameters and local binders",
      "constructorless inductives may sit below parameter universes",
      "constructor and field universes are rejected when they exceed the result universe",
      "recursor reduction rejects targets whose constructor parameters disagree",
      "non-positive nested uses of inductive parameters are rejected"
    ]

end LeanLean
