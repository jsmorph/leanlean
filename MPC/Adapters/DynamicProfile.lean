import Lean
import MPC.Check
import MPC.Replay
import MPC.Packages.Inductive.Admission
import MPC.Packages.Inductive.Reduction
import MPC.Packages.PrimitiveNat
import MPC.Packages.Projection
import Std.Data.HashMap

namespace MPC.Adapters.DynamicProfile

structure RepeatEntry where
  count : Nat := 0
  successCount : Nat := 0
  failureCount : Nat := 0
  repeatSuccessCount : Nat := 0
  repeatFailureCount : Nat := 0
  firstStep : Nat := 0
  lastStep : Nat := 0
  summary : String := ""
  sample : String := ""

structure Stats where
  steps : Nat := 0
  inferCalls : Nat := 0
  inferSortCalls : Nat := 0
  checkCalls : Nat := 0
  defEqCalls : Nat := 0
  defEqAlphaEqHits : Nat := 0
  structuralDefEqCalls : Nat := 0
  structuralWhnfAlphaEqHits : Nat := 0
  whnfCalls : Nat := 0
  whnfAlphaEqCalls : Nat := 0
  proofIrrelevanceCalls : Nat := 0
  functionEtaCalls : Nat := 0
  structureEtaCalls : Nat := 0
  singletonInductiveCalls : Nat := 0
  reduceEqRecByEndpointCalls : Nat := 0
  zetaReductions : Nat := 0
  betaReductions : Nat := 0
  definitionUnfolds : Nat := 0
  primitiveReductionAttempts : Nat := 0
  primitiveReductionSuccesses : Nat := 0
  projectionReductionAttempts : Nat := 0
  projectionReductionSuccesses : Nat := 0
  recursorReductionAttempts : Nat := 0
  recursorReductionSuccesses : Nat := 0
  quotientReductionAttempts : Nat := 0
  quotientReductionSuccesses : Nat := 0
  equalityRecReductionAttempts : Nat := 0
  equalityRecReductionSuccesses : Nat := 0
  whnfCacheHits : Nat := 0
  whnfCacheMisses : Nat := 0
  whnfCacheEntries : Nat := 0
  defEqCacheHits : Nat := 0
  defEqCacheMisses : Nat := 0
  defEqCacheEntries : Nat := 0
  defEqSuccessCacheHits : Nat := 0
  defEqSuccessCacheMisses : Nat := 0
  defEqSuccessCacheEntries : Nat := 0
  defEqSuccessCacheDropped : Nat := 0
  constructorProofFieldSkips : Nat := 0
  defEqRepeatObservations : Nat := 0
  defEqRepeatHits : Nat := 0
  defEqRepeatDropped : Nat := 0
  defEqRepeatSuccesses : Nat := 0
  defEqRepeatFailures : Nat := 0
  defEqRepeatHitSuccesses : Nat := 0
  defEqRepeatHitFailures : Nat := 0
  whnfRepeatObservations : Nat := 0
  whnfRepeatHits : Nat := 0
  whnfRepeatDropped : Nat := 0
  unfoldNames : Std.HashMap String Nat := {}
  defEqHeadPairs : Std.HashMap String Nat := {}
  defEqShapePairs : Std.HashMap String Nat := {}
  defEqContextDepths : Std.HashMap String Nat := {}
  structuralHeadPairs : Std.HashMap String Nat := {}
  defEqRepeats : Std.HashMap String RepeatEntry := {}
  whnfRepeats : Std.HashMap String RepeatEntry := {}
  structuralProjectionSamples : List (String × String) := []
  structuralLambdaSamples : List (String × String) := []

structure WhnfKey where
  levelParams : LevelContext
  expr : Expr
  deriving BEq, Hashable

structure DefEqKey where
  levelParams : LevelContext
  ctx : Context
  left : Expr
  right : Expr
  deriving BEq, Hashable

structure Profiler where
  budget : Nat
  ref : IO.Ref Stats
  markRef : IO.Ref String
  whnfCacheRef : IO.Ref (Std.HashMap WhnfKey Expr)
  defEqCacheRef : IO.Ref (Std.HashMap DefEqKey Unit)
  defEqSuccessCacheRef : IO.Ref (Std.HashMap DefEqKey Unit)
  useMemo : Bool := false
  useRepeatDiag : Bool := false
  useDefEqSuccessCache : Bool := false
  traceEvery : Nat := 1000

abbrev M := ExceptT Error IO

def fail {α : Type} (message : String) : M α :=
  throw { message }

def trace (message : String) : M Unit :=
  liftM (IO.eprintln message)

def Profiler.mark (profiler : Profiler) (message : String) : M Unit :=
  liftM (profiler.markRef.set message : IO Unit)

def liftResult {α : Type} : Result α → M α
  | .ok value => pure value
  | .error err => throw err

def capture {α : Type} (action : M α) : M (Except Error α) := do
  let result ← liftM action.run
  pure result

def jsonNat (value : Nat) : Lean.Json :=
  Lean.Json.num (Lean.JsonNumber.fromNat value)

def incrementString (map : Std.HashMap String Nat) (key : String) :
    Std.HashMap String Nat :=
  let value :=
    match map.get? key with
    | some value => value + 1
    | none => 1
  map.insert key value

def insertCountSorted (entry : String × Nat) : List (String × Nat) → List (String × Nat)
  | [] => [entry]
  | head :: rest =>
      if entry.2 > head.2 then
        entry :: head :: rest
      else
        head :: insertCountSorted entry rest

def topCounts (map : Std.HashMap String Nat) (limit : Nat) : List (String × Nat) :=
  (map.toList.foldl (fun entries entry => insertCountSorted entry entries) []).take limit

def countJson (entry : String × Nat) : Lean.Json :=
  Lean.Json.mkObj [
    ("name", Lean.Json.str entry.1),
    ("count", jsonNat entry.2)
  ]

def countsJson (map : Std.HashMap String Nat) (limit : Nat) : Lean.Json :=
  Lean.Json.arr ((topCounts map limit).map countJson).toArray

def stringPairJson (entry : String × String) : Lean.Json :=
  Lean.Json.mkObj [
    ("left", Lean.Json.str entry.1),
    ("right", Lean.Json.str entry.2)
  ]

def stringPairsJson (entries : List (String × String)) : Lean.Json :=
  Lean.Json.arr (entries.map stringPairJson).toArray

def insertRepeatSorted (entry : String × RepeatEntry) :
    List (String × RepeatEntry) → List (String × RepeatEntry)
  | [] => [entry]
  | head :: rest =>
      if entry.2.count > head.2.count then
        entry :: head :: rest
      else
        head :: insertRepeatSorted entry rest

def topRepeats (map : Std.HashMap String RepeatEntry) (limit : Nat) :
    List (String × RepeatEntry) :=
  (map.toList.foldl
    (fun entries entry =>
      if entry.2.count > 1 then
        insertRepeatSorted entry entries
      else
        entries)
    []).take limit

def repeatEntryJson (entry : String × RepeatEntry) : Lean.Json :=
  Lean.Json.mkObj [
    ("fingerprint", Lean.Json.str entry.1),
    ("count", jsonNat entry.2.count),
    ("success_count", jsonNat entry.2.successCount),
    ("failure_count", jsonNat entry.2.failureCount),
    ("repeat_success_count", jsonNat entry.2.repeatSuccessCount),
    ("repeat_failure_count", jsonNat entry.2.repeatFailureCount),
    ("first_step", jsonNat entry.2.firstStep),
    ("last_step", jsonNat entry.2.lastStep),
    ("summary", Lean.Json.str entry.2.summary),
    ("sample", Lean.Json.str entry.2.sample)
  ]

def repeatsJson (map : Std.HashMap String RepeatEntry) (limit : Nat) : Lean.Json :=
  Lean.Json.arr ((topRepeats map limit).map repeatEntryJson).toArray

def whnfCacheExprLimit : Nat :=
  128

def defEqCacheExprLimit : Nat :=
  32

def repeatMapLimit : Nat :=
  200000

def repeatTopLimit : Nat :=
  30

def defEqSuccessCacheLimit : Nat :=
  200000

def hashText {α : Type} [Hashable α] (value : α) : String :=
  toString (hash value)

partial def exprCacheSizeCapped (cap : Nat) : Expr → Nat
  | .bvar _
  | .sort _
  | .const ..
  | .lit _ => 1
  | .app fn arg =>
      if cap == 0 then
        1
      else
        let left := exprCacheSizeCapped (cap - 1) fn
        if left >= cap then
          cap
        else
          let right := exprCacheSizeCapped (cap - 1 - left) arg
          Nat.min cap (1 + left + right)
  | .lam _ type body
  | .forallE _ type body =>
      if cap == 0 then
        1
      else
        let typeSize := exprCacheSizeCapped (cap - 1) type
        if typeSize >= cap then
          cap
        else
          let bodySize := exprCacheSizeCapped (cap - 1 - typeSize) body
          Nat.min cap (1 + typeSize + bodySize)
  | .letE _ type value body =>
      if cap == 0 then
        1
      else
        let typeSize := exprCacheSizeCapped (cap - 1) type
        if typeSize >= cap then
          cap
        else
          let valueSize := exprCacheSizeCapped (cap - 1 - typeSize) value
          if typeSize + valueSize >= cap then
            cap
          else
            let bodySize := exprCacheSizeCapped (cap - 1 - typeSize - valueSize) body
            Nat.min cap (1 + typeSize + valueSize + bodySize)
  | .proj _ _ target =>
      if cap == 0 then
        1
      else
        Nat.min cap (1 + exprCacheSizeCapped (cap - 1) target)

def exprCacheable (limit : Nat) (expr : Expr) : Bool :=
  exprCacheSizeCapped (limit + 1) expr <= limit

def exprHeadLabel (expr : Expr) : String :=
  let (head, _) := expr.getAppFnArgs
  match head with
  | .bvar _ => "bvar"
  | .sort _ => "sort"
  | .const name _ => name
  | .lit _ => "lit"
  | .app _ _ => "app"
  | .lam .. => "lam"
  | .forallE .. => "forall"
  | .letE .. => "let"
  | .proj structureName fieldIndex _ => s!"proj {structureName}.{fieldIndex}"

def exprShapeLabel (expr : Expr) : String :=
  let (_, args) := expr.getAppFnArgs
  s!"{exprHeadLabel expr}/{args.length}/{exprCacheSizeCapped 65 expr}"

def exprFingerprintLabel (expr : Expr) : String :=
  s!"{exprHeadLabel expr}/{exprCacheSizeCapped 4097 expr}/{hashText expr}"

partial def exprShort : Nat → Expr → String
  | 0, expr => exprShapeLabel expr
  | fuel + 1, expr =>
      match expr with
      | .bvar index => s!"bvar {index}"
      | .sort level => s!"sort {repr level}"
      | .const name levels => s!"const {name}.{levels.length}"
      | .lit (.nat value) => s!"nat {value}"
      | .lit (.str value) => s!"str {value}"
      | .app .. =>
          let (head, args) := expr.getAppFnArgs
          let argText := String.intercalate ", " ((args.take 3).map (exprShort fuel))
          let suffix := if args.length > 3 then ", ..." else ""
          s!"app {exprHeadLabel head}/{args.length}({argText}{suffix})"
      | .lam name type body =>
          s!"lam {name} : {exprShort fuel type} => {exprShort fuel body}"
      | .forallE name type body =>
          s!"forall {name} : {exprShort fuel type} => {exprShort fuel body}"
      | .letE name type value body =>
          s!"let {name} : {exprShort fuel type} := {exprShort fuel value}; {exprShort fuel body}"
      | .proj structureName fieldIndex target =>
          s!"proj {structureName}.{fieldIndex}({exprShort fuel target})"

def Profiler.step (profiler : Profiler) (update : Stats → Stats) : M Unit := do
  let stats ← profiler.ref.get
  if stats.steps >= profiler.budget then
    fail s!"dynamic profile budget exhausted after {stats.steps} steps"
  else
    let nextStats := update { stats with steps := stats.steps + 1 }
    profiler.ref.set nextStats
    if profiler.traceEvery > 0 && nextStats.steps % profiler.traceEvery == 0 then
      let mark ← profiler.markRef.get
      trace s!"profile-step\t{nextStats.steps}\tmark={mark}\tinfer={nextStats.inferCalls}\tcheck={nextStats.checkCalls}\tdefeq={nextStats.defEqCalls}\twhnf={nextStats.whnfCalls}\twhnfAlphaEq={nextStats.whnfAlphaEqCalls}"

structure RepeatUpdate where
  map : Std.HashMap String RepeatEntry
  hit : Bool := false
  dropped : Bool := false

structure DefEqRepeatObservation where
  fingerprint : String
  hit : Bool := false

def updateRepeatMap (map : Std.HashMap String RepeatEntry) (step : Nat)
    (fingerprint summary sample : String) : RepeatUpdate :=
  match map.get? fingerprint with
  | some entry =>
      {
        map := map.insert fingerprint
          { entry with count := entry.count + 1, lastStep := step }
        hit := true
      }
  | none =>
      if map.size < repeatMapLimit then
        {
          map := map.insert fingerprint
            { count := 1, firstStep := step, lastStep := step, summary, sample }
        }
      else
        { map, dropped := true }

def defEqRepeatFingerprint (levelParams : LevelContext) (ctx : Context)
    (left right : Expr) : String :=
  s!"lp={hashText levelParams};ctx={ctx.length}:{hashText ctx};left={exprFingerprintLabel left};right={exprFingerprintLabel right}"

def defEqRepeatSummary (ctx : Context) (left right : Expr) : String :=
  s!"ctx={ctx.length}; {exprShapeLabel left} | {exprShapeLabel right}"

def whnfRepeatFingerprint (levelParams : LevelContext) (expr : Expr) : String :=
  s!"lp={hashText levelParams};expr={exprFingerprintLabel expr}"

def whnfRepeatSummary (expr : Expr) : String :=
  exprShapeLabel expr

def Profiler.noteDefEqRepeat (profiler : Profiler) (step : Nat)
    (levelParams : LevelContext) (ctx : Context) (left right : Expr) :
    M (Option DefEqRepeatObservation) := do
  let fingerprint := defEqRepeatFingerprint levelParams ctx left right
  let stats ← profiler.ref.get
  let update := updateRepeatMap stats.defEqRepeats step fingerprint
    (defEqRepeatSummary ctx left right)
    (s!"{exprShort 4 left} | {exprShort 4 right}")
  profiler.ref.set
    {
      stats with
      defEqRepeatObservations := stats.defEqRepeatObservations + 1,
      defEqRepeatHits := stats.defEqRepeatHits + if update.hit then 1 else 0,
      defEqRepeatDropped := stats.defEqRepeatDropped + if update.dropped then 1 else 0,
      defEqRepeats := update.map
    }
  if update.dropped then
    pure none
  else
    pure (some { fingerprint, hit := update.hit })

def updateDefEqRepeatOutcome (entry : RepeatEntry) (hit success : Bool) : RepeatEntry :=
  {
    entry with
    successCount := entry.successCount + if success then 1 else 0,
    failureCount := entry.failureCount + if success then 0 else 1,
    repeatSuccessCount := entry.repeatSuccessCount + if hit && success then 1 else 0,
    repeatFailureCount := entry.repeatFailureCount + if hit && !success then 1 else 0
  }

def Profiler.noteDefEqRepeatOutcome (profiler : Profiler)
    (observation : DefEqRepeatObservation) (success : Bool) : M Unit := do
  let stats ← profiler.ref.get
  match stats.defEqRepeats.get? observation.fingerprint with
  | none => pure ()
  | some entry =>
      profiler.ref.set
        {
          stats with
          defEqRepeatSuccesses := stats.defEqRepeatSuccesses + if success then 1 else 0,
          defEqRepeatFailures := stats.defEqRepeatFailures + if success then 0 else 1,
          defEqRepeatHitSuccesses :=
            stats.defEqRepeatHitSuccesses + if observation.hit && success then 1 else 0,
          defEqRepeatHitFailures :=
            stats.defEqRepeatHitFailures + if observation.hit && !success then 1 else 0,
          defEqRepeats :=
            stats.defEqRepeats.insert observation.fingerprint
              (updateDefEqRepeatOutcome entry observation.hit success)
        }

def Profiler.noteWhnfRepeat (profiler : Profiler) (step : Nat)
    (levelParams : LevelContext) (expr : Expr) : M Unit := do
  let fingerprint := whnfRepeatFingerprint levelParams expr
  let stats ← profiler.ref.get
  let update := updateRepeatMap stats.whnfRepeats step fingerprint
    (whnfRepeatSummary expr) (exprShort 5 expr)
  profiler.ref.set
    {
      stats with
      whnfRepeatObservations := stats.whnfRepeatObservations + 1,
      whnfRepeatHits := stats.whnfRepeatHits + if update.hit then 1 else 0,
      whnfRepeatDropped := stats.whnfRepeatDropped + if update.dropped then 1 else 0,
      whnfRepeats := update.map
    }

def Profiler.noteDefEq (profiler : Profiler) (ctx : Context) (left right : Expr) : M Unit := do
  let key := exprHeadLabel left ++ " | " ++ exprHeadLabel right
  let shapeKey := exprShapeLabel left ++ " | " ++ exprShapeLabel right
  let ctxKey := toString ctx.length
  profiler.step fun stats =>
    { stats with
      defEqHeadPairs := incrementString stats.defEqHeadPairs key,
      defEqShapePairs := incrementString stats.defEqShapePairs shapeKey,
      defEqContextDepths := incrementString stats.defEqContextDepths ctxKey }

def recordStats (profiler : Profiler) (update : Stats → Stats) : M Unit := do
  let stats ← profiler.ref.get
  profiler.ref.set (update stats)

def Profiler.checkDefEqSuccessCache? (profiler : Profiler) (key : DefEqKey) :
    M Bool := do
  match (← profiler.defEqSuccessCacheRef.get).get? key with
  | some () => do
      recordStats profiler fun stats =>
        { stats with defEqSuccessCacheHits := stats.defEqSuccessCacheHits + 1 }
      pure true
  | none => do
      recordStats profiler fun stats =>
        { stats with defEqSuccessCacheMisses := stats.defEqSuccessCacheMisses + 1 }
      pure false

def Profiler.insertDefEqSuccessCache (profiler : Profiler) (key : DefEqKey) : M Unit := do
  let cache ← profiler.defEqSuccessCacheRef.get
  if cache.contains key then
    pure ()
  else if cache.size < defEqSuccessCacheLimit then
    profiler.defEqSuccessCacheRef.set (cache.insert key ())
    recordStats profiler fun stats =>
      { stats with defEqSuccessCacheEntries := stats.defEqSuccessCacheEntries + 1 }
  else
    recordStats profiler fun stats =>
      { stats with defEqSuccessCacheDropped := stats.defEqSuccessCacheDropped + 1 }

def Profiler.noteStructuralCompare (profiler : Profiler) (left right : Expr) : M Unit := do
  let key := exprShapeLabel left ++ " | " ++ exprShapeLabel right
  let stats ← profiler.ref.get
  let samples :=
    match left, right with
    | .proj .., _ | _, .proj .. =>
        if stats.structuralProjectionSamples.length < 20 then
          stats.structuralProjectionSamples ++ [(exprShort 5 left, exprShort 5 right)]
        else
          stats.structuralProjectionSamples
    | _, _ => stats.structuralProjectionSamples
  let lambdaSamples :=
    match left, right with
    | .lam .., .lam .. =>
        if stats.structuralLambdaSamples.length < 20 then
          stats.structuralLambdaSamples ++ [(exprShort 5 left, exprShort 5 right)]
        else
          stats.structuralLambdaSamples
    | _, _ => stats.structuralLambdaSamples
  profiler.ref.set
    {
      stats with
      structuralHeadPairs := incrementString stats.structuralHeadPairs key,
      structuralProjectionSamples := samples,
      structuralLambdaSamples := lambdaSamples
    }

def Profiler.noteUnfold (profiler : Profiler) (name : Name) : M Unit := do
  profiler.step fun stats =>
    {
      stats with
      definitionUnfolds := stats.definitionUnfolds + 1,
      unfoldNames := incrementString stats.unfoldNames name
    }

def recordAttempt (profiler : Profiler) (update : Stats → Stats) : M Unit :=
  profiler.step update

mutual

partial def whnfAlphaEq (profiler : Profiler) (manifest : Manifest) (env : Env)
    (levelParams : LevelContext) (left right : Expr) : M Bool := do
  profiler.mark "whnf-alpha-eq"
  profiler.step fun stats => { stats with whnfAlphaEqCalls := stats.whnfAlphaEqCalls + 1 }
  let left ← whnf profiler manifest env levelParams left
  let right ← whnf profiler manifest env levelParams right
  match left, right with
  | .bvar left, .bvar right => pure (left == right)
  | .sort left, .sort right => pure (left.defEq right)
  | .const leftName leftLevels, .const rightName rightLevels =>
      pure
        (leftName == rightName &&
          leftLevels.length == rightLevels.length &&
          (leftLevels.zip rightLevels).all fun pair => pair.1.defEq pair.2)
  | .lit left, .lit right => pure (left == right)
  | .app leftFn leftArg, .app rightFn rightArg => do
      if ← whnfAlphaEq profiler manifest env levelParams leftFn rightFn then
        whnfAlphaEq profiler manifest env levelParams leftArg rightArg
      else
        pure false
  | .lam _ leftType leftBody, .lam _ rightType rightBody => do
      if ← whnfAlphaEq profiler manifest env levelParams leftType rightType then
        whnfAlphaEq profiler manifest env levelParams leftBody rightBody
      else
        pure false
  | .forallE _ leftType leftBody, .forallE _ rightType rightBody => do
      if ← whnfAlphaEq profiler manifest env levelParams leftType rightType then
        whnfAlphaEq profiler manifest env levelParams leftBody rightBody
      else
        pure false
  | .letE _ _ leftValue leftBody, _ =>
      whnfAlphaEq profiler manifest env levelParams (Expr.instantiate1 leftBody leftValue) right
  | _, .letE _ _ rightValue rightBody =>
      whnfAlphaEq profiler manifest env levelParams left (Expr.instantiate1 rightBody rightValue)
  | .proj leftStruct leftIndex leftTarget, .proj rightStruct rightIndex rightTarget =>
      if leftStruct == rightStruct && leftIndex == rightIndex then
        whnfAlphaEq profiler manifest env levelParams leftTarget rightTarget
      else
        pure false
  | _, _ => pure false

partial def reduceQuotLift? (profiler : Profiler) (manifest : Manifest) (env : Env)
    (levelParams : LevelContext) (_levels : List Level) (args : List Expr) :
    M (Option Expr) := do
  profiler.mark "reduce-quot-lift"
  recordAttempt profiler fun stats =>
    { stats with quotientReductionAttempts := stats.quotientReductionAttempts + 1 }
  if !manifest.supportsQuotients then
    pure none
  else
    let required := 6
    if args.length < required then
      pure none
    else
      let some fnArg := listGet? args 3
        | pure none
      let some quotientArg := listGet? args 5
        | pure none
      let trailing := args.drop required
      let quotientWhnf ← whnf profiler manifest env levelParams quotientArg
      let (quotientHead, quotientArgs) := quotientWhnf.getAppFnArgs
      match quotientHead with
      | Expr.const mkName _ =>
          match env.find? mkName with
          | some { kind := .quotientMk, .. } =>
              let some valueArg := listGet? quotientArgs 2
                | pure none
              profiler.step fun stats =>
                { stats with quotientReductionSuccesses := stats.quotientReductionSuccesses + 1 }
              pure (some (Expr.mkApps (.app fnArg valueArg) trailing))
          | _ => pure none
      | _ => pure none

partial def reduceEqRec? (profiler : Profiler) (manifest : Manifest) (env : Env)
    (levelParams : LevelContext) (args : List Expr) : M (Option Expr) := do
  profiler.mark "reduce-eq-rec"
  recordAttempt profiler fun stats =>
    { stats with equalityRecReductionAttempts := stats.equalityRecReductionAttempts + 1 }
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
      let proofWhnf ← whnf profiler manifest env levelParams proofArg
      let reduceToMinorIfEndpointsMatch : M (Option Expr) := do
        if ← whnfAlphaEq profiler manifest env levelParams aArg bArg then
          profiler.step fun stats =>
            { stats with equalityRecReductionSuccesses := stats.equalityRecReductionSuccesses + 1 }
          pure (some (Expr.mkApps minorArg trailing))
        else
          pure none
      match proofWhnf.getAppFnArgs with
      | (Expr.const reflName _, proofArgs) =>
          match env.find? reflName with
          | some { kind := .equalityRefl, .. } =>
              let some reflTypeArg := listGet? proofArgs 0
                | pure none
              let some reflValueArg := listGet? proofArgs 1
                | pure none
              if reflTypeArg == typeArg && reflValueArg == aArg && bArg == aArg then
                profiler.step fun stats =>
                  { stats with equalityRecReductionSuccesses := stats.equalityRecReductionSuccesses + 1 }
                pure (some (Expr.mkApps minorArg trailing))
              else
                reduceToMinorIfEndpointsMatch
          | _ => reduceToMinorIfEndpointsMatch
      | _ => reduceToMinorIfEndpointsMatch

partial def whnf (profiler : Profiler) (manifest : Manifest) (env : Env)
    (levelParams : LevelContext) (expr : Expr) : M Expr := do
  if !profiler.useMemo || !exprCacheable whnfCacheExprLimit expr then
    whnfCore profiler manifest env levelParams expr
  else
    let key : WhnfKey := { levelParams, expr }
    match (← profiler.whnfCacheRef.get).get? key with
    | some value => do
        recordStats profiler fun stats =>
          { stats with whnfCacheHits := stats.whnfCacheHits + 1 }
        pure value
    | none => do
        recordStats profiler fun stats =>
          { stats with whnfCacheMisses := stats.whnfCacheMisses + 1 }
        let value ← whnfCore profiler manifest env levelParams expr
        profiler.whnfCacheRef.set ((← profiler.whnfCacheRef.get).insert key value)
        recordStats profiler fun stats =>
          { stats with whnfCacheEntries := stats.whnfCacheEntries + 1 }
        pure value

partial def whnfCore (profiler : Profiler) (manifest : Manifest) (env : Env)
    (levelParams : LevelContext) (expr : Expr) : M Expr := do
  profiler.mark "whnf"
  profiler.step fun stats => { stats with whnfCalls := stats.whnfCalls + 1 }
  if profiler.useRepeatDiag then
    let stats ← profiler.ref.get
    profiler.noteWhnfRepeat stats.steps levelParams expr
  match expr with
  | .letE _ _ value body => do
      profiler.step fun stats => { stats with zetaReductions := stats.zetaReductions + 1 }
      whnf profiler manifest env levelParams (Expr.instantiate1 body value)
  | .proj structureName fieldIndex target => do
      if !manifest.supportsProjections then
        pure (.proj structureName fieldIndex target)
      else
        recordAttempt profiler fun stats =>
          { stats with projectionReductionAttempts := stats.projectionReductionAttempts + 1 }
        let targetWhnf ← whnf profiler manifest env levelParams target
        match ← liftResult
            (_root_.MPC.Packages.Projection.reduceTarget? manifest env structureName fieldIndex targetWhnf) with
        | some reduced => do
            profiler.step fun stats =>
              { stats with projectionReductionSuccesses := stats.projectionReductionSuccesses + 1 }
            whnf profiler manifest env levelParams reduced
        | none => pure (.proj structureName fieldIndex targetWhnf)
  | .app fn arg => do
      profiler.mark "whnf:app"
      let appExpr := Expr.app fn arg
      let (head, args) := Expr.getAppFnArgs appExpr
      let primitiveReduction? ←
        match head with
        | .const name levels =>
            match env.find? name with
            | some info => do
                recordAttempt profiler fun stats =>
                  { stats with primitiveReductionAttempts := stats.primitiveReductionAttempts + 1 }
                liftResult
                  (_root_.MPC.Packages.PrimitiveNat.reduce?
                    _root_.MPC.whnf manifest env levelParams name info levels args)
            | none => pure none
        | _ => pure none
      match primitiveReduction? with
      | some reduced => do
          profiler.step fun stats =>
            { stats with primitiveReductionSuccesses := stats.primitiveReductionSuccesses + 1 }
          whnf profiler manifest env levelParams reduced
      | none =>
          let projectionReduction? ←
            match head with
            | .const name levels => do
                recordAttempt profiler fun stats =>
                  { stats with projectionReductionAttempts := stats.projectionReductionAttempts + 1 }
                liftResult
                  (_root_.MPC.Packages.Projection.reduceConstant?
                    _root_.MPC.whnf manifest env levelParams name levels args)
            | _ => pure none
          match projectionReduction? with
          | some reduced => do
              profiler.step fun stats =>
                { stats with projectionReductionSuccesses := stats.projectionReductionSuccesses + 1 }
              whnf profiler manifest env levelParams reduced
          | none =>
              profiler.mark "whnf:head"
              let head ← whnf profiler manifest env levelParams head
              match head with
              | Expr.const name levels =>
                  match env.find? name with
                  | some { kind := .recursor info, .. } =>
                      recordAttempt profiler fun stats =>
                        { stats with recursorReductionAttempts := stats.recursorReductionAttempts + 1 }
                      match ← liftResult
                          (_root_.MPC.reduceSimpleRecursor?
                            _root_.MPC.whnf manifest env levelParams name info levels args) with
                      | some reduced => do
                          profiler.step fun stats =>
                            { stats with
                              recursorReductionSuccesses :=
                                stats.recursorReductionSuccesses + 1 }
                          whnf profiler manifest env levelParams reduced
                      | none => pure (Expr.mkApps head args)
                  | some { kind := .mutualRecursor info, .. } =>
                      recordAttempt profiler fun stats =>
                        { stats with recursorReductionAttempts := stats.recursorReductionAttempts + 1 }
                      match ← liftResult
                          (_root_.MPC.reduceMutualRecursor?
                            _root_.MPC.whnf manifest env levelParams name info levels args) with
                      | some reduced => do
                          profiler.step fun stats =>
                            { stats with
                              recursorReductionSuccesses :=
                                stats.recursorReductionSuccesses + 1 }
                          whnf profiler manifest env levelParams reduced
                      | none => pure (Expr.mkApps head args)
                  | some { kind := .indexedRecursor info, .. } =>
                      recordAttempt profiler fun stats =>
                        { stats with recursorReductionAttempts := stats.recursorReductionAttempts + 1 }
                      match ← liftResult
                          (_root_.MPC.reduceIndexedRecursor?
                            _root_.MPC.whnf manifest env levelParams name info levels args) with
                      | some reduced => do
                          profiler.step fun stats =>
                            { stats with
                              recursorReductionSuccesses :=
                                stats.recursorReductionSuccesses + 1 }
                          whnf profiler manifest env levelParams reduced
                      | none => pure (Expr.mkApps head args)
                  | some { kind := .nestedRecursor info, .. } =>
                      recordAttempt profiler fun stats =>
                        { stats with recursorReductionAttempts := stats.recursorReductionAttempts + 1 }
                      match ← liftResult
                          (_root_.MPC.reduceNestedRecursor?
                            _root_.MPC.whnf manifest env levelParams name info levels args) with
                      | some reduced => do
                          profiler.step fun stats =>
                            { stats with
                              recursorReductionSuccesses :=
                                stats.recursorReductionSuccesses + 1 }
                          whnf profiler manifest env levelParams reduced
                      | none => pure (Expr.mkApps head args)
                  | some { kind := .quotientLift, .. } =>
                      match ← reduceQuotLift? profiler manifest env levelParams levels args with
                      | some reduced => whnf profiler manifest env levelParams reduced
                      | none => pure (Expr.mkApps head args)
                  | some { kind := .equalityRec, .. } =>
                      match ← reduceEqRec? profiler manifest env levelParams args with
                      | some reduced => whnf profiler manifest env levelParams reduced
                      | none => pure (Expr.mkApps head args)
                  | _ => pure (Expr.mkApps head args)
              | .lam _ _ body =>
                  match args with
                  | first :: rest => do
                      profiler.step fun stats =>
                        { stats with betaReductions := stats.betaReductions + 1 }
                      whnf profiler manifest env levelParams
                        (Expr.mkApps (Expr.instantiate1 body first) rest)
                  | [] => pure head
              | .app _ _ =>
                  whnf profiler manifest env levelParams (Expr.mkApps head args)
              | _ => pure (Expr.mkApps head args)
  | .const name levels =>
      profiler.mark s!"whnf:const:{name}"
      match env.find? name with
      | some info =>
          match info.kind with
          | .definition => do
              match info.instantiateValue? levels with
              | some value => do
                  profiler.mark s!"whnf:unfold:{name}"
                  profiler.noteUnfold name
                  whnf profiler manifest env levelParams value
              | none => pure (.const name levels)
          | _ => pure (.const name levels)
      | none => pure (.const name levels)
  | _ => pure expr

partial def infer (profiler : Profiler) (manifest : Manifest) (env : Env)
    (levelParams : LevelContext) (ctx : Context) : Expr → M Expr
  | .bvar index => do
      profiler.mark "infer:bvar"
      profiler.step fun stats => { stats with inferCalls := stats.inferCalls + 1 }
      match ctx.lookup? index with
      | some binder => pure binder.type
      | none => fail s!"unbound de Bruijn index: {index}"
  | .sort level => do
      profiler.mark "infer:sort"
      profiler.step fun stats => { stats with inferCalls := stats.inferCalls + 1 }
      if level.closedIn levelParams then
        pure (.sort (.succ level))
      else
        fail s!"sort level is not closed in active universe context: {repr level}"
  | .const name levels => do
      profiler.mark s!"infer:const:{name}"
      profiler.step fun stats => { stats with inferCalls := stats.inferCalls + 1 }
      liftResult (MPC.checkLevelsClosed levelParams levels)
      let some info := env.find? name
        | fail s!"unknown constant: {name}"
      let some type := info.instantiateType? levels
        | fail s!"constant {name} expects {info.levelParams.length} universe levels, got {levels.length}"
      pure type
  | .lit (.nat _) => do
      profiler.mark "infer:nat-lit"
      profiler.step fun stats => { stats with inferCalls := stats.inferCalls + 1 }
      if !manifest.supportsNatLiterals then
        fail "natural literals are disabled by the manifest"
      else
        liftResult (MPC.Packages.Literal.requireNatSupport env)
        pure (.const "Nat" [])
  | .lit (.str _) => do
      profiler.mark "infer:string-lit"
      profiler.step fun stats => { stats with inferCalls := stats.inferCalls + 1 }
      if !manifest.supportsStringLiterals then
        fail "string literals are disabled by the manifest"
      else
        liftResult (MPC.Packages.Literal.requireStringSupport env)
        pure (.const "String" [])
  | .app fn arg => do
      profiler.mark "infer:app"
      profiler.step fun stats => { stats with inferCalls := stats.inferCalls + 1 }
      let fnType ← whnf profiler manifest env levelParams
        (← infer profiler manifest env levelParams ctx fn)
      match fnType with
      | .forallE _ domain body => do
          check profiler manifest env levelParams ctx arg domain
          pure (Expr.instantiate1 body arg)
      | _ => fail s!"function expected, got {repr fnType}"
  | .lam name domain body => do
      profiler.mark "infer:lambda"
      profiler.step fun stats => { stats with inferCalls := stats.inferCalls + 1 }
      let _ ← inferSort profiler manifest env levelParams ctx domain
      let bodyType ← infer profiler manifest env levelParams (ctx.extend name domain) body
      pure (.forallE name domain bodyType)
  | .forallE name domain body => do
      profiler.mark "infer:forall"
      profiler.step fun stats => { stats with inferCalls := stats.inferCalls + 1 }
      let domainSort ← inferSort profiler manifest env levelParams ctx domain
      let bodySort ← inferSort profiler manifest env levelParams (ctx.extend name domain) body
      pure (.sort (MPC.inferPiSort manifest domainSort bodySort))
  | .letE _ type value body => do
      profiler.mark "infer:let"
      profiler.step fun stats => { stats with inferCalls := stats.inferCalls + 1 }
      let _ ← inferSort profiler manifest env levelParams ctx type
      check profiler manifest env levelParams ctx value type
      infer profiler manifest env levelParams ctx (Expr.instantiate1 body value)
  | .proj structureName fieldIndex target => do
      profiler.mark s!"infer:proj:{structureName}.{fieldIndex}"
      profiler.step fun stats => { stats with inferCalls := stats.inferCalls + 1 }
      if !manifest.supportsProjections then
        fail "projection expressions are disabled by the manifest"
      else
        let targetType ← whnf profiler manifest env levelParams
          (← infer profiler manifest env levelParams ctx target)
        liftResult
          (MPC.Packages.Projection.fieldType env structureName fieldIndex target targetType)

partial def inferSort (profiler : Profiler) (manifest : Manifest) (env : Env)
    (levelParams : LevelContext) (ctx : Context) (expr : Expr) : M Level := do
  profiler.mark "infer-sort"
  profiler.step fun stats => { stats with inferSortCalls := stats.inferSortCalls + 1 }
  let type ← whnf profiler manifest env levelParams
    (← infer profiler manifest env levelParams ctx expr)
  match type with
  | .sort level => pure level
  | _ => fail s!"sort expected for {repr expr}, got {repr type}"

partial def check (profiler : Profiler) (manifest : Manifest) (env : Env)
    (levelParams : LevelContext) (ctx : Context) (expr expectedType : Expr) : M Unit := do
  profiler.mark "check"
  profiler.step fun stats => { stats with checkCalls := stats.checkCalls + 1 }
  match expr with
  | .lam name domain body => do
      let expectedType ← whnf profiler manifest env levelParams expectedType
      match expectedType with
      | .forallE _ expectedDomain expectedBody => do
          let _ ← inferSort profiler manifest env levelParams ctx domain
          profileDefEq profiler manifest env levelParams ctx domain expectedDomain
          check profiler manifest env levelParams (ctx.extend name domain) body expectedBody
      | _ =>
          let inferred ← infer profiler manifest env levelParams ctx expr
          profileDefEq profiler manifest env levelParams ctx inferred expectedType
  | .letE _ type value body => do
      let _ ← inferSort profiler manifest env levelParams ctx type
      check profiler manifest env levelParams ctx value type
      check profiler manifest env levelParams ctx (Expr.instantiate1 body value) expectedType
  | _ =>
      let inferred ← infer profiler manifest env levelParams ctx expr
      profileDefEq profiler manifest env levelParams ctx inferred expectedType

partial def reduceEqRecByEndpointDefEq? (profiler : Profiler) (manifest : Manifest)
    (env : Env) (levelParams : LevelContext) (ctx : Context) (expr : Expr) :
    M (Option Expr) := do
  profiler.mark "reduce-eq-rec-by-endpoint"
  profiler.step fun stats =>
    { stats with reduceEqRecByEndpointCalls := stats.reduceEqRecByEndpointCalls + 1 }
  let expr ← whnf profiler manifest env levelParams expr
  let (head, args) := expr.getAppFnArgs
  match head with
  | .const name _ =>
      match env.find? name with
      | some { kind := .equalityRec, .. } =>
          let required := 6
          if args.length < required then
            pure none
          else
            let some aArg := listGet? args 1
              | pure none
            let some minorArg := listGet? args 3
              | pure none
            let some bArg := listGet? args 4
              | pure none
            match ← capture (profileDefEq profiler manifest env levelParams ctx aArg bArg) with
            | Except.ok () => pure (some (Expr.mkApps minorArg (args.drop required)))
            | Except.error _ => pure none
      | _ => pure none
  | _ => pure none

partial def structuralDefEq (profiler : Profiler) (manifest : Manifest) (env : Env)
    (levelParams : LevelContext) (ctx : Context) (left right : Expr) : M Unit := do
  profiler.mark "structural-defeq"
  profiler.step fun stats =>
    { stats with structuralDefEqCalls := stats.structuralDefEqCalls + 1 }
  profiler.mark "structural-defeq:left-whnf"
  let left ← whnf profiler manifest env levelParams left
  profiler.mark "structural-defeq:right-whnf"
  let right ← whnf profiler manifest env levelParams right
  profiler.mark "structural-defeq:compare"
  profiler.noteStructuralCompare left right
  if left.alphaEq right then
    recordStats profiler fun stats =>
      { stats with structuralWhnfAlphaEqHits := stats.structuralWhnfAlphaEqHits + 1 }
  else
  match left, right with
  | .bvar left, .bvar right =>
      if left == right then pure () else fail "bound variables differ"
  | .sort left, .sort right =>
      if left.defEq right then pure () else fail "sort levels differ"
  | .const leftName leftLevels, .const rightName rightLevels =>
      if leftName != rightName || leftLevels.length != rightLevels.length then
        fail s!"constants differ: {leftName}{repr leftLevels} and {rightName}{repr rightLevels}"
      else
        liftResult (MPC.checkLevelArgsDefEq leftLevels rightLevels)
  | .lit left, .lit right =>
      if left == right then pure () else fail "literals differ"
  | .lit (.nat value), _ =>
      if !manifest.supportsNatLiterals then
        fail "natural literals are disabled by the manifest"
      else
        structuralDefEq profiler manifest env levelParams ctx
          (← liftResult (MPC.Packages.Literal.natConstructorSpine env value)) right
  | _, .lit (.nat value) =>
      if !manifest.supportsNatLiterals then
        fail "natural literals are disabled by the manifest"
      else
        structuralDefEq profiler manifest env levelParams ctx left
          (← liftResult (MPC.Packages.Literal.natConstructorSpine env value))
  | .app .., .app .. => do
      let (leftHead, leftArgs) := left.getAppFnArgs
      let (rightHead, rightArgs) := right.getAppFnArgs
      if leftArgs.length != rightArgs.length then
        fail "application arities differ"
      else
        let genericApplicationCompare : M Unit := do
          profileDefEq profiler manifest env levelParams ctx leftHead rightHead
          for pair in leftArgs.zip rightArgs do
            profileDefEq profiler manifest env levelParams ctx pair.1 pair.2
        match leftHead, rightHead with
        | .const leftName leftLevels, .const rightName rightLevels =>
            if manifest.prop == .enabled && leftName == rightName then
              match env.findConstructorFieldInfo? leftName with
              | some fieldInfo =>
                  let expectedArity := fieldInfo.paramCount + fieldInfo.proofFields.length
                  if leftArgs.length == expectedArity &&
                      rightArgs.length == expectedArity then
                    liftResult (MPC.checkLevelArgsDefEq leftLevels rightLevels)
                    for pair in (leftArgs.take fieldInfo.paramCount).zip
                        (rightArgs.take fieldInfo.paramCount) do
                      profileDefEq profiler manifest env levelParams ctx pair.1 pair.2
                    let leftFields := leftArgs.drop fieldInfo.paramCount
                    let rightFields := rightArgs.drop fieldInfo.paramCount
                    for pair in fieldInfo.proofFields.zip (leftFields.zip rightFields) do
                      if pair.1 then
                        recordStats profiler fun stats =>
                          {
                            stats with
                            constructorProofFieldSkips := stats.constructorProofFieldSkips + 1
                          }
                      else
                        profileDefEq profiler manifest env levelParams ctx pair.2.1 pair.2.2
                  else
                    genericApplicationCompare
              | none => genericApplicationCompare
            else
              genericApplicationCompare
        | _, _ => genericApplicationCompare
  | .lam _ leftType leftBody, .lam _ rightType rightBody => do
      profileDefEq profiler manifest env levelParams ctx leftType rightType
      profileDefEq profiler manifest env levelParams (ctx.extend "_" leftType) leftBody rightBody
  | .forallE _ leftType leftBody, .forallE _ rightType rightBody => do
      profileDefEq profiler manifest env levelParams ctx leftType rightType
      profileDefEq profiler manifest env levelParams (ctx.extend "_" leftType) leftBody rightBody
  | .letE _ _ leftValue leftBody, _ =>
      profileDefEq profiler manifest env levelParams ctx (Expr.instantiate1 leftBody leftValue) right
  | _, .letE _ _ rightValue rightBody =>
      profileDefEq profiler manifest env levelParams ctx left (Expr.instantiate1 rightBody rightValue)
  | .proj leftStruct leftIndex leftTarget, .proj rightStruct rightIndex rightTarget =>
      if leftStruct == rightStruct && leftIndex == rightIndex then
        profileDefEq profiler manifest env levelParams ctx leftTarget rightTarget
      else
        fail "projections differ"
  | _, _ => fail "not definitionally equal"

partial def isPropExpr (profiler : Profiler) (manifest : Manifest) (env : Env)
    (levelParams : LevelContext) (ctx : Context) (expr : Expr) : M Unit := do
  profiler.mark "is-prop"
  if manifest.prop != .enabled then
    fail "Prop is disabled by the manifest"
  else
    let sort ← inferSort profiler manifest env levelParams ctx expr
    if sort.defEqZero then pure () else fail s!"not a proposition: {repr expr}"

partial def proofIrrelevanceDefEq (profiler : Profiler) (manifest : Manifest) (env : Env)
    (levelParams : LevelContext) (ctx : Context) (left right : Expr) : M Unit := do
  profiler.mark "proof-irrelevance"
  profiler.step fun stats =>
    { stats with proofIrrelevanceCalls := stats.proofIrrelevanceCalls + 1 }
  if manifest.prop != .enabled then
    fail "proof irrelevance is disabled by the manifest"
  else
    let leftType ← infer profiler manifest env levelParams ctx left
    isPropExpr profiler manifest env levelParams ctx leftType
    let rightType ← infer profiler manifest env levelParams ctx right
    profileDefEq profiler manifest env levelParams ctx leftType rightType

partial def singletonInductiveDefEq (profiler : Profiler) (manifest : Manifest) (env : Env)
    (levelParams : LevelContext) (ctx : Context) (left right : Expr) : M Unit := do
  profiler.mark "singleton-inductive"
  profiler.step fun stats =>
    { stats with singletonInductiveCalls := stats.singletonInductiveCalls + 1 }
  if !manifest.supportsSimpleInductives then
    fail "simple inductives are disabled by the manifest"
  else
    let leftType ← whnf profiler manifest env levelParams
      (← infer profiler manifest env levelParams ctx left)
    let rightType ← whnf profiler manifest env levelParams
      (← infer profiler manifest env levelParams ctx right)
    let (leftHead, leftArgs) := leftType.getAppFnArgs
    let (rightHead, rightArgs) := rightType.getAppFnArgs
    match leftHead, rightHead with
    | .const leftName leftLevels, .const rightName rightLevels =>
        if leftName != rightName || leftLevels.length != rightLevels.length ||
            leftArgs.length != rightArgs.length then
          fail "singleton inductive target types differ"
        else
          match env.find? leftName with
          | some { kind := .inductiveType spec, levelParams := specLevelParams, .. } =>
              match spec.constructors with
              | [ctor] =>
                  if leftLevels.length != specLevelParams.length ||
                      leftArgs.length != spec.params.length ||
                      !ctor.fields.isEmpty then
                    fail "singleton inductive target shape mismatch"
                  else
                    profileDefEq profiler manifest env levelParams ctx leftType rightType
              | _ => fail "singleton inductive target has multiple constructors"
          | _ => fail "singleton inductive target is not a simple inductive"
    | _, _ => fail "singleton inductive target types are not constant applications"

partial def functionEtaDefEq (profiler : Profiler) (manifest : Manifest) (env : Env)
    (levelParams : LevelContext) (ctx : Context) (etaExpanded other : Expr) : M Unit := do
  profiler.mark "function-eta"
  profiler.step fun stats => { stats with functionEtaCalls := stats.functionEtaCalls + 1 }
  if !manifest.supportsFunctionEta then
    fail "function eta is disabled by the manifest"
  else
    let etaExpanded ← whnf profiler manifest env levelParams etaExpanded
    match etaExpanded with
    | .lam name domain body => do
        let otherType ← whnf profiler manifest env levelParams
          (← infer profiler manifest env levelParams ctx other)
        match otherType with
        | .forallE _ expectedDomain _ => do
            profileDefEq profiler manifest env levelParams ctx domain expectedDomain
            let expectedBody := Expr.app (other.lift 1) (.bvar 0)
            profileDefEq profiler manifest env levelParams (ctx.extend name domain) body expectedBody
        | _ => fail "function eta target is not a function"
    | _ => fail "function eta expansion is not a lambda"

partial def structureEtaDefEq (profiler : Profiler) (manifest : Manifest) (env : Env)
    (levelParams : LevelContext) (ctx : Context) (other ctorExpr : Expr) : M Unit := do
  profiler.mark "structure-eta"
  profiler.step fun stats => { stats with structureEtaCalls := stats.structureEtaCalls + 1 }
  if !manifest.supportsProjections then
    fail "structure eta is disabled by the manifest"
  else
    let other ← whnf profiler manifest env levelParams other
    let ctorExpr ← whnf profiler manifest env levelParams ctorExpr
    let (otherHead, _) := other.getAppFnArgs
    match otherHead with
    | .const otherName _ =>
        match env.find? otherName with
        | some { kind := .constructor .., .. } => fail "structure eta target is constructor-headed"
        | _ => pure ()
    | _ => pure ()
    let (ctorHead, ctorArgs) := ctorExpr.getAppFnArgs
    match ctorHead with
    | .const ctorName ctorLevels =>
        match env.find? ctorName with
        | some { kind := .constructor inductiveName ctorIndex fieldCount, .. } =>
            match env.find? inductiveName with
            | some { kind := .inductiveType spec, .. } =>
                match spec.constructors with
                | [ctor] =>
                    if ctorIndex != 0 ||
                        ctor.name != ctorName ||
                        fieldCount != ctor.fields.length ||
                        ctorArgs.length != spec.params.length + fieldCount ||
                        ctorLevels.length != spec.levelParams.length then
                      fail "structure eta constructor shape mismatch"
                    else if !simpleRecursorEtaDataResult spec ctorLevels then
                      fail "structure eta target is proposition-valued"
                    else
                      match env.find? (inductiveName ++ ".rec") with
                      | some { kind := .recursor recursorInfo, .. } =>
                          let some ctorInfo :=
                              findSimpleRecursorConstructor? ctorName recursorInfo.constructors
                            | fail "structure eta recursor metadata missing constructor"
                          if !ctorInfo.recursiveFields.isEmpty then
                            fail "structure eta target has recursive fields"
                          else
                            profileDefEq profiler manifest env levelParams ctx
                              (← infer profiler manifest env levelParams ctx other)
                              (← infer profiler manifest env levelParams ctx ctorExpr)
                            let fieldArgs := ctorArgs.drop spec.params.length
                            for pair in (List.range fieldCount).zip fieldArgs do
                              profileDefEq profiler manifest env levelParams ctx
                                (Expr.proj inductiveName pair.1 other)
                                pair.2
                      | _ => fail "structure eta recursor metadata missing"
                | _ => fail "structure eta target is not a one-constructor structure"
            | _ => fail "structure eta target is not a simple inductive"
        | _ => fail "structure eta expression is not constructor-headed"
    | _ => fail "structure eta expression is not constructor-headed"

partial def profileDefEq (profiler : Profiler) (manifest : Manifest) (env : Env)
    (levelParams : LevelContext) (ctx : Context) (left right : Expr) : M Unit := do
  profiler.mark "defeq"
  profiler.noteDefEq ctx left right
  profiler.step fun stats => { stats with defEqCalls := stats.defEqCalls + 1 }
  let alphaEq := left.alphaEq right
  if alphaEq then
    recordStats profiler fun stats =>
      { stats with defEqAlphaEqHits := stats.defEqAlphaEqHits + 1 }
  else do
    let successCacheKey? :=
      if profiler.useDefEqSuccessCache then
        some ({ levelParams, ctx, left, right } : DefEqKey)
      else
        none
    match successCacheKey? with
    | some key =>
        if ← profiler.checkDefEqSuccessCache? key then
          return ()
    | none => pure ()
    let observation? ←
      if profiler.useRepeatDiag then
        let stats ← profiler.ref.get
        profiler.noteDefEqRepeat stats.steps levelParams ctx left right
      else
        pure none
    let runCompare : M Unit :=
      if !profiler.useMemo ||
          !ctx.isEmpty ||
          !exprCacheable defEqCacheExprLimit left ||
          !exprCacheable defEqCacheExprLimit right then
        profileDefEqCore profiler manifest env levelParams ctx left right
      else do
        let key : DefEqKey := { levelParams, ctx, left, right }
        match (← profiler.defEqCacheRef.get).get? key with
        | some () => do
            recordStats profiler fun stats =>
              { stats with defEqCacheHits := stats.defEqCacheHits + 1 }
            pure ()
        | none => do
            recordStats profiler fun stats =>
              { stats with defEqCacheMisses := stats.defEqCacheMisses + 1 }
            match ← capture (profileDefEqCore profiler manifest env levelParams ctx left right) with
            | Except.ok () => do
                let cache ← profiler.defEqCacheRef.get
                profiler.defEqCacheRef.set (cache.insert key ())
                recordStats profiler fun stats =>
                  { stats with defEqCacheEntries := stats.defEqCacheEntries + 1 }
                pure ()
            | Except.error err => throw err
    if profiler.useRepeatDiag then
      match ← capture runCompare with
      | Except.ok () => do
          match observation? with
          | some observation => profiler.noteDefEqRepeatOutcome observation true
          | none => pure ()
          match successCacheKey? with
          | some key => profiler.insertDefEqSuccessCache key
          | none => pure ()
      | Except.error err => do
          match observation? with
          | some observation => profiler.noteDefEqRepeatOutcome observation false
          | none => pure ()
          throw err
    else
      match ← capture runCompare with
      | Except.ok () => do
          match successCacheKey? with
          | some key => profiler.insertDefEqSuccessCache key
          | none => pure ()
      | Except.error err => throw err

partial def profileDefEqCore (profiler : Profiler) (manifest : Manifest) (env : Env)
    (levelParams : LevelContext) (ctx : Context) (left right : Expr) : M Unit := do
  match ← capture (structuralDefEq profiler manifest env levelParams ctx left right) with
    | Except.ok () => pure ()
    | Except.error structuralError =>
        match ← reduceEqRecByEndpointDefEq? profiler manifest env levelParams ctx left with
        | some reducedLeft => profileDefEq profiler manifest env levelParams ctx reducedLeft right
        | none =>
            match ← reduceEqRecByEndpointDefEq? profiler manifest env levelParams ctx right with
            | some reducedRight => profileDefEq profiler manifest env levelParams ctx left reducedRight
            | none =>
                match ← capture (structureEtaDefEq profiler manifest env levelParams ctx left right) with
                | Except.ok () => pure ()
                | Except.error _ =>
                    match ← capture (structureEtaDefEq profiler manifest env levelParams ctx right left) with
                    | Except.ok () => pure ()
                    | Except.error _ =>
                        match ← capture (singletonInductiveDefEq profiler manifest env levelParams ctx left right) with
                        | Except.ok () => pure ()
                        | Except.error _ =>
                            match ← capture (proofIrrelevanceDefEq profiler manifest env levelParams ctx left right) with
                            | Except.ok () => pure ()
                            | Except.error proofError =>
                                match ← capture (functionEtaDefEq profiler manifest env levelParams ctx left right) with
                                | Except.ok () => pure ()
                                | Except.error _ =>
                                    match ← capture (functionEtaDefEq profiler manifest env levelParams ctx right left) with
                                    | Except.ok () => pure ()
                                    | Except.error _ =>
                                        fail s!"{structuralError.message}; proof irrelevance fallback failed: {proofError.message}"

end

def checkDeclaration (profiler : Profiler) (manifest : Manifest) (env : Env) :
    Declaration → M Unit
  | .axiom _ levelParams type => do
      trace "phase\taxiom\tvalidate"
      liftResult (Manifest.validate manifest)
      trace "phase\taxiom\tinfer-type"
      let _ ← inferSort profiler manifest env levelParams [] type
      pure ()
  | .definition _ levelParams type value
  | .opaque _ levelParams type value => do
      trace "phase\tdefinition\tvalidate"
      liftResult (Manifest.validate manifest)
      trace "phase\tdefinition\tinfer-type"
      let _ ← inferSort profiler manifest env levelParams [] type
      trace "phase\tdefinition\tcheck-value"
      check profiler manifest env levelParams [] value type
  | .theorem _ levelParams type value => do
      trace "phase\ttheorem\tvalidate"
      liftResult (Manifest.validate manifest)
      trace "phase\ttheorem\tcheck-prop"
      isPropExpr profiler manifest env levelParams [] type
      trace "phase\ttheorem\tcheck-value"
      check profiler manifest env levelParams [] value type
  | declaration => do
      trace "phase\tgenerated\tadd-declaration"
      let _ ← liftResult (MPC.addDecl manifest env declaration)
      pure ()

def addDeclaration (profiler : Profiler) (manifest : Manifest) (env : Env) :
    Declaration → M Env
  | .axiom name levelParams type => do
      liftResult (Manifest.validate manifest)
      let _ ← inferSort profiler manifest env levelParams [] type
      liftResult (Env.add env { name, levelParams, type, kind := .axiom })
  | .definition name levelParams type value => do
      liftResult (Manifest.validate manifest)
      let _ ← inferSort profiler manifest env levelParams [] type
      check profiler manifest env levelParams [] value type
      liftResult (Env.add env { name, levelParams, type, value? := some value, kind := .definition })
  | .opaque name levelParams type value => do
      liftResult (Manifest.validate manifest)
      let _ ← inferSort profiler manifest env levelParams [] type
      check profiler manifest env levelParams [] value type
      liftResult (Env.add env { name, levelParams, type, value? := some value, kind := .opaque })
  | .theorem name levelParams type value => do
      liftResult (Manifest.validate manifest)
      isPropExpr profiler manifest env levelParams [] type
      check profiler manifest env levelParams [] value type
      liftResult (Env.add env { name, levelParams, type, value? := some value, kind := .theorem })
  | declaration =>
      liftResult (MPC.addDecl manifest env declaration)

def Stats.toJson (stats : Stats) : Lean.Json :=
  Lean.Json.mkObj [
    ("steps", jsonNat stats.steps),
    ("infer_calls", jsonNat stats.inferCalls),
    ("infer_sort_calls", jsonNat stats.inferSortCalls),
    ("check_calls", jsonNat stats.checkCalls),
    ("defeq_calls", jsonNat stats.defEqCalls),
    ("defeq_alphaeq_hits", jsonNat stats.defEqAlphaEqHits),
    ("structural_defeq_calls", jsonNat stats.structuralDefEqCalls),
    ("structural_whnf_alphaeq_hits", jsonNat stats.structuralWhnfAlphaEqHits),
    ("whnf_calls", jsonNat stats.whnfCalls),
    ("whnf_alpha_eq_calls", jsonNat stats.whnfAlphaEqCalls),
    ("proof_irrelevance_calls", jsonNat stats.proofIrrelevanceCalls),
    ("function_eta_calls", jsonNat stats.functionEtaCalls),
    ("structure_eta_calls", jsonNat stats.structureEtaCalls),
    ("singleton_inductive_calls", jsonNat stats.singletonInductiveCalls),
    ("reduce_eqrec_by_endpoint_calls", jsonNat stats.reduceEqRecByEndpointCalls),
    ("zeta_reductions", jsonNat stats.zetaReductions),
    ("beta_reductions", jsonNat stats.betaReductions),
    ("definition_unfolds", jsonNat stats.definitionUnfolds),
    ("primitive_reduction_attempts", jsonNat stats.primitiveReductionAttempts),
    ("primitive_reduction_successes", jsonNat stats.primitiveReductionSuccesses),
    ("projection_reduction_attempts", jsonNat stats.projectionReductionAttempts),
    ("projection_reduction_successes", jsonNat stats.projectionReductionSuccesses),
    ("recursor_reduction_attempts", jsonNat stats.recursorReductionAttempts),
    ("recursor_reduction_successes", jsonNat stats.recursorReductionSuccesses),
    ("quotient_reduction_attempts", jsonNat stats.quotientReductionAttempts),
    ("quotient_reduction_successes", jsonNat stats.quotientReductionSuccesses),
    ("equality_rec_reduction_attempts", jsonNat stats.equalityRecReductionAttempts),
    ("equality_rec_reduction_successes", jsonNat stats.equalityRecReductionSuccesses),
    ("whnf_cache_hits", jsonNat stats.whnfCacheHits),
    ("whnf_cache_misses", jsonNat stats.whnfCacheMisses),
    ("whnf_cache_entries", jsonNat stats.whnfCacheEntries),
    ("defeq_cache_hits", jsonNat stats.defEqCacheHits),
    ("defeq_cache_misses", jsonNat stats.defEqCacheMisses),
    ("defeq_cache_entries", jsonNat stats.defEqCacheEntries),
    ("defeq_success_cache_hits", jsonNat stats.defEqSuccessCacheHits),
    ("defeq_success_cache_misses", jsonNat stats.defEqSuccessCacheMisses),
    ("defeq_success_cache_entries", jsonNat stats.defEqSuccessCacheEntries),
    ("defeq_success_cache_dropped", jsonNat stats.defEqSuccessCacheDropped),
    ("constructor_proof_field_skips", jsonNat stats.constructorProofFieldSkips),
    ("defeq_nonalpha_repeat_observations", jsonNat stats.defEqRepeatObservations),
    ("defeq_nonalpha_repeat_hits", jsonNat stats.defEqRepeatHits),
    ("defeq_nonalpha_repeat_dropped", jsonNat stats.defEqRepeatDropped),
    ("defeq_nonalpha_repeat_successes", jsonNat stats.defEqRepeatSuccesses),
    ("defeq_nonalpha_repeat_failures", jsonNat stats.defEqRepeatFailures),
    ("defeq_nonalpha_repeat_hit_successes", jsonNat stats.defEqRepeatHitSuccesses),
    ("defeq_nonalpha_repeat_hit_failures", jsonNat stats.defEqRepeatHitFailures),
    ("defeq_nonalpha_repeat_distinct", jsonNat stats.defEqRepeats.size),
    ("whnf_repeat_observations", jsonNat stats.whnfRepeatObservations),
    ("whnf_repeat_hits", jsonNat stats.whnfRepeatHits),
    ("whnf_repeat_dropped", jsonNat stats.whnfRepeatDropped),
    ("whnf_repeat_distinct", jsonNat stats.whnfRepeats.size),
    ("top_unfold_names", countsJson stats.unfoldNames 30),
    ("top_defeq_head_pairs", countsJson stats.defEqHeadPairs 30),
    ("top_defeq_shape_pairs", countsJson stats.defEqShapePairs 30),
    ("top_defeq_context_depths", countsJson stats.defEqContextDepths 30),
    ("top_structural_head_pairs", countsJson stats.structuralHeadPairs 30),
    ("top_defeq_nonalpha_repeats", repeatsJson stats.defEqRepeats repeatTopLimit),
    ("top_whnf_repeats", repeatsJson stats.whnfRepeats repeatTopLimit),
    ("structural_projection_samples", stringPairsJson stats.structuralProjectionSamples),
    ("structural_lambda_samples", stringPairsJson stats.structuralLambdaSamples)
  ]

def newProfiler (budget traceEvery : Nat)
    (useMemo useRepeatDiag useDefEqSuccessCache : Bool) : IO Profiler := do
  let ref ← IO.mkRef ({} : Stats)
  let markRef ← IO.mkRef "start"
  let whnfCacheRef ← IO.mkRef ({} : Std.HashMap WhnfKey Expr)
  let defEqCacheRef ← IO.mkRef ({} : Std.HashMap DefEqKey Unit)
  let defEqSuccessCacheRef ← IO.mkRef ({} : Std.HashMap DefEqKey Unit)
  pure {
    budget,
    ref,
    markRef,
    whnfCacheRef,
    defEqCacheRef,
    defEqSuccessCacheRef,
    useMemo,
    useRepeatDiag,
    useDefEqSuccessCache,
    traceEvery
  }

def replayProfilerBudget : Nat :=
  10000000000

def addDeclarationWithDefEqSuccessCache (manifest : Manifest) (env : Env)
    (declaration : Declaration) : IO (Result Env) := do
  let profiler ← newProfiler replayProfilerBudget 0 false false true
  (addDeclaration profiler manifest env declaration).run

def profileDeclaration (manifest : Manifest) (env : Env) (budget traceEvery : Nat)
    (useMemo useRepeatDiag useDefEqSuccessCache : Bool)
    (declaration : Declaration) : IO Lean.Json := do
  let profiler ← newProfiler budget traceEvery useMemo useRepeatDiag useDefEqSuccessCache
  let startedMs ← IO.monoMsNow
  let result ← (checkDeclaration profiler manifest env declaration).run
  let stoppedMs ← IO.monoMsNow
  let stats ← profiler.ref.get
  let statusAndMessage :=
    match result with
    | .ok () => ("checked", "")
    | .error err =>
        if err.message.startsWith "dynamic profile budget exhausted" then
          ("budget-exhausted", err.message)
        else
          ("rejected", err.message)
  let fields := [
    ("event", Lean.Json.str "dynamic-profile"),
    ("status", Lean.Json.str statusAndMessage.1),
    ("message", Lean.Json.str statusAndMessage.2),
    ("elapsed_ms", jsonNat (stoppedMs - startedMs)),
    ("budget", jsonNat budget),
    ("trace_every", jsonNat traceEvery),
    ("repeat_diag", Lean.Json.bool useRepeatDiag),
    ("defeq_success_cache", Lean.Json.bool useDefEqSuccessCache),
    ("stats", stats.toJson)
  ]
  pure (Lean.Json.mkObj fields)

end MPC.Adapters.DynamicProfile
