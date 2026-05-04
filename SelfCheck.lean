import LeanLean.Checker

namespace LeanLean.SelfCheck

structure ModuleTarget where
  moduleName : Lean.Name
  roots : List Lean.Name

structure RootResult where
  moduleName : Lean.Name
  root : Lean.Name
  outcome : Checker.Outcome

structure ModuleRoots where
  roots : List Lean.Name
  skipped : Nat

inductive Mode where
  | targetClosure
  | moduleClosure
  | roots : Bool → Bool → Mode

def targets : List ModuleTarget :=
  [
    {
      moduleName := `LeanLean.Syntax
      roots := [`LeanLean.Name, `LeanLean.Level, `LeanLean.Literal, `LeanLean.Expr, `LeanLean.Level.defEq]
    },
    {
      moduleName := `LeanLean.Kernel
      roots :=
        [
          `LeanLean.LevelContext,
          `LeanLean.Telescope,
          `LeanLean.Context,
          `LeanLean.Result,
          `LeanLean.Env,
          `LeanLean.Binder,
          `LeanLean.checkDefEqIn,
          `LeanLean.replayDeclarations
        ]
    }
  ]

def usage : String :=
  "usage: leanlean-self-check [--module-closure | --roots [--all] [--first-failure]]"

def parseArgs : List String → Except String Mode
  | [] => pure .targetClosure
  | ["--module-closure"] => pure .moduleClosure
  | ["--roots"] => pure (.roots false false)
  | ["--roots", "--all"] => pure (.roots true false)
  | ["--roots", "--first-failure"] => pure (.roots false true)
  | ["--roots", "--all", "--first-failure"] => pure (.roots true true)
  | ["--roots", "--first-failure", "--all"] => pure (.roots true true)
  | ["--help"] => .error usage
  | arg :: _ => .error s!"unknown argument: {arg}"

def generatedSupportName (name : Lean.Name) : Bool :=
  let text := toString name
  text.contains "._" ||
    text.contains "_proof_" ||
    text.contains "_unsafe_rec" ||
    text.contains ".match_" ||
    text.contains ".noConfusion" ||
    text.endsWith ".ctorElim" ||
    text.contains "_sparseCasesOn_" ||
    text.contains "._sparseCasesOn_" ||
    text.contains ".repr" ||
    text.contains ".instDecidable" ||
    text.contains ".instRepr" ||
    text.contains ".instInhabited" ||
    text.contains ".instBEq" ||
    text.startsWith "LeanLean.inst"

def leanAuxSupportName (env : Lean.Environment) (name : Lean.Name) : Bool :=
  let text := toString name
  Lean.isAuxRecursor env name ||
    (text.contains ".brecOn" && (text.endsWith ".go" || text.endsWith ".eq"))

def recursiveAuxSupportName (env : Lean.Environment) (name : Lean.Name) : Bool :=
  let text := toString name
  (Lean.isAuxRecursor env name && (text.endsWith ".brecOn" || text.endsWith ".below")) ||
    (text.contains ".brecOn" && (text.endsWith ".go" || text.endsWith ".eq"))

def trustedRoot? (env : Lean.Environment) : Lean.ConstantInfo → Bool
  | .defnInfo value =>
      value.safety == .safe &&
        !generatedSupportName value.name &&
        !leanAuxSupportName env value.name
  | .ctorInfo value => !value.isUnsafe
  | .recInfo value => !value.isUnsafe
  | .inductInfo value => !value.isUnsafe
  | .axiomInfo value => !value.isUnsafe && !generatedSupportName value.name
  | .opaqueInfo value => !value.isUnsafe && !generatedSupportName value.name
  | .thmInfo _ => false
  | _ => true

def checkSelfCheckConstantSafety : Lean.ConstantInfo → Except String Unit
  | .axiomInfo value =>
      if value.isUnsafe then
        .error s!"self-check rejects unsafe axiom dependency: {value.name}"
      else
        pure ()
  | .defnInfo value =>
      match value.safety with
      | .safe => pure ()
      | .«unsafe» => .error s!"self-check rejects unsafe definition dependency: {value.name}"
      | .«partial» => .error s!"self-check rejects partial definition dependency: {value.name}"
  | .opaqueInfo value =>
      if value.isUnsafe then
        .error s!"self-check rejects unsafe opaque dependency: {value.name}"
      else
        pure ()
  | .inductInfo value =>
      if value.isUnsafe then
        .error s!"self-check rejects unsafe inductive dependency: {value.name}"
      else
        pure ()
  | .ctorInfo value =>
      if value.isUnsafe then
        .error s!"self-check rejects unsafe constructor dependency: {value.name}"
      else
        pure ()
  | .recInfo value =>
      if value.isUnsafe then
        .error s!"self-check rejects unsafe recursor dependency: {value.name}"
      else
        pure ()
  | _ => pure ()

def moduleRoots (env : Lean.Environment) (moduleName : Lean.Name) :
    Except String ModuleRoots := do
  let some moduleIdx := env.getModuleIdx? moduleName
    | .error s!"module is not loaded: {moduleName}"
  if h : moduleIdx.toNat < env.header.moduleData.size then
    let data := env.header.moduleData[moduleIdx.toNat]
    let names := (data.constNames.qsort fun left right => left.quickCmp right == .lt).toList
    let roots :=
      names.filter fun name =>
        match env.find? name with
        | some info => trustedRoot? env info
        | none => false
    pure { roots, skipped := names.length - roots.length }
  else
    .error s!"module data is missing for {moduleName}"

def rootContains (roots : List Lean.Name) (name : Lean.Name) : Bool :=
  roots.any fun root => root == name

partial def appendStructureRootDependencies
    (env : Lean.Environment)
    (pending seen : List Lean.Name) : List Lean.Name :=
  match pending with
  | [] => seen
  | root :: rest =>
      if seen.any fun existing => existing == root then
        appendStructureRootDependencies env rest seen
      else
        let dependencies :=
          match env.find? root with
          | some (.inductInfo value) =>
              match Lean.getStructureInfo? env value.name with
              | some info => Import.leanStructureInfoConstants info
              | none => []
          | _ => []
        let pending := Import.appendLeanNames rest dependencies
        appendStructureRootDependencies env pending (seen ++ [root])

def selfCheckAssumption? (env : Lean.Environment) (roots : List Lean.Name) (info : Lean.ConstantInfo) : Bool :=
  if rootContains roots info.name then
    false
  else if generatedSupportName info.name then
    true
  else if recursiveAuxSupportName env info.name then
    false
  else if leanAuxSupportName env info.name then
    true
  else if (env.getProjectionFnInfo? info.name).isSome then
    false
  else
    match info with
    | .defnInfo value =>
        match value.hints with
        | .abbrev => false
        | _ => true
    | .inductInfo _ | .ctorInfo _ | .recInfo _ | .quotInfo _ => false
    | _ => true

def assumeConstantInfo : Lean.ConstantInfo → Lean.ConstantInfo
  | .axiomInfo value => .axiomInfo { value with isUnsafe := false }
  | .defnInfo value =>
      .axiomInfo
        {
          name := value.name
          levelParams := value.levelParams
          type := value.type
          isUnsafe := false
        }
  | .thmInfo value =>
      .axiomInfo
        {
          name := value.name
          levelParams := value.levelParams
          type := value.type
          isUnsafe := false
        }
  | .opaqueInfo value =>
      .axiomInfo
        {
          name := value.name
          levelParams := value.levelParams
          type := value.type
          isUnsafe := false
        }
  | info => info

def trustedDefinitionValueNeeded (name : Lean.Name) : Bool :=
  name == `outParam ||
    name == `semiOutParam ||
    name == `optParam ||
    name == `Nat.add ||
    name == `Nat.mul ||
    name == `Nat.pow ||
    name == `Nat.sub ||
    name == `Nat.beq ||
    name == `Nat.ble ||
    name == `DecidableEq

def selfCheckTrustedInfo (env : Lean.Environment) (roots : List Lean.Name) (info : Lean.ConstantInfo) :
    Lean.ConstantInfo :=
  if selfCheckAssumption? env roots info then
    match info with
    | .defnInfo value =>
        if trustedDefinitionValueNeeded value.name then
          info
        else
          assumeConstantInfo info
    | _ => assumeConstantInfo info
  else
    info

def translateTrustedBaseInfo? : Lean.ConstantInfo → Except String (Option ConstantInfo)
  | .axiomInfo value => do
      pure
        (some
          (ConstantInfo.mkAxiom
            (Import.translateName value.name)
            (Import.translateLevelParams value.levelParams)
            (← Import.translateExpr value.type)))
  | .defnInfo value => do
      pure
        (some
          (ConstantInfo.mkDefnWithHint
            (Import.translateName value.name)
            (Import.translateLevelParams value.levelParams)
            (← Import.translateExpr value.type)
            (← Import.translateExpr value.value)
            (Import.translateReducibilityHints value.hints)))
  | .thmInfo value => do
      pure
        (some
          (ConstantInfo.mkAxiom
            (Import.translateName value.name)
            (Import.translateLevelParams value.levelParams)
            (← Import.translateExpr value.type)))
  | .opaqueInfo value => do
      pure
        (some
          (ConstantInfo.mkOpaqueDefn
            (Import.translateName value.name)
            (Import.translateLevelParams value.levelParams)
            (← Import.translateExpr value.type)
            (← Import.translateExpr value.value)))
  | .inductInfo value => do
      pure
        (some
          (ConstantInfo.mkAxiom
            (Import.translateName value.name)
            (Import.translateLevelParams value.levelParams)
            (← Import.translateExpr value.type)))
  | .ctorInfo value => do
      pure
        (some
          (ConstantInfo.mkAxiom
            (Import.translateName value.name)
            (Import.translateLevelParams value.levelParams)
            (← Import.translateExpr value.type)))
  | .recInfo value => do
      pure
        (some
          (ConstantInfo.mkAxiom
            (Import.translateName value.name)
            (Import.translateLevelParams value.levelParams)
            (← Import.translateExpr value.type)))
  | .quotInfo value => do
      pure
        (some
          (ConstantInfo.mkPrimitive
            (Import.translateName value.name)
            (Import.translateLevelParams value.levelParams)
            (← Import.translateExpr value.type)
            (Import.translateQuotKind value.kind)))

def selfCheckDependencyNames
    (env : Lean.Environment)
    (roots : List Lean.Name)
    (info : Lean.ConstantInfo) : List Lean.Name :=
  if selfCheckAssumption? env roots info then
    match info with
    | .defnInfo _ | .opaqueInfo _ => Import.constantInfoDependencyNames info
    | _ => Import.leanExprConstants info.type
  else
    Import.environmentConstantInfoDependencyNames env info

partial def collectSelfCheckClosure
    (env : Lean.Environment)
    (roots : List Lean.Name) : Except String (List Lean.ConstantInfo) := do
  let rec loop
      (pending seen : List Lean.Name)
      (infos : List Lean.ConstantInfo) : Except String (List Lean.ConstantInfo) := do
    match pending with
    | [] => pure infos.reverse
    | name :: rest =>
        if seen.any fun existing => existing == name then
          loop rest seen infos
        else
          let some info := env.find? name
            | .error s!"unknown Lean environment constant in self-check closure: {name}"
          let _ ← checkSelfCheckConstantSafety info
          let dependencies := selfCheckDependencyNames env roots info
          let pending := Import.appendLeanNames rest dependencies
          loop pending (name :: seen) (selfCheckTrustedInfo env roots info :: infos)
  loop roots [] []

def translateSelfCheckClosure
    (env : Lean.Environment)
    (roots : List Lean.Name) : Except String (Env × List Declaration) := do
  let roots := appendStructureRootDependencies env roots []
  let infos ← collectSelfCheckClosure env roots
  let mut trustedBase : Env := []
  let mut replayInfos : List Lean.ConstantInfo := []
  for info in infos do
    if selfCheckAssumption? env roots info then
      match ← translateTrustedBaseInfo? info with
      | some localInfo => trustedBase := localInfo :: trustedBase
      | none => replayInfos := replayInfos ++ [info]
    else
      replayInfos := replayInfos ++ [info]
  let declarations ← Import.translateConstantInfoSnapshot replayInfos
  let structureInfos ← Import.collectEnvironmentStructureInfos env replayInfos
  let structureInfos := structureInfos.filter fun info => rootContains roots info.structName
  let structureDeclarations ← structureInfos.mapM (Import.translateCheckedStructureInfo env)
  pure (trustedBase, declarations ++ structureDeclarations)

def checkSelfCheckRoots (env : Lean.Environment) (roots : List Lean.Name) : Checker.Outcome :=
  match translateSelfCheckClosure env roots with
  | .error err => .unsupported err
  | .ok (trustedBase, declarations) =>
      match replayDeclarations trustedBase declarations with
      | .ok _ => .accepted s!"checked {declarations.length} declaration entries"
      | .error err => .rejected err

def checkModule (env : Lean.Environment) (moduleName : Lean.Name) :
    List RootResult :=
  match moduleRoots env moduleName with
  | .error err =>
      [
        {
          moduleName
          root := moduleName
          outcome := Checker.Outcome.internalFailure err
        }
      ]
  | .ok moduleRoots =>
      moduleRoots.roots.map fun root =>
        {
          moduleName
          root
          outcome := checkSelfCheckRoots env [root]
        }

def checkModuleClosure (env : Lean.Environment) (moduleName : Lean.Name) :
    RootResult :=
  match moduleRoots env moduleName with
  | .error err =>
      {
        moduleName
        root := moduleName
        outcome := Checker.Outcome.internalFailure err
      }
  | .ok moduleRoots =>
      {
        moduleName
        root := moduleName
        outcome :=
          match checkSelfCheckRoots env moduleRoots.roots with
          | outcome =>
              { outcome with
                message := s!"{outcome.message}; skipped {moduleRoots.skipped} non-kernel-facing roots" }
      }

unsafe def checkTarget (target : ModuleTarget) : IO (List RootResult) := do
  match ← Checker.loadModuleEnvironment target.moduleName with
  | .ok env => pure (checkModule env target.moduleName)
  | .error err =>
      pure
        [
          {
            moduleName := target.moduleName
            root := target.moduleName
            outcome := Checker.Outcome.internalFailure s!"could not load module: {err}"
          }
        ]

unsafe def checkTargetUntilFailure (target : ModuleTarget) : IO (List RootResult) := do
  match ← Checker.loadModuleEnvironment target.moduleName with
  | .error err =>
      pure
        [
          {
            moduleName := target.moduleName
            root := target.moduleName
            outcome := Checker.Outcome.internalFailure s!"could not load module: {err}"
          }
        ]
  | .ok env =>
      match moduleRoots env target.moduleName with
      | .error err =>
          pure
            [
              {
                moduleName := target.moduleName
                root := target.moduleName
                outcome := Checker.Outcome.internalFailure err
              }
            ]
      | .ok moduleRoots =>
          let mut results := []
          for root in moduleRoots.roots do
            let result :=
              {
                moduleName := target.moduleName
                root
                outcome := checkSelfCheckRoots env [root]
              }
            results := results ++ [result]
            if result.outcome.status != .accepted then
              return results
          pure results

unsafe def checkTargetClosure (target : ModuleTarget) : IO RootResult := do
  match ← Checker.loadModuleEnvironment target.moduleName with
  | .ok env => pure (checkModuleClosure env target.moduleName)
  | .error err =>
      pure
        {
          moduleName := target.moduleName
          root := target.moduleName
          outcome := Checker.Outcome.internalFailure s!"could not load module: {err}"
        }

unsafe def checkTargetSelectedRoots (target : ModuleTarget) : IO RootResult := do
  match ← Checker.loadModuleEnvironment target.moduleName with
  | .error err =>
      pure
        {
          moduleName := target.moduleName
          root := target.moduleName
          outcome := Checker.Outcome.internalFailure s!"could not load module: {err}"
        }
  | .ok env =>
      let missing := target.roots.filter fun root => (env.find? root).isNone
      if !missing.isEmpty then
        pure
          {
            moduleName := target.moduleName
            root := target.moduleName
            outcome := Checker.Outcome.internalFailure s!"missing configured roots: {repr missing}"
          }
      else
        pure
          {
            moduleName := target.moduleName
            root := target.moduleName
            outcome :=
              match checkSelfCheckRoots env target.roots with
              | outcome =>
                  { outcome with
                    message := s!"{outcome.message}; roots {repr target.roots}" }
          }

def statusCount (status : Checker.Status) (results : List RootResult) : Nat :=
  results.foldl
    (fun count result =>
      if result.outcome.status == status then count + 1 else count)
    0

def resultLine (result : RootResult) : String :=
  s!"{result.outcome.label}: {result.moduleName}:{result.root}: {result.outcome.message}"

def printResult (result : RootResult) : IO Unit :=
  IO.println (resultLine result)

def printModuleSummary (moduleName : Lean.Name) (results : List RootResult) : IO Unit := do
  IO.println
    s!"module {moduleName}: {statusCount .accepted results} accepted, \
      {statusCount .rejected results} rejected, \
      {statusCount .unsupported results} unsupported, \
      {statusCount .internalFailure results} internal"

def printResults (showAll : Bool) (results : List RootResult) : IO Unit := do
  let moduleNames :=
    results.foldl
      (fun names result =>
        if names.any (· == result.moduleName) then names else names ++ [result.moduleName])
      []
  for moduleName in moduleNames do
    let moduleResults := results.filter (·.moduleName == moduleName)
    printModuleSummary moduleName moduleResults
  for result in results do
    if showAll || result.outcome.status != .accepted then
      printResult result

unsafe def run (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error err => do
      IO.eprintln usage
      if err != usage then
        IO.eprintln s!"error: {err}"
      return 2
  | .ok mode => do
      let mut results := []
      let showAll :=
        match mode with
        | .targetClosure => true
        | .moduleClosure => true
        | .roots showAll _ => showAll
      match mode with
      | .targetClosure =>
          for target in targets do
            results := results ++ [← checkTargetSelectedRoots target]
      | .moduleClosure =>
          for target in targets do
            results := results ++ [← checkTargetClosure target]
      | .roots _ true =>
          for target in targets do
            results := results ++ (← checkTargetUntilFailure target)
      | .roots _ false =>
          for target in targets do
            results := results ++ (← checkTarget target)
      printResults showAll results
      if results.all fun result => result.outcome.status == .accepted then
        return 0
      else
        return 1

end LeanLean.SelfCheck

unsafe def main (args : List String) : IO UInt32 :=
  LeanLean.SelfCheck.run args
