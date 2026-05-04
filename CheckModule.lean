import LeanLean.Export

namespace LeanLean.CheckModule

structure Config where
  moduleName : Lean.Name
  roots : List Lean.Name
  gapReport : Bool

def usage : String :=
  "usage: leanlean-check-module [--gap-report] --module <module> --decl <name> [--decl <name> ...]"

def parseDottedName (label input : String) : Except String Lean.Name := do
  let parts := input.splitOn "."
  if parts.isEmpty || parts.any String.isEmpty then
    .error s!"invalid {label}: {input}"
  else
    pure (parts.foldl Lean.Name.mkStr Lean.Name.anonymous)

partial def parseArgsLoop
    (moduleName? : Option Lean.Name)
    (roots : List Lean.Name)
    (gapReport : Bool) : List String → Except String Config
  | [] =>
      match moduleName?, roots with
      | none, _ => .error "missing --module"
      | some _, [] => .error "missing --decl"
      | some moduleName, roots => pure { moduleName, roots, gapReport }
  | "--module" :: value :: rest => do
      let moduleName ← parseDottedName "module name" value
      parseArgsLoop (some moduleName) roots gapReport rest
  | "--module" :: [] => .error "missing value after --module"
  | "--decl" :: value :: rest => do
      let root ← parseDottedName "declaration name" value
      parseArgsLoop moduleName? (roots ++ [root]) gapReport rest
  | "--decl" :: [] => .error "missing value after --decl"
  | "--gap-report" :: rest => do
      if gapReport then
        .error "multiple gap report flags"
      else
        parseArgsLoop moduleName? roots true rest
  | "--help" :: _ => .error usage
  | arg :: _ => .error s!"unknown argument: {arg}"

def parseArgs (args : List String) : Except String Config :=
  parseArgsLoop none [] false args

def printRoots : List Lean.Name → IO Unit
  | [] => pure ()
  | root :: rest => do
      IO.println s!"root: {root}"
      printRoots rest

def printOutcome (config : Config) (outcome : Checker.Outcome) : IO Unit := do
  IO.println outcome.label
  IO.println s!"module: {config.moduleName}"
  printRoots config.roots
  if outcome.message != "" then
    IO.println s!"message: {outcome.message}"

def constantInfoName : Lean.ConstantInfo → Lean.Name
  | .axiomInfo value => value.name
  | .defnInfo value => value.name
  | .thmInfo value => value.name
  | .opaqueInfo value => value.name
  | .quotInfo value => value.name
  | .inductInfo value => value.name
  | .ctorInfo value => value.name
  | .recInfo value => value.name

def constantInfoKind : Lean.ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def replayPolicySkip (info : Lean.ConstantInfo) : Bool :=
  info.isUnsafe || info.isPartial

def replayPolicySkipReason (info : Lean.ConstantInfo) : String :=
  if info.isUnsafe && info.isPartial then
    "unsafe+partial"
  else if info.isUnsafe then
    "unsafe"
  else
    "partial"

def policySkipLine (info : Lean.ConstantInfo) : String :=
  s!"policy-skip: name={constantInfoName info} kind={constantInfoKind info} \
    reason={replayPolicySkipReason info}"

def joinLines : List String → String
  | [] => ""
  | [line] => line
  | line :: rest => line ++ "\n" ++ joinLines rest

def translateReplayInfos
    (leanEnv : Lean.Environment)
    (infos : List Lean.ConstantInfo) : Result (List Declaration) := do
  let declarations ← Import.translateConstantInfoSnapshot infos
  let structureInfos ← Import.collectEnvironmentStructureInfos leanEnv infos
  let structureDeclarations ← structureInfos.mapM (Import.translateCheckedStructureInfo leanEnv)
  pure (declarations ++ structureDeclarations)

def moduleReplayGapReport
    (leanEnv : Lean.Environment)
    (config : Config) : Checker.Outcome :=
  match Import.collectEnvironmentClosureUnchecked leanEnv config.roots with
  | .error err => .unsupported err
  | .ok infos =>
      let replayInfos := infos.filter fun info => !replayPolicySkip info
      let skippedInfos := infos.filter replayPolicySkip
      match translateReplayInfos leanEnv replayInfos with
      | .error err => .unsupported err
      | .ok declarations =>
          match Export.formatReplayGapReport declarations with
          | .error err => .internalFailure err
          | .ok report =>
              let skipHeader :=
                s!"constant-infos: {infos.length}\n" ++
                s!"replay-policy-skips: {skippedInfos.length}"
              let skipDetails :=
                if skippedInfos.isEmpty then
                  ""
                else
                  "\n" ++ joinLines (skippedInfos.map policySkipLine)
              .accepted (skipHeader ++ "\n" ++ report ++ skipDetails)

def printGapReport (config : Config) (outcome : Checker.Outcome) : IO Unit := do
  match outcome.status with
  | .unsupported | .internalFailure => printOutcome config outcome
  | .accepted | .rejected => do
      IO.println "gap-report"
      IO.println s!"module: {config.moduleName}"
      printRoots config.roots
      if outcome.message != "" then
        IO.println outcome.message

unsafe def run (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error err => do
      IO.eprintln usage
      if err != usage then
        IO.eprintln s!"error: {err}"
      return 2
  | .ok config => do
      match ← Checker.loadModuleEnvironment config.moduleName with
      | .error err =>
          let outcome := Checker.Outcome.unsupported s!"could not load Lean module {config.moduleName}: {err}"
          if config.gapReport then
            printGapReport config outcome
          else
            printOutcome config outcome
          return outcome.exitCode
      | .ok leanEnv =>
          let outcome :=
            if config.gapReport then
              moduleReplayGapReport leanEnv config
            else
              Checker.checkEnvironmentRoots leanEnv config.roots
          if config.gapReport then
            printGapReport config outcome
          else
            printOutcome config outcome
          return outcome.exitCode

end LeanLean.CheckModule

unsafe def main (args : List String) : IO UInt32 :=
  LeanLean.CheckModule.run args
