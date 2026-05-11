import MPC.Adapters.DynamicProfile
import MPC.Adapters.Layer

namespace MPC.DynamicProfileExport

structure Config where
  inputPath : System.FilePath
  cacheLayerPath : System.FilePath
  declarationIndex : Nat
  budget : Nat := 1000000
  traceEvery : Nat := 100000
  useMemo : Bool := false
  useRepeatDiag : Bool := false
  useDefEqSuccessCache : Bool := false

def usage : String :=
  "usage: mpc-dynamic-profile-export --cache-layer <layer.db> --declaration <n> [--budget <n>] [--trace-every <n>] [--memo] [--repeat-diag] [--defeq-success-cache] <export.ndjson>"

def filePath (path : String) : Except String System.FilePath :=
  if path.isEmpty then
    .error "empty path"
  else
    pure (System.FilePath.mk path)

def parseNatArgument (label value : String) : Except String Nat :=
  match value.toNat? with
  | some n => pure n
  | none => .error s!"invalid {label}: {value}"

def setInputPath (input? : Option String) (path : String) :
    Except String (Option String) := do
  if input?.isSome then
    .error "multiple input paths"
  else
    pure (some path)

partial def parseArgsLoop
    (input? : Option String) (cacheLayerPath? : Option System.FilePath)
    (declarationIndex? : Option Nat) (budget traceEvery : Nat)
    (useMemo useRepeatDiag useDefEqSuccessCache : Bool) :
    List String →
      Except String
        (Option String × Option System.FilePath × Option Nat × Nat × Nat × Bool × Bool × Bool)
  | [] =>
      pure
        (input?, cacheLayerPath?, declarationIndex?, budget, traceEvery, useMemo,
          useRepeatDiag, useDefEqSuccessCache)
  | "--cache-layer" :: path :: rest => do
      if cacheLayerPath?.isSome then
        .error "multiple cache layers"
      else
        parseArgsLoop input? (some (← filePath path)) declarationIndex? budget traceEvery
          useMemo useRepeatDiag useDefEqSuccessCache rest
  | "--cache-layer" :: [] => .error "missing value after --cache-layer"
  | "--declaration" :: value :: rest => do
      if declarationIndex?.isSome then
        .error "multiple declaration indexes"
      else
        parseArgsLoop input? cacheLayerPath?
          (some (← parseNatArgument "declaration index" value)) budget traceEvery
          useMemo useRepeatDiag useDefEqSuccessCache rest
  | "--declaration" :: [] => .error "missing value after --declaration"
  | "--budget" :: value :: rest => do
      parseArgsLoop input? cacheLayerPath? declarationIndex?
        (← parseNatArgument "budget" value) traceEvery useMemo useRepeatDiag
        useDefEqSuccessCache rest
  | "--budget" :: [] => .error "missing value after --budget"
  | "--trace-every" :: value :: rest => do
      parseArgsLoop input? cacheLayerPath? declarationIndex? budget
        (← parseNatArgument "trace interval" value) useMemo useRepeatDiag
        useDefEqSuccessCache rest
  | "--trace-every" :: [] => .error "missing value after --trace-every"
  | "--memo" :: rest =>
      parseArgsLoop input? cacheLayerPath? declarationIndex? budget traceEvery true
        useRepeatDiag useDefEqSuccessCache rest
  | "--repeat-diag" :: rest =>
      parseArgsLoop input? cacheLayerPath? declarationIndex? budget traceEvery useMemo
        true useDefEqSuccessCache rest
  | "--defeq-success-cache" :: rest =>
      parseArgsLoop input? cacheLayerPath? declarationIndex? budget traceEvery useMemo
        useRepeatDiag true rest
  | "--help" :: _ => .error usage
  | arg :: rest => do
      if arg.startsWith "-" then
        .error s!"unknown argument: {arg}"
      else
        parseArgsLoop (← setInputPath input? arg) cacheLayerPath? declarationIndex?
          budget traceEvery useMemo useRepeatDiag useDefEqSuccessCache rest

def parseArgs (args : List String) : Except String Config := do
  let (input?, cacheLayerPath?, declarationIndex?, budget, traceEvery, useMemo,
    useRepeatDiag, useDefEqSuccessCache) ←
    parseArgsLoop none none none 1000000 100000 false false false args
  let some input := input?
    | .error "missing input path"
  let some cacheLayerPath := cacheLayerPath?
    | .error "missing cache layer"
  let some declarationIndex := declarationIndex?
    | .error "missing declaration index"
  pure {
    inputPath := (← filePath input),
    cacheLayerPath,
    declarationIndex,
    budget,
    traceEvery,
    useMemo,
    useRepeatDiag,
    useDefEqSuccessCache
  }

def replayStatusLabel : MPC.Adapters.Layer.ReplayStepStatus → String
  | .started => "started"
  | .reused => "reused"
  | .checked => "checked"
  | .rejected => "rejected"

def emitReplayProgress (step : MPC.Adapters.Layer.ReplayStep) : IO Unit := do
  IO.eprintln s!"{step.timestampMs}\t{step.index}\t{replayStatusLabel step.status}\t{step.elapsedMs}\t{MPC.Adapters.Export.declarationKindLabel step.declaration}\t{MPC.Adapters.Export.declarationNameLabel step.declaration}"

partial def replayPrefixLoop (config : Config) (handle : IO.FS.Handle)
    (lineNumber : Nat) (parseState : MPC.Adapters.Export.State)
    (replayState : MPC.Adapters.Layer.SqliteOnDemandReplayState) :
    IO (Result (Env × Declaration)) := do
  let line ← handle.getLine
  if line == "" then
    pure (.error {
      message := s!"declaration index {config.declarationIndex} is out of range"
    })
  else
    match MPC.Adapters.Export.parseLineEvent lineNumber parseState line with
    | .error err => pure (.error err)
    | .ok (parseState, event) =>
        let mut replayState := replayState
        for declaration in event.declarations do
          if replayState.index == config.declarationIndex then
            IO.eprintln s!"profiling\t{replayState.index}\t{MPC.Adapters.Export.declarationKindLabel declaration}\t{MPC.Adapters.Export.declarationNameLabel declaration}"
            return .ok (replayState.env, declaration)
          match ←
              MPC.Adapters.Layer.replaySqliteOnDemandStep MPC.Configs.LeanCore429
                config.cacheLayerPath (some emitReplayProgress) true replayState declaration with
          | .error err => return .error err
          | .ok nextState => replayState := nextState
        replayPrefixLoop config handle (lineNumber + 1) parseState replayState

def runProfile (config : Config) : IO (Result Lean.Json) := do
  if !MPC.Adapters.Layer.sqlitePath config.cacheLayerPath then
    pure (.error { message := "--cache-layer requires a SQLite layer path" })
  else
    match ← MPC.Adapters.Layer.ensureSqliteOnDemandLayer config.cacheLayerPath with
    | .error err => pure (.error err)
    | .ok () =>
        match ← IO.FS.withFile config.inputPath .read fun handle =>
            replayPrefixLoop config handle 1 {} {} with
        | .error err => pure (.error {
            message := s!"while replaying cached prefix {config.cacheLayerPath}: {err.message}"
          })
        | .ok (env, declaration) => do
            let json ←
              MPC.Adapters.DynamicProfile.profileDeclaration
                MPC.Configs.LeanCore429 env config.budget config.traceEvery config.useMemo
                config.useRepeatDiag config.useDefEqSuccessCache declaration
            pure (.ok json)

def run (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error err => do
      IO.eprintln usage
      if err != usage then
        IO.eprintln s!"error: {err}"
      return 2
  | .ok config =>
      match ← runProfile config with
      | .ok json => do
          IO.println json.compress
          return 0
      | .error err => do
          IO.println "rejected"
          IO.println s!"artifact: {config.inputPath}"
          IO.println s!"message: {err.message}"
          return 1

end MPC.DynamicProfileExport

def main (args : List String) : IO UInt32 :=
  MPC.DynamicProfileExport.run args
