import MPC.Adapters.Export

namespace MPC.CheckExport

inductive TelemetryFormat where
  | off
  | text
  | jsonl
  deriving BEq, Inhabited

structure ReplayOptions where
  trace : Bool := false
  telemetry : TelemetryFormat := .off
  deriving Inhabited

structure Config where
  inputPath : System.FilePath
  limit? : Option Nat := none
  replayOptions : ReplayOptions := {}
  assumeGenerated : Bool := false

def usage : String :=
  "usage: mpc-check-export [<export.ndjson>]\n" ++
  "       mpc-check-export --input <export.ndjson>\n" ++
  "       mpc-check-export [--limit <n>] [--trace] [--stats|--stats-jsonl] [--assume-generated] <export.ndjson>\n" ++
  "       IN=<export.ndjson> mpc-check-export"

def filePath (path : String) : Except String System.FilePath :=
  if path.isEmpty then
    .error "empty input path"
  else
    pure (System.FilePath.mk path)

def configFromPath
    (limit? : Option Nat)
    (replayOptions : ReplayOptions)
    (assumeGenerated : Bool)
    (path : String) :
    Except String Config := do
  pure { inputPath := (← filePath path), limit?, replayOptions, assumeGenerated }

def configFromEnv
    (limit? : Option Nat)
    (replayOptions : ReplayOptions)
    (assumeGenerated : Bool) : IO (Except String Config) := do
  match ← IO.getEnv "IN" with
  | some path => pure (configFromPath limit? replayOptions assumeGenerated path)
  | none => pure (.error "missing input path")

def setInputPath (input? : Option String) (path : String) : Except String (Option String) := do
  if input?.isSome then
    .error "multiple input paths"
  else if path.isEmpty then
    .error "empty input path"
  else
    pure (some path)

def parseNatArgument (label value : String) : Except String Nat :=
  match value.toNat? with
  | some n => pure n
  | none => .error s!"invalid {label}: {value}"

def setTelemetryFormat
    (options : ReplayOptions)
    (format : TelemetryFormat) :
    Except String ReplayOptions :=
  if options.telemetry != .off then
    .error "multiple telemetry formats"
  else
    pure { options with telemetry := format }

partial def parseArgsLoop
    (input? : Option String)
    (limit? : Option Nat)
    (replayOptions : ReplayOptions)
    (assumeGenerated : Bool) :
    List String → Except String (Option String × Option Nat × ReplayOptions × Bool)
  | [] => pure (input?, limit?, replayOptions, assumeGenerated)
  | "--input" :: path :: rest => do
      parseArgsLoop (← setInputPath input? path) limit? replayOptions assumeGenerated rest
  | "--input" :: [] => .error "missing value after --input"
  | "--limit" :: value :: rest => do
      if limit?.isSome then
        .error "multiple limits"
      else
        parseArgsLoop input? (some (← parseNatArgument "limit" value)) replayOptions assumeGenerated rest
  | "--limit" :: [] => .error "missing value after --limit"
  | "--trace" :: rest =>
      parseArgsLoop input? limit? { replayOptions with trace := true } assumeGenerated rest
  | "--stats" :: rest => do
      parseArgsLoop input? limit? (← setTelemetryFormat replayOptions .text) assumeGenerated rest
  | "--stats-jsonl" :: rest => do
      parseArgsLoop input? limit? (← setTelemetryFormat replayOptions .jsonl) assumeGenerated rest
  | "--assume-generated" :: rest =>
      parseArgsLoop input? limit? replayOptions true rest
  | "--help" :: _ => .error usage
  | arg :: rest =>
      if arg.startsWith "-" then
        .error s!"unknown argument: {arg}"
      else do
        parseArgsLoop (← setInputPath input? arg) limit? replayOptions assumeGenerated rest

def parseArgs : List String → IO (Except String Config)
  | args => do
      match parseArgsLoop none none {} false args with
      | .error err => pure (.error err)
      | .ok (some path, limit?, replayOptions, assumeGenerated) =>
          pure (configFromPath limit? replayOptions assumeGenerated path)
      | .ok (none, limit?, replayOptions, assumeGenerated) =>
          configFromEnv limit? replayOptions assumeGenerated

def printOutcome (status : String) (path : System.FilePath) (message : String) : IO Unit := do
  IO.println status
  IO.println s!"artifact: {path}"
  if message != "" then
    IO.println s!"message: {message}"

inductive ReplayStatus where
  | checked
  | rejected

def ReplayStatus.label : ReplayStatus → String
  | .checked => "checked"
  | .rejected => "rejected"

structure DeclarationTelemetry where
  index : Nat
  kind : String
  name : String
  elapsedMs : Nat
  cumulativeMs : Nat
  status : ReplayStatus

def jsonNat (value : Nat) : Lean.Json :=
  Lean.Json.num (Lean.JsonNumber.fromNat value)

def DeclarationTelemetry.toJson (entry : DeclarationTelemetry) : Lean.Json :=
  Lean.Json.mkObj [
    ("event", Lean.Json.str "declaration"),
    ("index", jsonNat entry.index),
    ("kind", Lean.Json.str entry.kind),
    ("name", Lean.Json.str entry.name),
    ("status", Lean.Json.str entry.status.label),
    ("elapsed_ms", jsonNat entry.elapsedMs),
    ("cumulative_ms", jsonNat entry.cumulativeMs)
  ]

def DeclarationTelemetry.text (entry : DeclarationTelemetry) : String :=
  s!"stats: index={entry.index} status={entry.status.label} elapsed_ms={entry.elapsedMs} cumulative_ms={entry.cumulativeMs} kind={entry.kind} name={entry.name}"

def emitDeclarationTelemetry
    (format : TelemetryFormat)
    (entry : DeclarationTelemetry) :
    IO Unit := do
  match format with
  | .off => pure ()
  | .text => IO.println entry.text
  | .jsonl => IO.println entry.toJson.compress
  if format != .off then
    (← IO.getStdout).flush

partial def replayLoop
    (manifest : Manifest)
    (options : ReplayOptions) :
    Nat → Nat → Env → List Declaration → IO (Result Env)
  | _, _, env, [] => pure (.ok env)
  | index, cumulativeMs, env, declaration :: rest => do
      if options.telemetry == .off then
        if options.trace then
          let kind := MPC.Adapters.Export.declarationKindLabel declaration
          let name := MPC.Adapters.Export.declarationNameLabel declaration
          IO.println s!"replay: {index} {kind} {name}"
          (← IO.getStdout).flush
        match addDecl manifest env declaration with
        | .ok env => replayLoop manifest options (index + 1) cumulativeMs env rest
        | .error err =>
            let kind := MPC.Adapters.Export.declarationKindLabel declaration
            let name := MPC.Adapters.Export.declarationNameLabel declaration
            pure (.error { message := s!"while replaying {kind} {name}: {err.message}" })
      else
        let kind := MPC.Adapters.Export.declarationKindLabel declaration
        let name := MPC.Adapters.Export.declarationNameLabel declaration
        if options.trace then
          IO.println s!"replay: {index} {kind} {name}"
          (← IO.getStdout).flush
        let startMs ← IO.monoMsNow
        match addDecl manifest env declaration with
        | .ok env =>
            let stopMs ← IO.monoMsNow
            let elapsedMs := stopMs - startMs
            let cumulativeMs := cumulativeMs + elapsedMs
            emitDeclarationTelemetry options.telemetry {
              index,
              kind,
              name,
              elapsedMs,
              cumulativeMs,
              status := .checked
            }
            replayLoop manifest options (index + 1) cumulativeMs env rest
        | .error err =>
            let stopMs ← IO.monoMsNow
            let elapsedMs := stopMs - startMs
            let cumulativeMs := cumulativeMs + elapsedMs
            emitDeclarationTelemetry options.telemetry {
              index,
              kind,
              name,
              elapsedMs,
              cumulativeMs,
              status := .rejected
            }
            pure (.error { message := s!"while replaying {kind} {name}: {err.message}" })

def generatedSupportAssumptionName (name : Name) : Bool :=
  name.endsWith ".noConfusion" ||
    name.startsWith "noConfusion_of_"

def generatedSupportAssumption : Declaration → Bool
  | .definition name .. => generatedSupportAssumptionName name
  | .theorem name .. => generatedSupportAssumptionName name
  | .opaque name .. => generatedSupportAssumptionName name
  | _ => false

def assumeGeneratedSupport : Declaration → Declaration
  | .definition name levelParams type value =>
      if generatedSupportAssumptionName name then
        .axiom name levelParams type
      else
        .definition name levelParams type value
  | .theorem name levelParams type value =>
      if generatedSupportAssumptionName name then
        .axiom name levelParams type
      else
        .theorem name levelParams type value
  | .opaque name levelParams type value =>
      if generatedSupportAssumptionName name then
        .axiom name levelParams type
      else
        .opaque name levelParams type value
  | declaration => declaration

def prepareDeclarations (config : Config) (state : MPC.Adapters.Export.ParseState) :
    List Declaration :=
  let declarations :=
    match config.limit? with
    | some limit => state.declarations.take limit
    | none => state.declarations
  if config.assumeGenerated then
    declarations.map fun declaration =>
      if generatedSupportAssumption declaration then
        assumeGeneratedSupport declaration
      else
        declaration
  else
    declarations

def generatedAssumptionCount (config : Config) (state : MPC.Adapters.Export.ParseState) : Nat :=
  if config.assumeGenerated then
    (prepareDeclarations { config with assumeGenerated := false } state).filter generatedSupportAssumption |>.length
  else
    0

def replayConfig (config : Config) (state : MPC.Adapters.Export.ParseState) :
    IO (Result Env) := do
  let declarations := prepareDeclarations config state
  match ← replayLoop MPC.Configs.LeanCore429 config.replayOptions 0 0 emptyEnv declarations with
  | .error err => pure (.error err)
  | .ok env =>
      match config.limit? with
      | some _ => pure (.ok env)
      | none =>
          match MPC.Adapters.Export.auditGenerated env state.audit with
          | .ok () => pure (.ok env)
          | .error err => pure (.error err)

def run (args : List String) : IO UInt32 := do
  match ← parseArgs args with
  | .error err => do
      IO.eprintln usage
      if err != usage then
        IO.eprintln s!"error: {err}"
      return 2
  | .ok config => do
      let input ← IO.FS.readFile config.inputPath
      match MPC.Adapters.Export.parseString input with
      | .error err => do
          printOutcome "unsupported" config.inputPath err.message
          return 2
      | .ok state =>
          match ← replayConfig config state with
          | .error err => do
              printOutcome "rejected" config.inputPath err.message
              return 1
          | .ok env => do
              let checked :=
                match config.limit? with
                | some limit => Nat.min limit state.declarations.length
                | none => state.declarations.length
              let prefixText :=
                match config.limit? with
                | some _ => "prefix "
                | none => ""
              let assumptionText :=
                let count := generatedAssumptionCount config state
                if count == 0 then
                  ""
                else
                  s!"; assumed {count} generated-support declarations"
              printOutcome "accepted" config.inputPath s!"checked {prefixText}{checked} declaration entries; environment size {env.length}{assumptionText}"
              return 0

end MPC.CheckExport

def main (args : List String) : IO UInt32 :=
  MPC.CheckExport.run args
