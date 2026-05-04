import MPC.Adapters.Export

namespace MPC.CheckExport

structure Config where
  inputPath : System.FilePath
  limit? : Option Nat := none
  trace : Bool := false
  assumeGenerated : Bool := false

def usage : String :=
  "usage: mpc-check-export [<export.ndjson>]\n" ++
  "       mpc-check-export --input <export.ndjson>\n" ++
  "       mpc-check-export [--limit <n>] [--trace] [--assume-generated] <export.ndjson>\n" ++
  "       IN=<export.ndjson> mpc-check-export"

def filePath (path : String) : Except String System.FilePath :=
  if path.isEmpty then
    .error "empty input path"
  else
    pure (System.FilePath.mk path)

def configFromPath
    (limit? : Option Nat)
    (trace assumeGenerated : Bool)
    (path : String) :
    Except String Config := do
  pure { inputPath := (← filePath path), limit?, trace, assumeGenerated }

def configFromEnv
    (limit? : Option Nat)
    (trace assumeGenerated : Bool) : IO (Except String Config) := do
  match ← IO.getEnv "IN" with
  | some path => pure (configFromPath limit? trace assumeGenerated path)
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

partial def parseArgsLoop
    (input? : Option String)
    (limit? : Option Nat)
    (trace assumeGenerated : Bool) :
    List String → Except String (Option String × Option Nat × Bool × Bool)
  | [] => pure (input?, limit?, trace, assumeGenerated)
  | "--input" :: path :: rest => do
      parseArgsLoop (← setInputPath input? path) limit? trace assumeGenerated rest
  | "--input" :: [] => .error "missing value after --input"
  | "--limit" :: value :: rest => do
      if limit?.isSome then
        .error "multiple limits"
      else
        parseArgsLoop input? (some (← parseNatArgument "limit" value)) trace assumeGenerated rest
  | "--limit" :: [] => .error "missing value after --limit"
  | "--trace" :: rest =>
      parseArgsLoop input? limit? true assumeGenerated rest
  | "--assume-generated" :: rest =>
      parseArgsLoop input? limit? trace true rest
  | "--help" :: _ => .error usage
  | arg :: rest =>
      if arg.startsWith "-" then
        .error s!"unknown argument: {arg}"
      else do
        parseArgsLoop (← setInputPath input? arg) limit? trace assumeGenerated rest

def parseArgs : List String → IO (Except String Config)
  | args => do
      match parseArgsLoop none none false false args with
      | .error err => pure (.error err)
      | .ok (some path, limit?, trace, assumeGenerated) =>
          pure (configFromPath limit? trace assumeGenerated path)
      | .ok (none, limit?, trace, assumeGenerated) =>
          configFromEnv limit? trace assumeGenerated

def printOutcome (status : String) (path : System.FilePath) (message : String) : IO Unit := do
  IO.println status
  IO.println s!"artifact: {path}"
  if message != "" then
    IO.println s!"message: {message}"

partial def replayTraceLoop
    (manifest : Manifest) :
    Nat → Env → List Declaration → IO (Result Env)
  | _, env, [] => pure (.ok env)
  | index, env, declaration :: rest => do
      IO.println s!"replay: {index} {MPC.Adapters.Export.declarationKindLabel declaration} {MPC.Adapters.Export.declarationNameLabel declaration}"
      (← IO.getStdout).flush
      match addDecl manifest env declaration with
      | .ok env => replayTraceLoop manifest (index + 1) env rest
      | .error err =>
          pure (.error { message := s!"while replaying {MPC.Adapters.Export.declarationKindLabel declaration} {MPC.Adapters.Export.declarationNameLabel declaration}: {err.message}" })

def generatedSupportAssumptionName (name : Name) : Bool :=
  name.endsWith ".noConfusion" ||
    name.endsWith ".noConfusionType" ||
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
  if config.trace then
    replayTraceLoop MPC.Configs.LeanCore429 0 emptyEnv declarations
  else
    match config.limit? with
    | some _ =>
        pure (MPC.Adapters.Export.replayDeclarations MPC.Configs.LeanCore429 emptyEnv declarations)
    | none =>
        pure (MPC.Adapters.Export.replayParsed MPC.Configs.LeanCore429 state)

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
