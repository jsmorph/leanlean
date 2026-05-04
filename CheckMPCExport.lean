import MPC.Adapters.Export

namespace MPC.CheckExport

structure Config where
  inputPath : System.FilePath
  limit? : Option Nat := none
  trace : Bool := false

def usage : String :=
  "usage: mpc-check-export [<export.ndjson>]\n" ++
  "       mpc-check-export --input <export.ndjson>\n" ++
  "       mpc-check-export [--limit <n>] [--trace] <export.ndjson>\n" ++
  "       IN=<export.ndjson> mpc-check-export"

def filePath (path : String) : Except String System.FilePath :=
  if path.isEmpty then
    .error "empty input path"
  else
    pure (System.FilePath.mk path)

def configFromPath (limit? : Option Nat) (trace : Bool) (path : String) :
    Except String Config := do
  pure { inputPath := (← filePath path), limit?, trace }

def configFromEnv (limit? : Option Nat) (trace : Bool) : IO (Except String Config) := do
  match ← IO.getEnv "IN" with
  | some path => pure (configFromPath limit? trace path)
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
    (trace : Bool) :
    List String → Except String (Option String × Option Nat × Bool)
  | [] => pure (input?, limit?, trace)
  | "--input" :: path :: rest => do
      parseArgsLoop (← setInputPath input? path) limit? trace rest
  | "--input" :: [] => .error "missing value after --input"
  | "--limit" :: value :: rest => do
      if limit?.isSome then
        .error "multiple limits"
      else
        parseArgsLoop input? (some (← parseNatArgument "limit" value)) trace rest
  | "--limit" :: [] => .error "missing value after --limit"
  | "--trace" :: rest =>
      parseArgsLoop input? limit? true rest
  | "--help" :: _ => .error usage
  | arg :: rest =>
      if arg.startsWith "-" then
        .error s!"unknown argument: {arg}"
      else do
        parseArgsLoop (← setInputPath input? arg) limit? trace rest

def parseArgs : List String → IO (Except String Config)
  | args => do
      match parseArgsLoop none none false args with
      | .error err => pure (.error err)
      | .ok (some path, limit?, trace) => pure (configFromPath limit? trace path)
      | .ok (none, limit?, trace) => configFromEnv limit? trace

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

def replayConfig (config : Config) (state : MPC.Adapters.Export.ParseState) :
    IO (Result Env) := do
  let declarations :=
    match config.limit? with
    | some limit => state.declarations.take limit
    | none => state.declarations
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
              printOutcome "accepted" config.inputPath s!"checked {prefixText}{checked} declaration entries; environment size {env.length}"
              return 0

end MPC.CheckExport

def main (args : List String) : IO UInt32 :=
  MPC.CheckExport.run args
