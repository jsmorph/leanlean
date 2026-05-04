import MPC.Adapters.Export

namespace MPC.CheckExport

structure Config where
  inputPath : System.FilePath

def usage : String :=
  "usage: mpc-check-export [<export.ndjson>]\n" ++
  "       mpc-check-export --input <export.ndjson>\n" ++
  "       IN=<export.ndjson> mpc-check-export"

def filePath (path : String) : Except String System.FilePath :=
  if path.isEmpty then
    .error "empty input path"
  else
    pure (System.FilePath.mk path)

def configFromPath (path : String) : Except String Config := do
  pure { inputPath := (← filePath path) }

def configFromEnv : IO (Except String Config) := do
  match ← IO.getEnv "IN" with
  | some path => pure (configFromPath path)
  | none => pure (.error "missing input path")

def setInputPath (input? : Option String) (path : String) : Except String (Option String) := do
  if input?.isSome then
    .error "multiple input paths"
  else if path.isEmpty then
    .error "empty input path"
  else
    pure (some path)

partial def parseArgsLoop (input? : Option String) :
    List String → Except String (Option String)
  | [] => pure input?
  | "--input" :: path :: rest => do
      parseArgsLoop (← setInputPath input? path) rest
  | "--input" :: [] => .error "missing value after --input"
  | "--help" :: _ => .error usage
  | arg :: rest =>
      if arg.startsWith "-" then
        .error s!"unknown argument: {arg}"
      else do
        parseArgsLoop (← setInputPath input? arg) rest

def parseArgs : List String → IO (Except String Config)
  | args => do
      match parseArgsLoop none args with
      | .error err => pure (.error err)
      | .ok (some path) => pure (configFromPath path)
      | .ok none => configFromEnv

def printOutcome (status : String) (path : System.FilePath) (message : String) : IO Unit := do
  IO.println status
  IO.println s!"artifact: {path}"
  if message != "" then
    IO.println s!"message: {message}"

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
          match MPC.Adapters.Export.replayParsed MPC.Configs.LeanCore429 state with
          | .error err => do
              printOutcome "rejected" config.inputPath err.message
              return 1
          | .ok env => do
              printOutcome "accepted" config.inputPath s!"checked {state.declarations.length} declaration entries; environment size {env.length}"
              return 0

end MPC.CheckExport

def main (args : List String) : IO UInt32 :=
  MPC.CheckExport.run args
