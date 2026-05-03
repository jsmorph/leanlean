import LeanLean.Export

namespace LeanLean.CheckExport

structure Config where
  inputPath : System.FilePath

def usage : String :=
  "usage: leanlean-check-export [<export.ndjson>]\n" ++
  "       leanlean-check-export --input <export.ndjson>\n" ++
  "       IN=<export.ndjson> leanlean-check-export"

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

def parseArgs : List String → IO (Except String Config)
  | [] => configFromEnv
  | ["--help"] => pure (.error usage)
  | ["--input", path] => pure (configFromPath path)
  | "--input" :: [] => pure (.error "missing value after --input")
  | [path] => pure (configFromPath path)
  | arg :: _ => pure (.error s!"unknown argument: {arg}")

def printOutcome (config : Config) (outcome : Checker.Outcome) : IO Unit := do
  IO.println outcome.label
  IO.println s!"artifact: {config.inputPath}"
  if outcome.message != "" then
    IO.println s!"message: {outcome.message}"

def run (args : List String) : IO UInt32 := do
  match ← parseArgs args with
  | .error err => do
      IO.eprintln usage
      if err != usage then
        IO.eprintln s!"error: {err}"
      return 2
  | .ok config => do
      let input ← IO.FS.readFile config.inputPath
      let outcome := Export.checkString input
      printOutcome config outcome
      return outcome.exitCode

end LeanLean.CheckExport

def main (args : List String) : IO UInt32 :=
  LeanLean.CheckExport.run args
