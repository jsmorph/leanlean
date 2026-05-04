import LeanLean.Export

namespace LeanLean.CheckExport

inductive ReplayMode where
  | ordered
  | dependencyAware
  deriving DecidableEq

structure Config where
  inputPath : System.FilePath
  replayMode : ReplayMode
  rootsPath? : Option System.FilePath

def usage : String :=
  "usage: leanlean-check-export [--ordered | --dependency-aware] [<export.ndjson>]\n" ++
  "       leanlean-check-export [--ordered | --dependency-aware] --input <export.ndjson>\n" ++
  "       leanlean-check-export --self-check-roots <roots.txt> [<export.ndjson>]\n" ++
  "       IN=<export.ndjson> leanlean-check-export [--ordered | --dependency-aware]"

def filePath (path : String) : Except String System.FilePath :=
  if path.isEmpty then
    .error "empty input path"
  else
    pure (System.FilePath.mk path)

def configFromPath
    (replayMode : ReplayMode)
    (rootsPath? : Option System.FilePath)
    (path : String) : Except String Config := do
  pure { inputPath := (← filePath path), replayMode, rootsPath? }

def configFromEnv
    (replayMode : ReplayMode)
    (rootsPath? : Option System.FilePath) : IO (Except String Config) := do
  match ← IO.getEnv "IN" with
  | some path => pure (configFromPath replayMode rootsPath? path)
  | none => pure (.error "missing input path")

def setInputPath (input? : Option String) (path : String) : Except String (Option String) := do
  if input?.isSome then
    .error "multiple input paths"
  else
    if path.isEmpty then
      .error "empty input path"
    else
      pure (some path)

def setReplayMode (mode? : Option ReplayMode) (newMode : ReplayMode) :
    Except String (Option ReplayMode) := do
  match mode? with
  | none => pure (some newMode)
  | some mode =>
      if mode == newMode then
        pure mode?
      else
        .error "multiple replay modes"

partial def parseArgsLoop
    (input? : Option String)
    (mode? : Option ReplayMode)
    (rootsPath? : Option System.FilePath) :
    List String → Except String (Option String × Option ReplayMode × Option System.FilePath)
  | [] => pure (input?, mode?, rootsPath?)
  | "--ordered" :: rest => do
      parseArgsLoop input? (← setReplayMode mode? .ordered) rootsPath? rest
  | "--dependency-aware" :: rest => do
      parseArgsLoop input? (← setReplayMode mode? .dependencyAware) rootsPath? rest
  | "--self-check-roots" :: path :: rest => do
      if rootsPath?.isSome then
        .error "multiple self-check root files"
      else
        parseArgsLoop input? mode? (some (← filePath path)) rest
  | "--self-check-roots" :: [] => .error "missing value after --self-check-roots"
  | "--input" :: path :: rest => do
      parseArgsLoop (← setInputPath input? path) mode? rootsPath? rest
  | "--input" :: [] => .error "missing value after --input"
  | "--help" :: _ => .error usage
  | arg :: rest =>
      if arg.startsWith "-" then
        .error s!"unknown argument: {arg}"
      else do
        parseArgsLoop (← setInputPath input? arg) mode? rootsPath? rest

def parseArgs : List String → IO (Except String Config)
  | args => do
      match parseArgsLoop none none none args with
      | .error err => pure (.error err)
      | .ok (some path, mode?, rootsPath?) =>
          pure (configFromPath (mode?.getD .ordered) rootsPath? path)
      | .ok (none, mode?, rootsPath?) => configFromEnv (mode?.getD .ordered) rootsPath?

def parseRootFile (path : System.FilePath) : IO (Except String (List Name)) := do
  try
    let input ← IO.FS.readFile path
    let roots :=
      (input.splitOn "\n").filterMap fun line =>
        let trimmed := line.trimAscii.toString
        if trimmed.isEmpty then none else some trimmed
    pure (.ok roots)
  catch err =>
    pure (.error err.toString)

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
      match config.rootsPath? with
      | some rootsPath =>
          if config.replayMode != .ordered then
            IO.eprintln "error: --self-check-roots requires ordered replay"
            return 2
          match ← parseRootFile rootsPath with
          | .error err => do
              IO.eprintln s!"error: could not read self-check roots {rootsPath}: {err}"
              return 2
          | .ok roots => do
              if roots.isEmpty then
                IO.eprintln s!"error: self-check root file is empty: {rootsPath}"
                return 2
              let outcome := Export.checkStringWithRootAssumptions input roots
              printOutcome config outcome
              return outcome.exitCode
      | none =>
          let outcome :=
            match config.replayMode with
            | .ordered => Export.checkStringOrdered input
            | .dependencyAware => Export.checkStringDependencyAware input
          printOutcome config outcome
          return outcome.exitCode

end LeanLean.CheckExport

def main (args : List String) : IO UInt32 :=
  LeanLean.CheckExport.run args
