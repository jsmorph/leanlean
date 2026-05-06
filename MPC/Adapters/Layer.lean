import MPC.Adapters.Export
import Std.Data.HashMap

namespace MPC.Adapters.Layer

deriving instance Lean.ToJson, Lean.FromJson for Level
deriving instance Lean.ToJson, Lean.FromJson for Literal
deriving instance Lean.ToJson, Lean.FromJson for Expr
deriving instance Lean.ToJson, Lean.FromJson for Binder
deriving instance Lean.ToJson, Lean.FromJson for SimpleConstructorSpec
deriving instance Lean.ToJson, Lean.FromJson for SimpleInductiveSpec
deriving instance Lean.ToJson, Lean.FromJson for InductiveBlockSpec
deriving instance Lean.ToJson, Lean.FromJson for IndexedConstructorSpec
deriving instance Lean.ToJson, Lean.FromJson for IndexedInductiveSpec
deriving instance Lean.ToJson, Lean.FromJson for SimpleRecursiveFieldInfo
deriving instance Lean.ToJson, Lean.FromJson for SimpleRecursorConstructorInfo
deriving instance Lean.ToJson, Lean.FromJson for SimpleRecursorInfo
deriving instance Lean.ToJson, Lean.FromJson for MutualRecursiveFieldInfo
deriving instance Lean.ToJson, Lean.FromJson for MutualRecursorConstructorInfo
deriving instance Lean.ToJson, Lean.FromJson for MutualRecursorInfo
deriving instance Lean.ToJson, Lean.FromJson for IndexedRecursiveFieldInfo
deriving instance Lean.ToJson, Lean.FromJson for IndexedRecursorConstructorInfo
deriving instance Lean.ToJson, Lean.FromJson for IndexedRecursorInfo
deriving instance Lean.ToJson, Lean.FromJson for NestedRecursiveFieldInfo
deriving instance Lean.ToJson, Lean.FromJson for NestedRecursorConstructorInfo
deriving instance Lean.ToJson, Lean.FromJson for NestedRecursorTargetInfo
deriving instance Lean.ToJson, Lean.FromJson for NestedRecursorInfo
deriving instance Lean.ToJson, Lean.FromJson for ConstantKind
deriving instance Lean.ToJson, Lean.FromJson for ConstantInfo

structure CheckedLayer where
  env : Env := emptyEnv
  contentToNames : Std.HashMap String (List Name) := {}
  nameToContent : Std.HashMap Name String := {}
  declarations : Nat := 0

structure ReplaySummary where
  env : Env
  reused : Nat := 0
  checked : Nat := 0

structure SqliteReplayResult where
  env : Env
  reused : Nat := 0
  checked : Nat := 0
  newEntries : List ConstantInfo := []
  newContentToNames : Std.HashMap String (List Name) := {}

structure SqliteOnDemandReplayState where
  env : Env := emptyEnv
  reused : Nat := 0
  checked : Nat := 0
  newEntries : List ConstantInfo := []
  newContentToNames : Std.HashMap String (List Name) := {}
  cumulativeMs : Nat := 0
  index : Nat := 0

inductive ReplayStepStatus where
  | reused
  | checked
  | rejected
  deriving BEq

structure ReplayStep where
  index : Nat
  declaration : Declaration
  status : ReplayStepStatus
  elapsedMs : Nat
  cumulativeMs : Nat

abbrev ReplayObserver :=
  ReplayStep → IO Unit

structure SaveSummary where
  declarations : Nat
  envLength : Nat

structure ContentEntry where
  key : String
  names : List Name
  deriving Lean.ToJson, Lean.FromJson

structure LayerFile where
  formatVersion : Nat
  manifest : String
  declarations : Nat
  entries : List ConstantInfo
  content : List ContentEntry
  deriving Lean.ToJson, Lean.FromJson

def formatVersion : Nat :=
  1

def sqliteFormatVersion : Nat :=
  2

def sqliteOnDemandFormatVersion : Nat :=
  3

def manifestName : String :=
  "LeanCore429"

def declarationContentKey (declaration : Declaration) : String :=
  toString (repr declaration)

def addedNames (before after : Env) : Result (List Name) := do
  if before.length <= after.length then
    pure ((after.entries.take (after.length - before.length)).map fun info => info.name)
  else
    fail "environment length decreased while replaying a declaration"

def addedEntries (before after : Env) : Result (List ConstantInfo) := do
  if before.length <= after.length then
    pure (after.entries.take (after.length - before.length))
  else
    fail "environment length decreased while replaying a declaration"

def CheckedLayer.record (layer : CheckedLayer) (declaration : Declaration)
    (names : List Name) (env : Env) : CheckedLayer :=
  let key := declarationContentKey declaration
  {
    env
    contentToNames := layer.contentToNames.insert key names
    nameToContent := names.foldl (fun index name => index.insert name key) layer.nameToContent
    declarations := layer.declarations + 1
  }

def contentEntries (layer : CheckedLayer) : List ContentEntry :=
  layer.contentToNames.toList.map fun pair => { key := pair.1, names := pair.2 }

def toLayerFile (layer : CheckedLayer) : LayerFile :=
  {
    formatVersion
    manifest := manifestName
    declarations := layer.declarations
    entries := layer.env.entries
    content := contentEntries layer
  }

def legacyEqualityNdRecPrimitive (info : ConstantInfo) : Bool :=
  info.name == "Eq.ndrec" && info.kind == .equalityNdRec

def envFromEntries (entries : List ConstantInfo) : Result Env := do
  let mut env := emptyEnv
  for info in entries.reverse do
    if legacyEqualityNdRecPrimitive info then
      pure ()
    else
      env ← Env.add env info
  pure env

def fromLayerFile (file : LayerFile) : Result CheckedLayer := do
  if file.formatVersion != formatVersion then
    fail s!"unsupported layer format version: {file.formatVersion}"
  else if file.manifest != manifestName then
    fail s!"unsupported layer manifest: {file.manifest}"
  else
    let env ← envFromEntries file.entries
    let contentToNames :=
      file.content.foldl
        (fun index entry => index.insert entry.key entry.names)
        ({} : Std.HashMap String (List Name))
    let nameToContent :=
      file.content.foldl
        (fun index entry =>
          entry.names.foldl (fun index name => index.insert name entry.key) index)
        ({} : Std.HashMap Name String)
    pure { env, contentToNames, nameToContent, declarations := file.declarations }

def sqlitePath (path : System.FilePath) : Bool :=
  let text := path.toString
  text.endsWith ".sqlite" || text.endsWith ".sqlite3" || text.endsWith ".db"

def saveJson (path : System.FilePath) (layer : CheckedLayer) : IO Unit := do
  IO.FS.writeFile path (Lean.toJson (toLayerFile layer)).compress

def loadJson (path : System.FilePath) : IO (Result CheckedLayer) := do
  let input ← IO.FS.readFile path
  match Lean.Json.parse input with
  | .error err => pure (.error { message := s!"invalid layer JSON: {err}" })
  | .ok json =>
      match (Lean.fromJson? json : Except String LayerFile) with
      | .error err => pure (.error { message := s!"invalid layer file: {err}" })
      | .ok file => pure (fromLayerFile file)

def sqlQuote (text : String) : String :=
  let body :=
    text.foldl
      (fun acc c =>
        if c == '\'' then
          (acc.push '\'').push '\''
        else
          acc.push c)
      ""
  "'" ++ body ++ "'"

def sqlite3Output (args : Array String) (script : String) : IO (Result String) := do
  try
    let output ← IO.Process.output { cmd := "sqlite3", args } (some script)
    if output.exitCode == 0 then
      pure (.ok output.stdout)
    else
      pure (.error { message := s!"sqlite3 failed with exit code {output.exitCode}: {output.stderr.trimAscii}" })
  catch err =>
    pure (.error { message := s!"could not run sqlite3: {err}" })

def sqlite3RunWriter (args : Array String)
    (writeScript : IO.FS.Handle → IO (Result α)) : IO (Result α) := do
  try
    let child0 ←
      IO.Process.spawn {
        cmd := "sqlite3",
        args,
        stdin := .piped,
        stdout := .piped,
        stderr := .piped
      }
    let (stdin, child) ← child0.takeStdin
    let stdoutTask ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
    let stderrTask ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
    let callbackResult : Result α ← try
      writeScript stdin
    catch err =>
      try child.kill catch _ => pure ()
      let stderr := (match stderrTask.get with | .ok text => text | .error _ => "").trimAscii
      let detail := if stderr.isEmpty then "" else s!"; sqlite3 stderr: {stderr}"
      pure (.error { message := s!"could not write sqlite3 script: {err}{detail}" })
    match callbackResult with
    | .error err =>
        try
          stdin.putStr "ROLLBACK;\n.quit\n"
          stdin.flush
        catch _ =>
          child.kill
        let _ ← child.wait
        let _ := stdoutTask.get
        let _ := stderrTask.get
        pure (.error err)
    | .ok value =>
        stdin.putStr ".quit\n"
        stdin.flush
        let exitCode ← child.wait
        let _ ← IO.ofExcept stdoutTask.get
        let stderr ← IO.ofExcept stderrTask.get
        if exitCode == 0 then
          pure (.ok value)
        else
          pure (.error { message := s!"sqlite3 failed with exit code {exitCode}: {stderr.trimAscii}" })
  catch err =>
    pure (.error { message := s!"could not run sqlite3: {err}" })

def chompLine (line : String) : String :=
  let line :=
    if line.endsWith "\n" then
      (line.dropEnd 1).toString
    else
      line
  if line.endsWith "\r" then
    (line.dropEnd 1).toString
  else
    line

partial def sqliteFoldStdoutRows (stdout : IO.FS.Handle) (acc : α)
    (step : α → String → IO (Result α)) : IO (Result α) := do
  let line ← stdout.getLine
  if line == "" then
    pure (.ok acc)
  else
    match ← step acc (chompLine line) with
    | .error err => pure (.error err)
    | .ok acc => sqliteFoldStdoutRows stdout acc step

def sqlite3FoldRows (args : Array String)
    (writeScript : IO.FS.Handle → IO Unit) (init : α)
    (step : α → String → IO (Result α)) : IO (Result α) := do
  try
    let child0 ←
      IO.Process.spawn {
        cmd := "sqlite3",
        args,
        stdin := .piped,
        stdout := .piped,
        stderr := .piped
      }
    let (stdin, child) ← child0.takeStdin
    let stderrTask ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
    let writeResult : Result Unit ← try
      writeScript stdin
      stdin.putStr ".quit\n"
      stdin.flush
      pure (Except.ok ())
    catch err =>
      try child.kill catch _ => pure ()
      let stderr := (match stderrTask.get with | .ok text => text | .error _ => "").trimAscii
      let detail := if stderr.isEmpty then "" else s!"; sqlite3 stderr: {stderr}"
      pure (Except.error { message := s!"could not write sqlite3 query: {err}{detail}" })
    match writeResult with
    | Except.error err =>
        let _ ← child.wait
        let _ := stderrTask.get
        pure (.error err)
    | Except.ok () =>
        let rowsResult ← sqliteFoldStdoutRows child.stdout init step
        match rowsResult with
        | .error err =>
            child.kill
            let _ ← child.wait
            let _ := stderrTask.get
            pure (.error err)
        | .ok acc =>
            let exitCode ← child.wait
            let stderr ← IO.ofExcept stderrTask.get
            if exitCode == 0 then
              pure (.ok acc)
            else
              pure (.error { message := s!"sqlite3 failed with exit code {exitCode}: {stderr.trimAscii}" })
  catch err =>
    pure (.error { message := s!"could not run sqlite3: {err}" })

def sqliteScriptHeader : String :=
  ".bail on\n" ++
  "PRAGMA synchronous=OFF;\n"

def sqliteSelectHeader : String :=
  ".bail on\n" ++
  ".mode list\n" ++
  ".headers off\n"

def sqliteInsertText (table : String) (pos : Nat) (json : String) : String :=
  s!"INSERT INTO {table}(pos,json) VALUES({pos},{sqlQuote json});\n"

def sqliteTempPath (path : System.FilePath) : System.FilePath :=
  path.addExtension "tmp"

def checkSavePath (path : System.FilePath) : IO (Result Unit) := do
  if sqlitePath path then
    if ← System.FilePath.pathExists path then
      pure (.error { message := s!"SQLite layer already exists: {path}" })
    else
      let tempPath := sqliteTempPath path
      if ← System.FilePath.pathExists tempPath then
        pure (.error { message := s!"temporary SQLite layer already exists: {tempPath}" })
      else
        pure (.ok ())
  else
    pure (.ok ())

def sqliteCreateScript : String :=
  sqliteScriptHeader ++
  "BEGIN;\n" ++
  "CREATE TABLE meta(key TEXT PRIMARY KEY, value TEXT NOT NULL);\n" ++
  "CREATE TABLE env(pos INTEGER PRIMARY KEY, json TEXT NOT NULL);\n" ++
  "CREATE TABLE content(key TEXT PRIMARY KEY, names TEXT NOT NULL) WITHOUT ROWID;\n"

def sqliteInsertEnv (pos : Nat) (info : ConstantInfo) : String :=
  sqliteInsertText "env" pos (Lean.toJson info).compress

def sqliteInsertContent (key : String) (names : List Name) : String :=
  s!"INSERT INTO content(key,names) VALUES({sqlQuote key},{sqlQuote (Lean.toJson names).compress});\n"

def sqliteInsertContentIgnore (key : String) (names : List Name) : String :=
  s!"INSERT OR IGNORE INTO content(key,names) VALUES({sqlQuote key},{sqlQuote (Lean.toJson names).compress});\n"

def sqliteInsertMeta (key value : String) : String :=
  s!"INSERT INTO meta(key,value) VALUES({sqlQuote key},{sqlQuote value});\n"

def sqliteUpdateMeta (key value : String) : String :=
  s!"UPDATE meta SET value = {sqlQuote value} WHERE key = {sqlQuote key};\n"

def sqliteFinishScript (declarations : Nat) : String :=
  sqliteInsertMeta "formatVersion" (toString sqliteFormatVersion) ++
  sqliteInsertMeta "manifest" manifestName ++
  sqliteInsertMeta "declarations" (toString declarations) ++
  "COMMIT;\n"

def sqliteOnDemandCreateScript : String :=
  sqliteScriptHeader ++
  "BEGIN;\n" ++
  "CREATE TABLE meta(key TEXT PRIMARY KEY, value TEXT NOT NULL);\n" ++
  "CREATE TABLE declarations(id INTEGER PRIMARY KEY AUTOINCREMENT, anchor TEXT NOT NULL, kind TEXT NOT NULL, entry_count INTEGER NOT NULL);\n" ++
  "CREATE INDEX declarations_anchor_idx ON declarations(anchor);\n" ++
  "CREATE TABLE entries(decl_id INTEGER NOT NULL, entry_pos INTEGER NOT NULL, name TEXT NOT NULL, json TEXT NOT NULL, PRIMARY KEY(decl_id, entry_pos));\n" ++
  "CREATE INDEX entries_name_idx ON entries(name);\n"

def sqliteOnDemandFinishScript (declarations : Nat) : String :=
  sqliteInsertMeta "formatVersion" (toString sqliteOnDemandFormatVersion) ++
  sqliteInsertMeta "manifest" manifestName ++
  sqliteInsertMeta "declarations" (toString declarations) ++
  "COMMIT;\n"

def sqliteInsertOnDemandDeclarationHeader (anchor kind : String) (entryCount : Nat) :
    String :=
  s!"INSERT INTO declarations(anchor,kind,entry_count) VALUES({sqlQuote anchor},{sqlQuote kind},{entryCount});\n"

def sqliteInsertOnDemandEntry (entryPos : Nat) (info : ConstantInfo) : String :=
  s!"INSERT INTO entries(decl_id,entry_pos,name,json) VALUES((SELECT id FROM declarations ORDER BY id DESC LIMIT 1),{entryPos},{sqlQuote info.name},{sqlQuote (Lean.toJson info).compress});\n"

def sqliteInsertOnDemandEntryJson (entryPos : Nat) (info : ConstantInfo) (json : String) :
    String :=
  s!"INSERT INTO entries(decl_id,entry_pos,name,json) VALUES((SELECT id FROM declarations ORDER BY id DESC LIMIT 1),{entryPos},{sqlQuote info.name},{sqlQuote json});\n"

def declarationPrimaryAnchor : Declaration → Name
  | .axiom name ..
  | .definition name ..
  | .opaque name ..
  | .theorem name .. => name
  | .inductive spec => spec.name
  | .inductiveBlock block =>
      match block.specs with
      | spec :: _ => spec.name
      | [] => "empty inductive block"
  | .indexedInductive spec => spec.name
  | .equalityPrimitives => "Eq"
  | .quotientPrimitives => "Quot"

def cachedDeclarationKind (declaration : Declaration) : String :=
  MPC.Adapters.Export.declarationKindLabel declaration

def saveSqliteFromLayer (path : System.FilePath) (layer : CheckedLayer) : IO (Result Unit) := do
  match ← checkSavePath path with
  | .error err => pure (.error err)
  | .ok () =>
      let tempPath := sqliteTempPath path
      let result ← sqlite3RunWriter #[tempPath.toString] fun input => do
        input.putStr sqliteCreateScript
        let mut pos := 0
        for info in layer.env.entries.reverse do
          input.putStr (sqliteInsertEnv pos info)
          pos := pos + 1
        for entry in contentEntries layer do
          input.putStr (sqliteInsertContent entry.key entry.names)
        input.putStr (sqliteFinishScript layer.declarations)
        pure (.ok ())
      match result with
      | .error err => pure (.error err)
      | .ok () =>
          try
            IO.FS.rename tempPath path
            pure (.ok ())
          catch err =>
            pure (.error { message := s!"could not move SQLite layer {tempPath} to {path}: {err}" })

def saveSqliteFromState (manifest : Manifest) (path : System.FilePath)
    (state : MPC.Adapters.Export.ParseState) : IO (Result SaveSummary) := do
  match ← checkSavePath path with
  | .error err => pure (.error err)
  | .ok () =>
      let tempPath := sqliteTempPath path
      let result ← sqlite3RunWriter #[tempPath.toString] fun input => do
        input.putStr sqliteOnDemandCreateScript
        let mut env := emptyEnv
        let mut declarations := 0
        for declaration in state.declarations do
          let before := env
          match addDecl manifest env declaration with
          | .error err =>
              return .error {
                message := s!"while replaying {MPC.Adapters.Export.declarationKindLabel declaration} {MPC.Adapters.Export.declarationNameLabel declaration}: {err.message}"
              }
          | .ok nextEnv =>
              match addedEntries before nextEnv with
              | .error err => return .error err
              | .ok entries =>
                  input.putStr
                    (sqliteInsertOnDemandDeclarationHeader
                      (declarationPrimaryAnchor declaration)
                      (cachedDeclarationKind declaration)
                      entries.length)
                  let mut entryPos := 0
                  for info in entries.reverse do
                    input.putStr (sqliteInsertOnDemandEntry entryPos info)
                    entryPos := entryPos + 1
                  env := nextEnv
                  declarations := declarations + 1
        match MPC.Adapters.Export.auditGenerated env state.audit with
        | .error err => return .error err
        | .ok () =>
            input.putStr (sqliteOnDemandFinishScript declarations)
            pure (.ok { declarations, envLength := env.length })
      match result with
      | .error err => pure (.error err)
      | .ok summary =>
          try
            IO.FS.rename tempPath path
            pure (.ok summary)
          catch err =>
            pure (.error { message := s!"could not move SQLite layer {tempPath} to {path}: {err}" })

def saveSqlite (path : System.FilePath) (layer : CheckedLayer) : IO (Result Unit) := do
  saveSqliteFromLayer path layer

def createEmptySqliteLayer (path : System.FilePath) : IO (Result Unit) := do
  match ← checkSavePath path with
  | .error err => pure (.error err)
  | .ok () =>
      let tempPath := sqliteTempPath path
      let result ← sqlite3RunWriter #[tempPath.toString] fun input => do
        input.putStr sqliteCreateScript
        input.putStr (sqliteFinishScript 0)
        pure (.ok ())
      match result with
      | .error err => pure (.error err)
      | .ok () =>
          try
            IO.FS.rename tempPath path
            pure (.ok ())
          catch err =>
            pure (.error { message := s!"could not move SQLite layer {tempPath} to {path}: {err}" })

def appendSqliteLayer (path : System.FilePath) (startEnvPos declarations checked : Nat)
    (entries : List ConstantInfo) (contentToNames : Std.HashMap String (List Name)) :
    IO (Result Unit) := do
  let result ← sqlite3RunWriter #[path.toString] fun input => do
    input.putStr sqliteScriptHeader
    input.putStr "BEGIN;\n"
    let mut pos := startEnvPos
    for info in entries do
      input.putStr (sqliteInsertEnv pos info)
      pos := pos + 1
    for pair in contentToNames.toList do
      input.putStr (sqliteInsertContentIgnore pair.1 pair.2)
    input.putStr (sqliteUpdateMeta "declarations" (toString (declarations + checked)))
    input.putStr "COMMIT;\n"
    pure (.ok ())
  match result with
  | .error err => pure (.error err)
  | .ok () => pure (.ok ())

def sqliteRows (stdout : String) : List String :=
  (stdout.splitOn "\n").filter fun line => line != ""

def sqliteQuery (path : System.FilePath) (query : String) : IO (Result (List String)) := do
  match ← sqlite3Output #["-readonly", path.toString] (sqliteSelectHeader ++ query ++ "\n.quit\n") with
  | .error err => pure (.error err)
  | .ok stdout => pure (.ok (sqliteRows stdout))

def singleSqliteRow (label : String) (rows : List String) : Result String :=
  match rows with
  | [row] => pure row
  | [] => fail s!"SQLite layer is missing {label}"
  | _ => fail s!"SQLite layer has multiple {label} rows"

def sqliteMeta (path : System.FilePath) (key : String) : IO (Result String) := do
  match ← sqliteQuery path s!"SELECT value FROM meta WHERE key = {sqlQuote key};" with
  | .error err => pure (.error err)
  | .ok rows => pure (singleSqliteRow key rows)

def parseSqliteNat (label value : String) : Result Nat :=
  match value.trimAscii.toString.toNat? with
  | some n => pure n
  | none => fail s!"invalid SQLite layer {label}: {value}"

def parseJsonRow (label : String) (row : String) {α : Type} [Lean.FromJson α] : Result α := do
  match Lean.Json.parse row with
  | .error err => fail s!"invalid SQLite layer {label} JSON: {err}"
  | .ok json =>
      match (Lean.fromJson? json : Except String α) with
      | .error err => fail s!"invalid SQLite layer {label}: {err}"
      | .ok value => pure value

structure SqliteLayer where
  path : System.FilePath
  env : Env
  declarations : Nat
  envRows : Nat

def checkSqliteMeta (path : System.FilePath) : IO (Result Nat) := do
  match ← sqliteMeta path "formatVersion" with
  | .error err => pure (.error err)
  | .ok versionText =>
      match ← sqliteMeta path "manifest" with
      | .error err => pure (.error err)
      | .ok manifest =>
          match ← sqliteMeta path "declarations" with
          | .error err => pure (.error err)
          | .ok declarationsText =>
              let metaResult : Result Nat := do
                let version ← parseSqliteNat "format version" versionText
                if version != sqliteFormatVersion then
                  fail s!"unsupported SQLite layer format version: {version}"
                if manifest != manifestName then
                  fail s!"unsupported layer manifest: {manifest}"
                parseSqliteNat "declaration count" declarationsText
              pure metaResult

def sqliteLayerFormatVersion (path : System.FilePath) : IO (Result Nat) := do
  match ← sqliteMeta path "formatVersion" with
  | .error err => pure (.error err)
  | .ok versionText => pure (parseSqliteNat "format version" versionText)

def checkSqliteOnDemandMeta (path : System.FilePath) : IO (Result Nat) := do
  match ← sqliteMeta path "formatVersion" with
  | .error err => pure (.error err)
  | .ok versionText =>
      match ← sqliteMeta path "manifest" with
      | .error err => pure (.error err)
      | .ok manifest =>
          match ← sqliteMeta path "declarations" with
          | .error err => pure (.error err)
          | .ok declarationsText =>
              let metaResult : Result Nat := do
                let version ← parseSqliteNat "format version" versionText
                if version != sqliteOnDemandFormatVersion then
                  fail s!"unsupported SQLite layer format version: {version}"
                if manifest != manifestName then
                  fail s!"unsupported layer manifest: {manifest}"
                parseSqliteNat "declaration count" declarationsText
              pure metaResult

def ensureSqliteLayer (path : System.FilePath) : IO (Result Unit) := do
  if ← System.FilePath.pathExists path then
    match ← checkSqliteMeta path with
    | .error err => pure (.error err)
    | .ok _ => pure (.ok ())
  else
    createEmptySqliteLayer path

def createEmptySqliteOnDemandLayer (path : System.FilePath) : IO (Result Unit) := do
  match ← checkSavePath path with
  | .error err => pure (.error err)
  | .ok () =>
      let tempPath := sqliteTempPath path
      let result ← sqlite3RunWriter #[tempPath.toString] fun input => do
        input.putStr sqliteOnDemandCreateScript
        input.putStr (sqliteOnDemandFinishScript 0)
        pure (.ok ())
      match result with
      | .error err => pure (.error err)
      | .ok () =>
          try
            IO.FS.rename tempPath path
            pure (.ok ())
          catch err =>
            pure (.error { message := s!"could not move SQLite layer {tempPath} to {path}: {err}" })

def ensureSqliteOnDemandLayer (path : System.FilePath) : IO (Result Unit) := do
  if ← System.FilePath.pathExists path then
    match ← sqliteLayerFormatVersion path with
    | .error err => pure (.error err)
    | .ok version =>
        if version == sqliteOnDemandFormatVersion then
          match ← checkSqliteOnDemandMeta path with
          | .error err => pure (.error err)
          | .ok _ => pure (.ok ())
        else if version == sqliteFormatVersion then
          pure (.error { message := s!"SQLite layer {path} uses v2 bulk-cache format; migrate it with mpc-migrate-layer or use a new .db path" })
        else
          pure (.error { message := s!"unsupported SQLite layer format version: {version}" })
  else
    createEmptySqliteOnDemandLayer path

def loadSqliteLayer (path : System.FilePath) : IO (Result SqliteLayer) := do
  match ← checkSqliteMeta path with
  | .error err => pure (.error err)
  | .ok declarations =>
      match ← sqlite3FoldRows #["-readonly", path.toString]
          (fun input => do
            input.putStr sqliteSelectHeader
            input.putStr "SELECT json FROM env ORDER BY pos;\n")
          (emptyEnv, 0)
          (fun state row => do
            let (env, rows) := state
            match (parseJsonRow "environment entry" row : Result ConstantInfo) with
            | .error err => pure (.error err)
            | .ok info =>
                if legacyEqualityNdRecPrimitive info then
                  pure (.ok (env, rows + 1))
                else
                  match Env.add env info with
                  | .error err => pure (.error err)
                  | .ok env => pure (.ok (env, rows + 1))) with
      | .error err => pure (.error err)
      | .ok (env, envRows) => pure (.ok { path, env, declarations, envRows })

def splitSqlitePair (row : String) : Result (String × String) :=
  match row.splitOn "|" with
  | first :: rest => pure (first, String.intercalate "|" rest)
  | [] => fail "empty SQLite result row"

def parseNamesJson (label row : String) : Result (List Name) :=
  parseJsonRow label row

def loadSqlite (path : System.FilePath) : IO (Result CheckedLayer) := do
  match ← loadSqliteLayer path with
  | .error err => pure (.error err)
  | .ok layer =>
      match ← sqlite3FoldRows #["-readonly", path.toString]
          (fun input => do
            input.putStr sqliteSelectHeader
            input.putStr "SELECT key, names FROM content ORDER BY key;\n")
          ({} : Std.HashMap String (List Name))
          (fun contentToNames row => do
            match splitSqlitePair row with
            | .error err => pure (.error err)
            | .ok (key, namesJson) =>
                match parseNamesJson "content names" namesJson with
                | .error err => pure (.error err)
                | .ok names => pure (.ok (contentToNames.insert key names))) with
      | .error err => pure (.error err)
      | .ok contentToNames =>
          let nameToContent :=
            contentToNames.toList.foldl
              (fun index pair =>
                pair.2.foldl (fun index name => index.insert name pair.1) index)
              ({} : Std.HashMap Name String)
          pure (.ok {
            env := layer.env,
            contentToNames,
            nameToContent,
            declarations := layer.declarations
          })

def save (path : System.FilePath) (layer : CheckedLayer) : IO (Result Unit) := do
  if sqlitePath path then
    saveSqlite path layer
  else
    try
      saveJson path layer
      pure (.ok ())
    catch err =>
      pure (.error { message := s!"could not write layer {path}: {err}" })

def load (path : System.FilePath) : IO (Result CheckedLayer) := do
  if sqlitePath path then
    loadSqlite path
  else
    loadJson path

def equalityPrimitiveNames : List Name :=
  ["Eq", "Eq.refl", "Eq.rec"]

def quotientPrimitiveNames : List Name :=
  ["Quot", "Quot.mk", "Quot.lift", "Quot.ind", "Quot.sound"]

def declarationAnchorNames : Declaration → List Name
  | .axiom name ..
  | .definition name ..
  | .opaque name ..
  | .theorem name .. => [name]
  | .inductive spec => [spec.name]
  | .inductiveBlock block => block.specs.map fun spec => spec.name
  | .indexedInductive spec => [spec.name]
  | .equalityPrimitives => equalityPrimitiveNames
  | .quotientPrimitives => quotientPrimitiveNames

def checkCachedNames (env : Env) (names : List Name) : Result Unit := do
  for name in names do
    if env.contains name then
      pure ()
    else
      fail s!"checked layer is missing cached constant {name}"

def cachedAnchorNames (declaration : Declaration) (names : List Name) : List Name :=
  match declaration with
  | .equalityPrimitives => equalityPrimitiveNames
  | _ => names

def checkNoAnchorConflict (env : Env) (declaration : Declaration) : Result Unit := do
  for name in declarationAnchorNames declaration do
    if env.contains name then
      fail s!"checked layer has a different declaration for {name}"
    else
      pure ()

def optionExprAlphaEq : Option Expr → Option Expr → Bool
  | none, none => true
  | some left, some right => left.alphaEq right
  | _, _ => false

def binderListAlphaEq (left right : List Binder) : Bool :=
  left.length == right.length &&
    (left.zip right).all fun pair => pair.1.type.alphaEq pair.2.type

def exprListAlphaEq (left right : List Expr) : Bool :=
  left.length == right.length &&
    (left.zip right).all fun pair => pair.1.alphaEq pair.2

def simpleConstructorSpecAlphaEq (left right : SimpleConstructorSpec) : Bool :=
  left.name == right.name && binderListAlphaEq left.fields right.fields

def simpleConstructorSpecsAlphaEq
    (left right : List SimpleConstructorSpec) : Bool :=
  left.length == right.length &&
    (left.zip right).all fun pair => simpleConstructorSpecAlphaEq pair.1 pair.2

def simpleInductiveSpecAlphaEq
    (left right : SimpleInductiveSpec) : Bool :=
  left.name == right.name &&
    left.levelParams == right.levelParams &&
    binderListAlphaEq left.params right.params &&
    left.resultLevel == right.resultLevel &&
    simpleConstructorSpecsAlphaEq left.constructors right.constructors

def indexedConstructorSpecAlphaEq
    (left right : IndexedConstructorSpec) : Bool :=
  left.name == right.name &&
    binderListAlphaEq left.fields right.fields &&
    exprListAlphaEq left.targetIndices right.targetIndices

def indexedConstructorSpecsAlphaEq
    (left right : List IndexedConstructorSpec) : Bool :=
  left.length == right.length &&
    (left.zip right).all fun pair => indexedConstructorSpecAlphaEq pair.1 pair.2

def indexedInductiveSpecAlphaEq
    (left right : IndexedInductiveSpec) : Bool :=
  left.name == right.name &&
    left.levelParams == right.levelParams &&
    binderListAlphaEq left.params right.params &&
    binderListAlphaEq left.indices right.indices &&
    left.resultLevel == right.resultLevel &&
    indexedConstructorSpecsAlphaEq left.constructors right.constructors

def constantInfoMatchesAtomicDeclaration (info : ConstantInfo) : Declaration → Bool
  | .axiom name levelParams type =>
      info.name == name &&
        info.levelParams == levelParams &&
        info.type.alphaEq type &&
        info.value?.isNone &&
        info.kind == .axiom
  | .definition name levelParams type value =>
      info.name == name &&
        info.levelParams == levelParams &&
        info.type.alphaEq type &&
        optionExprAlphaEq info.value? (some value) &&
        info.kind == .definition
  | .opaque name levelParams type value =>
      info.name == name &&
        info.levelParams == levelParams &&
        info.type.alphaEq type &&
        optionExprAlphaEq info.value? (some value) &&
        info.kind == .opaque
  | .theorem name levelParams type value =>
      info.name == name &&
        info.levelParams == levelParams &&
        info.type.alphaEq type &&
        optionExprAlphaEq info.value? (some value) &&
        info.kind == .theorem
  | _ => false

def atomicDeclarationName? : Declaration → Option Name
  | .axiom name ..
  | .definition name ..
  | .opaque name ..
  | .theorem name .. => some name
  | _ => none

def constantInfoMatchesSimpleInductive (info : ConstantInfo)
    (spec : SimpleInductiveSpec) : Bool :=
  info.name == spec.name &&
    info.levelParams == spec.levelParams &&
    info.type.alphaEq (simpleInductiveType spec) &&
    info.value?.isNone &&
    match info.kind with
    | .inductiveType cachedSpec => simpleInductiveSpecAlphaEq cachedSpec spec
    | _ => false

def constantInfoMatchesIndexedInductive (info : ConstantInfo)
    (spec : IndexedInductiveSpec) : Bool :=
  info.name == spec.name &&
    info.levelParams == spec.levelParams &&
    info.type.alphaEq (indexedInductiveType spec) &&
    info.value?.isNone &&
    match info.kind with
    | .indexedInductiveType cachedSpec => indexedInductiveSpecAlphaEq cachedSpec spec
    | _ => false

def checkExistingSimpleInductiveDeclaration (env : Env) (spec : SimpleInductiveSpec) :
    Result Bool := do
  match env.find? spec.name with
  | none => pure false
  | some info =>
      if constantInfoMatchesSimpleInductive info spec then
        pure true
      else
        fail s!"checked layer has a different declaration for {spec.name}"

def checkExistingIndexedInductiveDeclaration (env : Env) (spec : IndexedInductiveSpec) :
    Result Bool := do
  match env.find? spec.name with
  | none => pure false
  | some info =>
      if constantInfoMatchesIndexedInductive info spec then
        pure true
      else
        fail s!"checked layer has a different declaration for {spec.name}"

def checkExistingInductiveBlockDeclaration (env : Env) (block : InductiveBlockSpec) :
    Result Bool := do
  let mut sawExisting := false
  let mut sawMissing := false
  for spec in block.specs do
    match env.find? spec.name with
    | none => sawMissing := true
    | some info =>
        sawExisting := true
        if !(constantInfoMatchesSimpleInductive info { spec with levelParams := block.levelParams }) then
          fail s!"checked layer has a different declaration for {spec.name}"
  if sawExisting && sawMissing then
    fail "checked layer contains only part of an inductive block"
  else
    pure sawExisting

def checkExistingAtomicDeclaration (env : Env) (declaration : Declaration) : Result Bool := do
  match atomicDeclarationName? declaration with
  | none => pure false
  | some name =>
      match env.find? name with
      | none => pure false
      | some info =>
          if constantInfoMatchesAtomicDeclaration info declaration then
            pure true
          else
            fail s!"checked layer has a different declaration for {name}"

def checkExistingDeclarationReuse (env : Env) (declaration : Declaration) : Result Bool := do
  match ← checkExistingAtomicDeclaration env declaration with
  | true => pure true
  | false =>
      match declaration with
      | .inductive spec =>
          checkExistingSimpleInductiveDeclaration env spec
      | .indexedInductive spec =>
          checkExistingIndexedInductiveDeclaration env spec
      | .inductiveBlock block =>
          checkExistingInductiveBlockDeclaration env block
      | _ =>
          checkNoAnchorConflict env declaration
          pure false

def entriesFind? (entries : List ConstantInfo) (name : Name) : Option ConstantInfo :=
  entries.find? fun info => info.name == name

def entriesContainName (entries : List ConstantInfo) (name : Name) : Bool :=
  entries.any fun info => info.name == name

def entriesContainNames (entries : List ConstantInfo) (names : List Name) : Bool :=
  names.all fun name => entriesContainName entries name

def primitiveKindMatches (info : ConstantInfo) (name : Name) (kind : ConstantKind) : Bool :=
  info.name == name && info.kind == kind

def entriesMatchEqualityPrimitives (entries : List ConstantInfo) : Bool :=
  entries.length == 3 &&
    match entriesFind? entries "Eq", entriesFind? entries "Eq.refl",
        entriesFind? entries "Eq.rec" with
    | some eqInfo, some reflInfo, some recInfo =>
        primitiveKindMatches eqInfo "Eq" .equalityType &&
          primitiveKindMatches reflInfo "Eq.refl" .equalityRefl &&
          primitiveKindMatches recInfo "Eq.rec" .equalityRec
    | _, _, _ => false

def entriesMatchQuotientPrimitives (entries : List ConstantInfo) : Bool :=
  entries.length == 5 &&
    match entriesFind? entries "Quot", entriesFind? entries "Quot.mk",
        entriesFind? entries "Quot.lift", entriesFind? entries "Quot.ind",
        entriesFind? entries "Quot.sound" with
    | some quotInfo, some mkInfo, some liftInfo, some indInfo, some soundInfo =>
        primitiveKindMatches quotInfo "Quot" .quotientType &&
          primitiveKindMatches mkInfo "Quot.mk" .quotientMk &&
          primitiveKindMatches liftInfo "Quot.lift" .quotientLift &&
          primitiveKindMatches indInfo "Quot.ind" .quotientInd &&
          primitiveKindMatches soundInfo "Quot.sound" .quotientSound
    | _, _, _, _, _ => false

def simpleInductiveRequiredNames (spec : SimpleInductiveSpec) : List Name :=
  spec.name :: spec.constructors.map fun ctor => ctor.name

def indexedInductiveRequiredNames (spec : IndexedInductiveSpec) : List Name :=
  spec.name :: spec.constructors.map fun ctor => ctor.name

def blockRequiredNames (block : InductiveBlockSpec) : List Name :=
  block.specs.flatMap fun spec => simpleInductiveRequiredNames spec

def entriesMatchDeclaration (entries : List ConstantInfo) (declaration : Declaration) : Bool :=
  match declaration with
  | .axiom .. | .definition .. | .opaque .. | .theorem .. =>
      match entries with
      | [info] => constantInfoMatchesAtomicDeclaration info declaration
      | _ => false
  | .inductive spec =>
      let requiredNames := simpleInductiveRequiredNames spec
      match entriesFind? entries spec.name with
      | some info =>
          constantInfoMatchesSimpleInductive info spec &&
            entriesContainNames entries requiredNames &&
            requiredNames.length < entries.length
      | none => false
  | .indexedInductive spec =>
      let requiredNames := indexedInductiveRequiredNames spec
      match entriesFind? entries spec.name with
      | some info =>
          constantInfoMatchesIndexedInductive info spec &&
            entriesContainNames entries requiredNames &&
            requiredNames.length < entries.length
      | none => false
  | .inductiveBlock block =>
      let requiredNames := blockRequiredNames block
      entriesContainNames entries requiredNames &&
        requiredNames.length < entries.length &&
        block.specs.all fun spec =>
          match entriesFind? entries spec.name with
          | some info =>
              constantInfoMatchesSimpleInductive info
                { spec with levelParams := block.levelParams }
          | none => false
  | .equalityPrimitives => entriesMatchEqualityPrimitives entries
  | .quotientPrimitives => entriesMatchQuotientPrimitives entries

def addEntriesToEnv (env : Env) (entries : List ConstantInfo) : Result Env := do
  let mut env := env
  for info in entries do
    if legacyEqualityNdRecPrimitive info then
      pure ()
    else
      env ← Env.add env info
  pure env

def CheckedLayer.reusable? (layer : CheckedLayer) (env : Env)
    (declaration : Declaration) : Result Bool := do
  let key := declarationContentKey declaration
  match layer.contentToNames.get? key with
  | some names =>
      checkCachedNames env (cachedAnchorNames declaration names)
      pure true
  | none =>
      checkExistingDeclarationReuse env declaration

def parseContentMatchRow (row : String) : Result (Nat × List Name) := do
  let (indexText, namesJson) ← splitSqlitePair row
  let index ← parseSqliteNat "requested content index" indexText
  let names ← parseNamesJson "requested content names" namesJson
  pure (index, names)

def sqliteRequestedContentChunk (path : System.FilePath) (requests : Array (Nat × String)) :
    IO (Result (Std.HashMap Nat (List Name))) := do
  let init : Std.HashMap Nat (List Name) := {}
  let write : IO.FS.Handle → IO Unit := fun input => do
    input.putStr sqliteSelectHeader
    for request in requests do
      input.putStr s!"SELECT {request.1}, names FROM content WHERE key = {sqlQuote request.2};\n"
  let step : Std.HashMap Nat (List Name) → String → IO (Result (Std.HashMap Nat (List Name))) :=
    fun acc row => do
      match parseContentMatchRow row with
      | .error err => pure (.error err)
      | .ok (index, names) => pure (.ok (acc.insert index names))
  sqlite3FoldRows #["-readonly", path.toString] write init step

def sqliteRequestedContent (path : System.FilePath) (declarations : List Declaration) :
    IO (Result (Std.HashMap Nat (List Name))) := do
  let maxChunkChars := 4000000
  let maxChunkRows := 128
  let mut contentMatches : Std.HashMap Nat (List Name) := {}
  let mut chunk : Array (Nat × String) := #[]
  let mut chunkChars := 0
  let mut pos := 0
  for declaration in declarations do
    let key := declarationContentKey declaration
    let keyChars := key.length
    if !chunk.isEmpty && (chunk.size >= maxChunkRows || chunkChars + keyChars > maxChunkChars) then
      match ← sqliteRequestedContentChunk path chunk with
      | .error err => return .error err
      | .ok chunkMatches =>
          for pair in chunkMatches.toList do
            contentMatches := contentMatches.insert pair.1 pair.2
          chunk := #[]
          chunkChars := 0
    chunk := chunk.push (pos, key)
    chunkChars := chunkChars + keyChars
    pos := pos + 1
  if !chunk.isEmpty then
    match ← sqliteRequestedContentChunk path chunk with
    | .error err => return .error err
    | .ok chunkMatches =>
        for pair in chunkMatches.toList do
          contentMatches := contentMatches.insert pair.1 pair.2
  pure (.ok contentMatches)

def sqliteOnDemandCandidateIds (path : System.FilePath) (anchor : Name) :
    IO (Result (List Nat)) := do
  match ← sqliteQuery path
      s!"SELECT id FROM declarations WHERE anchor = {sqlQuote anchor} ORDER BY id DESC;" with
  | .error err => pure (.error err)
  | .ok rows =>
      let mut ids : List Nat := []
      for row in rows do
        match parseSqliteNat "declaration id" row with
        | .error err => return .error err
        | .ok id => ids := id :: ids
      pure (.ok ids.reverse)

def sqliteOnDemandLoadEntries (path : System.FilePath) (declarationId : Nat) :
    IO (Result (List ConstantInfo)) := do
  match ← sqlite3FoldRows #["-readonly", path.toString]
      (fun input => do
        input.putStr sqliteSelectHeader
        input.putStr s!"SELECT json FROM entries WHERE decl_id = {declarationId} ORDER BY entry_pos;\n")
      ([] : List ConstantInfo)
      (fun entries row => do
        match (parseJsonRow "on-demand environment entry" row : Result ConstantInfo) with
        | .error err => pure (.error err)
        | .ok info => pure (.ok (info :: entries))) with
  | .error err => pure (.error err)
  | .ok entries => pure (.ok entries.reverse)

partial def sqliteOnDemandFindMatchingEntries (path : System.FilePath)
    (declaration : Declaration) (candidateIds : List Nat) :
    IO (Result (Option (List ConstantInfo))) := do
  match candidateIds with
  | [] => pure (.ok none)
  | id :: rest =>
      match ← sqliteOnDemandLoadEntries path id with
      | .error err => pure (.error err)
      | .ok entries =>
          if entriesMatchDeclaration entries declaration then
            pure (.ok (some entries))
          else
            sqliteOnDemandFindMatchingEntries path declaration rest

def sqliteOnDemandLookup (path : System.FilePath) (declaration : Declaration) :
    IO (Result (Option (List ConstantInfo))) := do
  match ← sqliteOnDemandCandidateIds path (declarationPrimaryAnchor declaration) with
  | .error err => pure (.error err)
  | .ok ids => sqliteOnDemandFindMatchingEntries path declaration ids

def appendSqliteOnDemandDeclaration (path : System.FilePath)
    (declaration : Declaration) (entries : List ConstantInfo) : IO (Result Unit) := do
  let result ← sqlite3RunWriter #[path.toString] fun input => do
    input.putStr sqliteScriptHeader
    input.putStr "BEGIN;\n"
    input.putStr
      (sqliteInsertOnDemandDeclarationHeader
        (declarationPrimaryAnchor declaration) (cachedDeclarationKind declaration)
        entries.length)
    let mut entryPos := 0
    for info in entries do
      input.putStr (sqliteInsertOnDemandEntry entryPos info)
      entryPos := entryPos + 1
    input.putStr
      "UPDATE meta SET value = CAST(value AS INTEGER) + 1 WHERE key = 'declarations';\n"
    input.putStr "COMMIT;\n"
    pure (.ok ())
  match result with
  | .error err => pure (.error err)
  | .ok () => pure (.ok ())

structure SqliteEnvJsonEntry where
  pos : Nat
  info : ConstantInfo
  json : String

def parseSqliteEnvJsonEntry (row : String) : Result SqliteEnvJsonEntry := do
  let (posText, jsonText) ← splitSqlitePair row
  let pos ← parseSqliteNat "environment position" posText
  let info : ConstantInfo ← parseJsonRow "environment entry" jsonText
  pure { pos, info, json := jsonText }

def sqliteV2EnvEntriesByName (path : System.FilePath) :
    IO (Result (Std.HashMap Name SqliteEnvJsonEntry)) := do
  match ← sqlite3FoldRows #["-readonly", path.toString]
      (fun input => do
        input.putStr sqliteSelectHeader
        input.putStr "SELECT pos, json FROM env ORDER BY pos;\n")
      ({} : Std.HashMap Name SqliteEnvJsonEntry)
      (fun entries row => do
        match parseSqliteEnvJsonEntry row with
        | .error err => pure (.error err)
        | .ok entry =>
            if legacyEqualityNdRecPrimitive entry.info then
              pure (.ok entries)
            else
              pure (.ok (entries.insert entry.info.name entry))) with
  | .error err => pure (.error err)
  | .ok entries => pure (.ok entries)

def sqliteV2ContentNames (path : System.FilePath) : IO (Result (List (List Name))) := do
  match ← sqlite3FoldRows #["-readonly", path.toString]
      (fun input => do
        input.putStr sqliteSelectHeader
        input.putStr "SELECT names FROM content ORDER BY key;\n")
      ([] : List (List Name))
      (fun rows row => do
        match parseNamesJson "content names" row with
        | .error err => pure (.error err)
        | .ok names => pure (.ok (names :: rows))) with
  | .error err => pure (.error err)
  | .ok rows => pure (.ok rows.reverse)

def insertEnvJsonEntryByPos (entry : SqliteEnvJsonEntry) :
    List SqliteEnvJsonEntry → List SqliteEnvJsonEntry
  | [] => [entry]
  | head :: rest =>
      if entry.pos < head.pos then
        entry :: head :: rest
      else
        head :: insertEnvJsonEntryByPos entry rest

def sortEnvJsonEntriesByPos (entries : List SqliteEnvJsonEntry) :
    List SqliteEnvJsonEntry :=
  entries.foldl (fun sorted entry => insertEnvJsonEntryByPos entry sorted) []

def constantInfoKindLabel (info : ConstantInfo) : String :=
  match info.kind with
  | .axiom => "axiom"
  | .definition => "definition"
  | .opaque => "opaque"
  | .theorem => "theorem"
  | .inductiveType .. => "inductive"
  | .indexedInductiveType .. => "indexed-inductive"
  | .constructor .. => "generated"
  | .recursor .. => "generated"
  | .mutualRecursor .. => "generated"
  | .indexedRecursor .. => "generated"
  | .nestedRecursor .. => "generated"
  | .equalityType | .equalityRefl | .equalityRec | .equalityNdRec =>
      "equality-primitives"
  | .quotientType | .quotientMk | .quotientLift | .quotientInd | .quotientSound =>
      "quotient-primitives"

def migrateSqliteContentGroup (entriesByName : Std.HashMap Name SqliteEnvJsonEntry)
    (names : List Name) : Result (Name × String × List SqliteEnvJsonEntry) := do
  let mut entries : List SqliteEnvJsonEntry := []
  for name in names do
    match entriesByName.get? name with
    | some entry => entries := entry :: entries
    | none => fail s!"v2 layer content row references missing cached constant {name}"
  let sortedEntries := sortEnvJsonEntriesByPos entries
  match sortedEntries with
  | [] => fail "v2 layer content row has no cached constants"
  | first :: _ => pure (first.info.name, constantInfoKindLabel first.info, sortedEntries)

def migrateSqliteToOnDemand (sourcePath targetPath : System.FilePath) :
    IO (Result SaveSummary) := do
  match ← sqliteLayerFormatVersion sourcePath with
  | .error err => pure (.error err)
  | .ok version =>
      if version != sqliteFormatVersion then
        pure (.error { message := s!"source SQLite layer must use v2 format, found {version}" })
      else
        match ← checkSqliteMeta sourcePath with
        | .error err => pure (.error err)
        | .ok _ =>
            match ← checkSavePath targetPath with
            | .error err => pure (.error err)
            | .ok () =>
                match ← sqliteV2EnvEntriesByName sourcePath with
                | .error err => pure (.error err)
                | .ok entriesByName =>
                    match ← sqliteV2ContentNames sourcePath with
                    | .error err => pure (.error err)
                    | .ok contentRows =>
                        let tempPath := sqliteTempPath targetPath
                        let result ← sqlite3RunWriter #[tempPath.toString] fun input => do
                          input.putStr sqliteOnDemandCreateScript
                          let mut declarations := 0
                          for names in contentRows do
                            match migrateSqliteContentGroup entriesByName names with
                            | .error err => return .error err
                            | .ok (anchor, kind, entries) =>
                                input.putStr
                                  (sqliteInsertOnDemandDeclarationHeader anchor kind
                                    entries.length)
                                let mut entryPos := 0
                                for entry in entries do
                                  input.putStr
                                    (sqliteInsertOnDemandEntryJson entryPos entry.info
                                      entry.json)
                                  entryPos := entryPos + 1
                                declarations := declarations + 1
                          input.putStr (sqliteOnDemandFinishScript declarations)
                          pure (.ok {
                            declarations,
                            envLength := entriesByName.toList.length
                          })
                        match result with
                        | .error err => pure (.error err)
                        | .ok summary =>
                            try
                              IO.FS.rename tempPath targetPath
                              pure (.ok summary)
                            catch err =>
                              pure (.error { message := s!"could not move SQLite layer {tempPath} to {targetPath}: {err}" })

def emitReplayStep (observer? : Option ReplayObserver) (index : Nat) (declaration : Declaration)
    (status : ReplayStepStatus) (startMs? : Option Nat) (cumulativeMs : Nat) : IO Nat := do
  match observer?, startMs? with
  | some observer, some startMs =>
      let stopMs ← IO.monoMsNow
      let elapsedMs := stopMs - startMs
      let cumulativeMs := cumulativeMs + elapsedMs
      observer { index, declaration, status, elapsedMs, cumulativeMs }
      pure cumulativeMs
  | _, _ => pure cumulativeMs

def replaySqliteOnDemandStep (manifest : Manifest) (layerPath : System.FilePath)
    (observer? : Option ReplayObserver) (persist : Bool)
    (state : SqliteOnDemandReplayState) (declaration : Declaration) :
    IO (Result SqliteOnDemandReplayState) := do
  let startMs? ←
    match observer? with
    | some _ => some <$> IO.monoMsNow
    | none => pure none
  let key := declarationContentKey declaration
  match checkExistingDeclarationReuse state.env declaration with
  | .error err =>
      let _ ←
        emitReplayStep observer? state.index declaration .rejected startMs?
          state.cumulativeMs
      pure (.error err)
  | .ok true =>
      let cumulativeMs ←
        emitReplayStep observer? state.index declaration .reused startMs?
          state.cumulativeMs
      pure (.ok {
        state with
        reused := state.reused + 1,
        cumulativeMs,
        index := state.index + 1
      })
  | .ok false =>
      match ← sqliteOnDemandLookup layerPath declaration with
      | .error err =>
          let _ ←
            emitReplayStep observer? state.index declaration .rejected startMs?
              state.cumulativeMs
          pure (.error err)
      | .ok (some entries) =>
          match addEntriesToEnv state.env entries with
          | .error err =>
              let _ ←
                emitReplayStep observer? state.index declaration .rejected startMs?
                  state.cumulativeMs
              pure (.error err)
          | .ok env =>
              let cumulativeMs ←
                emitReplayStep observer? state.index declaration .reused startMs?
                  state.cumulativeMs
              pure (.ok {
                state with
                env,
                reused := state.reused + 1,
                cumulativeMs,
                index := state.index + 1
              })
      | .ok none =>
          let before := state.env
          match addDecl manifest state.env declaration with
          | .ok env =>
              match addedEntries before env with
              | .error err =>
                  let _ ←
                    emitReplayStep observer? state.index declaration .rejected startMs?
                      state.cumulativeMs
                  pure (.error err)
              | .ok entries =>
                  let entriesChronological := entries.reverse
                  if persist then
                    match ←
                        appendSqliteOnDemandDeclaration layerPath declaration
                          entriesChronological with
                    | .error err =>
                        let _ ←
                          emitReplayStep observer? state.index declaration .rejected startMs?
                            state.cumulativeMs
                        return .error err
                    | .ok () => pure ()
                  let newEntries :=
                    if persist then
                      state.newEntries
                    else
                      state.newEntries ++ entriesChronological
                  let newContentToNames :=
                    state.newContentToNames.insert key (entries.map fun info => info.name)
                  let cumulativeMs ←
                    emitReplayStep observer? state.index declaration .checked startMs?
                      state.cumulativeMs
                  pure (.ok {
                    state with
                    env,
                    checked := state.checked + 1,
                    newEntries,
                    newContentToNames,
                    cumulativeMs,
                    index := state.index + 1
                  })
          | .error err =>
              let _ ←
                emitReplayStep observer? state.index declaration .rejected startMs?
                  state.cumulativeMs
              pure (.error {
                message :=
                  s!"while replaying {MPC.Adapters.Export.declarationKindLabel declaration} {MPC.Adapters.Export.declarationNameLabel declaration}: {err.message}"
              })

def finishSqliteOnDemandReplay (audit : MPC.Adapters.Export.Audit)
    (state : SqliteOnDemandReplayState) : Result SqliteReplayResult := do
  MPC.Adapters.Export.auditGenerated state.env audit
  pure {
    env := state.env,
    reused := state.reused,
    checked := state.checked,
    newEntries := state.newEntries,
    newContentToNames := state.newContentToNames
  }

def replaySqliteOnDemandCore (manifest : Manifest) (layerPath : System.FilePath)
    (audit : MPC.Adapters.Export.Audit) (declarations : List Declaration)
    (observer? : Option ReplayObserver) (persist : Bool) :
    IO (Result SqliteReplayResult) := do
  match ← checkSqliteOnDemandMeta layerPath with
  | .error err => pure (.error err)
  | .ok _ =>
      let mut state : SqliteOnDemandReplayState := {}
      for declaration in declarations do
        match ← replaySqliteOnDemandStep manifest layerPath observer? persist state declaration with
        | .error err => return .error err
        | .ok nextState => state := nextState
      pure (finishSqliteOnDemandReplay audit state)

def replaySqliteCore (manifest : Manifest) (layerPath : System.FilePath)
    (audit : MPC.Adapters.Export.Audit) (declarations : List Declaration)
    (observer? : Option ReplayObserver) (persistPath? : Option System.FilePath := none) :
    IO (Result SqliteReplayResult) := do
  match ← loadSqliteLayer layerPath with
  | .error err => pure (.error err)
  | .ok layer =>
      match ← sqliteRequestedContent layerPath declarations with
      | .error err => pure (.error err)
      | .ok cachedContent =>
          let mut newContentToNames : Std.HashMap String (List Name) := {}
          let mut newEntries : List ConstantInfo := []
          let mut env := layer.env
          let mut persistedEnvRows := layer.envRows
          let mut reused := 0
          let mut checked := 0
          let mut persistedDeclarations := layer.declarations
          let mut cumulativeMs := 0
          let mut index := 0
          for declaration in declarations do
            let startMs? ←
              match observer? with
              | some _ => some <$> IO.monoMsNow
              | none => pure none
            let key := declarationContentKey declaration
            match newContentToNames.get? key with
            | some names =>
                match checkCachedNames env names with
                | .error err =>
                    cumulativeMs ← emitReplayStep observer? index declaration .rejected startMs? cumulativeMs
                    return .error err
                | .ok () =>
                    reused := reused + 1
                    cumulativeMs ← emitReplayStep observer? index declaration .reused startMs? cumulativeMs
            | none =>
                match cachedContent.get? index with
                | some names =>
                    match checkCachedNames env (cachedAnchorNames declaration names) with
                    | .error err =>
                        cumulativeMs ← emitReplayStep observer? index declaration .rejected startMs? cumulativeMs
                        return .error err
                    | .ok () =>
                        reused := reused + 1
                        cumulativeMs ← emitReplayStep observer? index declaration .reused startMs? cumulativeMs
                | none =>
                    match checkExistingDeclarationReuse env declaration with
                    | .error err =>
                        cumulativeMs ← emitReplayStep observer? index declaration .rejected startMs? cumulativeMs
                        return .error err
                    | .ok true =>
                        let names := declarationAnchorNames declaration
                        match persistPath? with
                        | some persistPath =>
                            let contentToNames :=
                              ({} : Std.HashMap String (List Name)).insert key names
                            match ←
                                appendSqliteLayer persistPath persistedEnvRows persistedDeclarations 0 []
                                  contentToNames with
                            | .error err =>
                                cumulativeMs ← emitReplayStep observer? index declaration .rejected startMs? cumulativeMs
                                return .error err
                            | .ok () => pure ()
                        | none => pure ()
                        newContentToNames := newContentToNames.insert key names
                        reused := reused + 1
                        cumulativeMs ← emitReplayStep observer? index declaration .reused startMs? cumulativeMs
                    | .ok false =>
                        let before := env
                        match addDecl manifest env declaration with
                        | .ok nextEnv =>
                            match addedEntries before nextEnv with
                            | .error err =>
                                cumulativeMs ← emitReplayStep observer? index declaration .rejected startMs? cumulativeMs
                                return .error err
                            | .ok entries =>
                                let names := entries.map fun info => info.name
                                match persistPath? with
                                | some persistPath =>
                                    let contentToNames :=
                                      ({} : Std.HashMap String (List Name)).insert key names
                                    match ←
                                        appendSqliteLayer persistPath persistedEnvRows
                                          persistedDeclarations 1 entries.reverse contentToNames with
                                    | .error err =>
                                        cumulativeMs ← emitReplayStep observer? index declaration .rejected startMs? cumulativeMs
                                        return .error err
                                    | .ok () =>
                                        persistedDeclarations := persistedDeclarations + 1
                                        persistedEnvRows := persistedEnvRows + entries.length
                                | none =>
                                    newEntries := newEntries ++ entries.reverse
                                env := nextEnv
                                newContentToNames := newContentToNames.insert key names
                                checked := checked + 1
                                cumulativeMs ← emitReplayStep observer? index declaration .checked startMs? cumulativeMs
                        | .error err =>
                            cumulativeMs ← emitReplayStep observer? index declaration .rejected startMs? cumulativeMs
                            return .error {
                              message := s!"while replaying {MPC.Adapters.Export.declarationKindLabel declaration} {MPC.Adapters.Export.declarationNameLabel declaration}: {err.message}"
                            }
            index := index + 1
          match MPC.Adapters.Export.auditGenerated env audit with
          | .error err => pure (.error err)
          | .ok () => pure (.ok { env, reused, checked, newEntries, newContentToNames })

def replaySqliteWithObserver (manifest : Manifest) (layerPath : System.FilePath)
    (audit : MPC.Adapters.Export.Audit) (declarations : List Declaration)
    (observer? : Option ReplayObserver) :
    IO (Result ReplaySummary) := do
  match ← sqliteLayerFormatVersion layerPath with
  | .error err => pure (.error err)
  | .ok version =>
      if version == sqliteOnDemandFormatVersion then
        match ← replaySqliteOnDemandCore manifest layerPath audit declarations observer? false with
        | .error err => pure (.error err)
        | .ok result =>
            pure (.ok { env := result.env, reused := result.reused, checked := result.checked })
      else if version == sqliteFormatVersion then
        match ← replaySqliteCore manifest layerPath audit declarations observer? with
        | .error err => pure (.error err)
        | .ok result =>
            pure (.ok { env := result.env, reused := result.reused, checked := result.checked })
      else
        pure (.error { message := s!"unsupported SQLite layer format version: {version}" })

def replaySqlite (manifest : Manifest) (layerPath : System.FilePath)
    (audit : MPC.Adapters.Export.Audit) (declarations : List Declaration) :
    IO (Result ReplaySummary) := do
  replaySqliteWithObserver manifest layerPath audit declarations none

def cacheSqliteWithObserver (manifest : Manifest) (layerPath : System.FilePath)
    (audit : MPC.Adapters.Export.Audit) (declarations : List Declaration)
    (observer? : Option ReplayObserver) :
    IO (Result ReplaySummary) := do
  match ← ensureSqliteOnDemandLayer layerPath with
  | .error err => pure (.error err)
  | .ok () =>
      match ← replaySqliteOnDemandCore manifest layerPath audit declarations observer? true with
      | .error err => pure (.error err)
      | .ok result =>
          pure (.ok { env := result.env, reused := result.reused, checked := result.checked })

def cacheSqlite (manifest : Manifest) (layerPath : System.FilePath)
    (audit : MPC.Adapters.Export.Audit) (declarations : List Declaration) :
    IO (Result ReplaySummary) := do
  cacheSqliteWithObserver manifest layerPath audit declarations none

def build (manifest : Manifest) (state : MPC.Adapters.Export.ParseState) :
    Result CheckedLayer := do
  let mut layer : CheckedLayer := {}
  let mut env := emptyEnv
  for declaration in state.declarations do
    let before := env
    match addDecl manifest env declaration with
    | .ok nextEnv =>
        let names ← addedNames before nextEnv
        env := nextEnv
        layer := layer.record declaration names env
    | .error err =>
        fail s!"while replaying {MPC.Adapters.Export.declarationKindLabel declaration} {MPC.Adapters.Export.declarationNameLabel declaration}: {err.message}"
  MPC.Adapters.Export.auditGenerated env state.audit
  pure layer

def saveFromState (manifest : Manifest) (path : System.FilePath)
    (state : MPC.Adapters.Export.ParseState) : IO (Result SaveSummary) := do
  if sqlitePath path then
    saveSqliteFromState manifest path state
  else
    match build manifest state with
    | .error err => pure (.error err)
    | .ok layer => do
        match ← save path layer with
        | .error err => pure (.error err)
        | .ok () => pure (.ok { declarations := layer.declarations, envLength := layer.env.length })

def replay (manifest : Manifest) (layer : CheckedLayer) (audit : MPC.Adapters.Export.Audit)
    (declarations : List Declaration) : Result ReplaySummary := do
  let mut layer := layer
  let mut env := layer.env
  let mut reused := 0
  let mut checked := 0
  for declaration in declarations do
    if ← layer.reusable? env declaration then
      reused := reused + 1
    else
      let before := env
      match addDecl manifest env declaration with
      | .ok nextEnv =>
          let names ← addedNames before nextEnv
          env := nextEnv
          layer := layer.record declaration names env
          checked := checked + 1
      | .error err =>
          fail s!"while replaying {MPC.Adapters.Export.declarationKindLabel declaration} {MPC.Adapters.Export.declarationNameLabel declaration}: {err.message}"
  MPC.Adapters.Export.auditGenerated env audit
  pure { env, reused, checked }

end MPC.Adapters.Layer
