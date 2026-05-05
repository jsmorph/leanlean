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

def manifestName : String :=
  "LeanCore429"

def declarationContentKey (declaration : Declaration) : String :=
  toString (repr declaration)

def addedNames (before after : Env) : Result (List Name) := do
  if before.length <= after.length then
    pure ((after.entries.take (after.length - before.length)).map fun info => info.name)
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

def envFromEntries (entries : List ConstantInfo) : Result Env := do
  let mut env := emptyEnv
  for info in entries.reverse do
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

def sqlite3Stream (args : Array String) (writeScript : IO.FS.Handle → IO Unit) :
    IO (Result String) := do
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
    let writeResult : Result Unit ← try
      writeScript stdin
      stdin.putStr ".quit\n"
      stdin.flush
      pure (Except.ok ())
    catch err =>
      child.kill
      pure (Except.error { message := s!"could not write sqlite3 script: {err}" })
    match writeResult with
    | Except.error err => pure (.error err)
    | Except.ok () =>
        let exitCode ← child.wait
        let stdout ← IO.ofExcept stdoutTask.get
        let stderr ← IO.ofExcept stderrTask.get
        if exitCode == 0 then
          pure (.ok stdout)
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

def saveSqlite (path : System.FilePath) (layer : CheckedLayer) : IO (Result Unit) := do
  match ← checkSavePath path with
  | .error err => pure (.error err)
  | .ok () =>
    let tempPath := sqliteTempPath path
    let result ← sqlite3Stream #[tempPath.toString] fun input => do
      input.putStr sqliteScriptHeader
      input.putStr "BEGIN;\n"
      input.putStr "CREATE TABLE meta(key TEXT PRIMARY KEY, value TEXT NOT NULL);\n"
      input.putStr "CREATE TABLE env(pos INTEGER PRIMARY KEY, json TEXT NOT NULL);\n"
      input.putStr "CREATE TABLE content(pos INTEGER PRIMARY KEY, json TEXT NOT NULL);\n"
      input.putStr s!"INSERT INTO meta(key,value) VALUES({sqlQuote "formatVersion"},{sqlQuote (toString formatVersion)});\n"
      input.putStr s!"INSERT INTO meta(key,value) VALUES({sqlQuote "manifest"},{sqlQuote manifestName});\n"
      input.putStr s!"INSERT INTO meta(key,value) VALUES({sqlQuote "declarations"},{sqlQuote (toString layer.declarations)});\n"
      let mut pos := 0
      for info in layer.env.entries do
        input.putStr (sqliteInsertText "env" pos (Lean.toJson info).compress)
        pos := pos + 1
      pos := 0
      for entry in contentEntries layer do
        input.putStr (sqliteInsertText "content" pos (Lean.toJson entry).compress)
        pos := pos + 1
      input.putStr "COMMIT;\n"
    match result with
    | .ok _ =>
        try
          IO.FS.rename tempPath path
          pure (.ok ())
        catch err =>
          pure (.error { message := s!"could not move SQLite layer {tempPath} to {path}: {err}" })
    | .error err => pure (.error err)

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

def sqliteJsonRows (path : System.FilePath) (table : String) : IO (Result (List String)) := do
  sqliteQuery path s!"SELECT json FROM {table} ORDER BY pos;"

def loadSqlite (path : System.FilePath) : IO (Result CheckedLayer) := do
  match ← sqliteMeta path "formatVersion" with
  | .error err => pure (.error err)
  | .ok versionText =>
      match ← sqliteMeta path "manifest" with
      | .error err => pure (.error err)
      | .ok manifest =>
          match ← sqliteMeta path "declarations" with
          | .error err => pure (.error err)
          | .ok declarationsText =>
              match ← sqliteJsonRows path "env" with
              | .error err => pure (.error err)
              | .ok entryRows =>
                  match ← sqliteJsonRows path "content" with
                  | .error err => pure (.error err)
                  | .ok contentRows =>
                      let fileResult : Result LayerFile := do
                        let entries ←
                          entryRows.mapM fun row =>
                            (parseJsonRow "environment entry" row : Result ConstantInfo)
                        let content ←
                          contentRows.mapM fun row =>
                            (parseJsonRow "content entry" row : Result ContentEntry)
                        pure {
                          formatVersion := (← parseSqliteNat "format version" versionText)
                          manifest
                          declarations := (← parseSqliteNat "declaration count" declarationsText)
                          entries
                          content
                        }
                      match fileResult with
                      | .error err => pure (.error err)
                      | .ok file => pure (fromLayerFile file)

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
  ["Eq", "Eq.refl", "Eq.rec", "Eq.ndrec"]

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

def CheckedLayer.reusable? (layer : CheckedLayer) (env : Env)
    (declaration : Declaration) : Result Bool := do
  let key := declarationContentKey declaration
  match layer.contentToNames.get? key with
  | some names =>
      for name in names do
        if env.contains name then
          pure ()
        else
          fail s!"checked layer is missing cached constant {name}"
      pure true
  | none =>
      for name in declarationAnchorNames declaration do
        if env.contains name then
          fail s!"checked layer has a different declaration for {name}"
        else
          pure ()
      pure false

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
