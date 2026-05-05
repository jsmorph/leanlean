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

def save (path : System.FilePath) (layer : CheckedLayer) : IO Unit := do
  IO.FS.writeFile path (Lean.toJson (toLayerFile layer)).compress

def load (path : System.FilePath) : IO (Result CheckedLayer) := do
  let input ← IO.FS.readFile path
  match Lean.Json.parse input with
  | .error err => pure (.error { message := s!"invalid layer JSON: {err}" })
  | .ok json =>
      match (Lean.fromJson? json : Except String LayerFile) with
      | .error err => pure (.error { message := s!"invalid layer file: {err}" })
      | .ok file => pure (fromLayerFile file)

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
