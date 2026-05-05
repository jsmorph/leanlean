import MPC.Adapters.Export
import Std.Data.HashMap

namespace MPC.Adapters.Layer

structure CheckedLayer where
  env : Env := emptyEnv
  contentToNames : Std.HashMap String (List Name) := {}
  nameToContent : Std.HashMap Name String := {}
  declarations : Nat := 0

structure ReplaySummary where
  env : Env
  reused : Nat := 0
  checked : Nat := 0

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
