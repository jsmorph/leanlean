import MPC.Packages.Inductive.Recursor

namespace MPC

def checkSimpleInductiveField
    (manifest : Manifest)
    (env : Env)
    (levelParams : LevelContext)
    (inductiveName : Name)
    (ctx : Context)
    (field : Binder) : Result Context := do
  let _ ← inferSort manifest env levelParams ctx field.type
  if simpleStrictlyPositive manifest env inductiveName field.type then
    pure (ctx.extend field.name field.type)
  else
    fail s!"field {field.name} is not strictly positive in {inductiveName}"

partial def checkSimpleInductiveFields
    (manifest : Manifest)
    (env : Env)
    (levelParams : LevelContext)
    (inductiveName : Name)
    (ctx : Context) : List Binder → Result Unit
  | [] => pure ()
  | field :: rest => do
      let ctx ← checkSimpleInductiveField manifest env levelParams inductiveName ctx field
      checkSimpleInductiveFields manifest env levelParams inductiveName ctx rest

def addSimpleInductive (manifest : Manifest) (env : Env) (spec : SimpleInductiveSpec) :
    Result Env := do
  Manifest.validate manifest
  if !manifest.supportsSimpleInductives then
    fail "simple inductives are disabled by the manifest"
  else if spec.resultLevel.defEq .zero then
    MPC.Packages.Inductive.Prop.checkPropInductiveEnabled manifest
  else
    pure ()
  let _ ← inferSort manifest env spec.levelParams [] (.sort spec.resultLevel)
  let inductiveInfo : ConstantInfo :=
    {
      name := spec.name
      levelParams := spec.levelParams
      type := simpleInductiveType spec
      kind := .inductiveType spec
  }
  let env ← Env.add env inductiveInfo
  let paramCtx := extendBinders [] spec.params
  for ctor in spec.constructors do
    checkSimpleInductiveFields manifest env spec.levelParams spec.name paramCtx ctor.fields
  let mut env := env
  for pair in enumerate spec.constructors do
    let ctor := pair.2
    let type := simpleConstructorType spec ctor
    let _ ← inferSort manifest env spec.levelParams [] type
    env ← Env.add env
      {
        name := ctor.name
        levelParams := spec.levelParams
        type
        kind := .constructor spec.name pair.1 ctor.fields.length
      }
  let largeElimEligible ← MPC.Packages.Inductive.Prop.simpleLargeElimEligible manifest env spec
  let motiveLevel :=
    MPC.Packages.Inductive.Prop.recursorMotiveLevel spec.levelParams spec.resultLevel
      largeElimEligible
  let recursorLevelParams :=
    MPC.Packages.Inductive.Prop.recursorLevelParams motiveLevel spec.levelParams
  match ← buildNestedRecursorFamily? manifest env spec with
  | some targets => do
      let mut nextEnv := env
      for pair in enumerate targets do
        let recursorType ← nestedRecursorType spec targets pair.1 motiveLevel
        let _ ← inferSort manifest nextEnv recursorLevelParams [] recursorType
        nextEnv ← Env.add nextEnv
          {
            name := pair.2.recursorName
            levelParams := recursorLevelParams
            type := recursorType
            kind :=
              .nestedRecursor
                {
                  rootName := spec.name
                  targetIndex := pair.1
                  targets
                }
          }
      pure nextEnv
  | none => do
      let recursorType := simpleRecursorType spec motiveLevel
      let _ ← inferSort manifest env recursorLevelParams [] recursorType
      let ctorInfos := spec.constructors.map (simpleRecursorConstructorInfo spec)
      Env.add env
        {
          name := simpleRecursorName spec
          levelParams := recursorLevelParams
          type := recursorType
          kind :=
            .recursor
              {
                inductiveName := spec.name
                constructors := ctorInfos
              }
        }

def checkMutualInductiveField
    (manifest : Manifest)
    (env : Env)
    (levelParams : LevelContext)
    (blockNames : List Name)
    (ctx : Context)
    (field : Binder) : Result Context := do
  let _ ← inferSort manifest env levelParams ctx field.type
  if mutualStrictlyPositive manifest env blockNames field.type then
    pure (ctx.extend field.name field.type)
  else
    fail s!"field {field.name} is not strictly positive in mutual block"

partial def checkMutualInductiveFields
    (manifest : Manifest)
    (env : Env)
    (levelParams : LevelContext)
    (blockNames : List Name)
    (ctx : Context) : List Binder → Result Unit
  | [] => pure ()
  | field :: rest => do
      let ctx ← checkMutualInductiveField manifest env levelParams blockNames ctx field
      checkMutualInductiveFields manifest env levelParams blockNames ctx rest

def checkInductiveBlockHeader
    (manifest : Manifest)
    (env : Env)
    (block : InductiveBlockSpec)
    (sharedParams : List Binder)
    (spec : SimpleInductiveSpec) : Result Unit := do
  if spec.levelParams != block.levelParams then
    fail s!"inductive {spec.name} must use the block universe parameters"
  else if !binderTypesAlphaEq spec.params sharedParams then
    fail s!"inductive {spec.name} must use the block parameter telescope"
  else if spec.resultLevel.defEq .zero then
    MPC.Packages.Inductive.Prop.checkPropInductiveEnabled manifest
  else
    pure ()
  let _ ← inferSort manifest env block.levelParams [] (.sort spec.resultLevel)
  let _ ← inferSort manifest env block.levelParams [] (simpleInductiveType spec)
  pure ()

def addInductiveBlock (manifest : Manifest) (env : Env) (block : InductiveBlockSpec) :
    Result Env := do
  Manifest.validate manifest
  if !manifest.supportsInductiveBlocks then
    fail "mutual inductive blocks are disabled by the manifest"
  else if !manifest.supportsSimpleInductives then
    fail "simple inductives are disabled by the manifest"
  else
    pure ()
  let firstSpec ←
    match block.specs with
    | [] => fail "mutual inductive block must contain at least one inductive"
    | spec :: _ => pure spec
  for spec in block.specs do
    checkInductiveBlockHeader manifest env block firstSpec.params spec
  let mut provisionalEnv := env
  for spec in block.specs do
    provisionalEnv ← Env.add provisionalEnv
      {
        name := spec.name
        levelParams := block.levelParams
        type := simpleInductiveType spec
        kind := .inductiveType spec
      }
  let blockNames := mutualBlockNames block
  let paramCtx := extendBinders [] firstSpec.params
  for spec in block.specs do
    for ctor in spec.constructors do
      checkMutualInductiveFields manifest provisionalEnv block.levelParams blockNames
        paramCtx ctor.fields
      let _ ← inferSort manifest provisionalEnv block.levelParams []
        (simpleConstructorType spec ctor)
      pure ()
  let mut env := provisionalEnv
  for entry in mutualConstructorEntries block do
    env ← Env.add env
      {
        name := entry.ctor.name
        levelParams := block.levelParams
        type := simpleConstructorType entry.spec entry.ctor
        kind := .constructor entry.spec.name entry.constructorIndex entry.ctor.fields.length
      }
  let largeElimEligible := false
  let motiveLevel := mutualBlockMotiveLevel block largeElimEligible
  let recursorLevelParams :=
    MPC.Packages.Inductive.Prop.recursorLevelParams motiveLevel block.levelParams
  let ctorInfos := (mutualConstructorEntries block).map (mutualRecursorConstructorInfo block)
  let inductiveNames := mutualBlockNames block
  for pair in enumerate block.specs do
    let recursorType ← mutualRecursorType block pair.1 motiveLevel
    let _ ← inferSort manifest env recursorLevelParams [] recursorType
    env ← Env.add env
      {
        name := simpleRecursorName pair.2
        levelParams := recursorLevelParams
        type := recursorType
        kind :=
          .mutualRecursor
            {
              targetIndex := pair.1
              inductiveNames
              constructors := ctorInfos
            }
      }
  pure env

def checkIndexedConstructor
    (manifest : Manifest)
    (env : Env)
    (spec : IndexedInductiveSpec)
    (paramCtx : Context)
    (ctor : IndexedConstructorSpec) : Result Unit := do
  if ctor.targetIndices.length != spec.indices.length then
    fail s!"constructor {ctor.name} has wrong number of target indices"
  checkSimpleInductiveFields manifest env spec.levelParams spec.name paramCtx ctor.fields
  let _ ← inferSort manifest env spec.levelParams [] (indexedConstructorType spec ctor)
  pure ()

def addIndexedInductive (manifest : Manifest) (env : Env) (spec : IndexedInductiveSpec) :
    Result Env := do
  Manifest.validate manifest
  if !manifest.supportsIndexedInductives then
    fail "indexed inductives are disabled by the manifest"
  else if spec.resultLevel.defEq .zero then
    MPC.Packages.Inductive.Prop.checkPropInductiveEnabled manifest
  else
    pure ()
  let _ ← inferSort manifest env spec.levelParams [] (indexedInductiveType spec)
  let inductiveInfo : ConstantInfo :=
    {
      name := spec.name
      levelParams := spec.levelParams
      type := indexedInductiveType spec
      kind := .indexedInductiveType spec
    }
  let env ← Env.add env inductiveInfo
  let paramCtx := extendBinders [] spec.params
  for ctor in spec.constructors do
    checkIndexedConstructor manifest env spec paramCtx ctor
  let mut env := env
  for pair in enumerate spec.constructors do
    let ctor := pair.2
    env ← Env.add env
      {
        name := ctor.name
        levelParams := spec.levelParams
        type := indexedConstructorType spec ctor
        kind := .constructor spec.name pair.1 ctor.fields.length
      }
  let ctorInfos := spec.constructors.map (indexedRecursorConstructorInfo spec)
  let largeElimEligible ← MPC.Packages.Inductive.Prop.indexedLargeElimEligible manifest env spec
  let motiveLevel :=
    MPC.Packages.Inductive.Prop.recursorMotiveLevel spec.levelParams spec.resultLevel
      largeElimEligible
  let recursorLevelParams :=
    MPC.Packages.Inductive.Prop.recursorLevelParams motiveLevel spec.levelParams
  let recursorType := indexedRecursorType spec ctorInfos motiveLevel
  let _ ← inferSort manifest env recursorLevelParams [] recursorType
  Env.add env
    {
      name := indexedRecursorName spec
      levelParams := recursorLevelParams
      type := recursorType
      kind :=
        .indexedRecursor
          {
            inductiveName := spec.name
            constructors := ctorInfos
          }
    }

end MPC
