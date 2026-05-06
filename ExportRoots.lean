import Lean

namespace MPC.ExportRoots

inductive RootMode where
  | exportable
  | sourceFacing
  | selfCheck
  deriving DecidableEq

structure Config where
  moduleName : Lean.Name
  includeUnsafe : Bool
  mode : RootMode

def usage : String :=
  "usage: mpc-export-roots --module <module> [--source-facing | --self-check | --exportable] [--include-unsafe]"

def parseDottedName (label input : String) : Except String Lean.Name := do
  let parts := input.splitOn "."
  if parts.isEmpty || parts.any String.isEmpty then
    .error s!"invalid {label}: {input}"
  else
    pure (parts.foldl Lean.Name.mkStr Lean.Name.anonymous)

partial def parseArgsLoop
    (moduleName? : Option Lean.Name)
    (includeUnsafe : Bool)
    (mode : RootMode) : List String → Except String Config
  | [] =>
      match moduleName? with
      | none => .error "missing --module"
      | some moduleName => pure { moduleName, includeUnsafe, mode }
  | "--module" :: value :: rest => do
      let moduleName ← parseDottedName "module name" value
      parseArgsLoop (some moduleName) includeUnsafe mode rest
  | "--module" :: [] => .error "missing value after --module"
  | "--include-unsafe" :: rest =>
      parseArgsLoop moduleName? true mode rest
  | "--source-facing" :: rest =>
      parseArgsLoop moduleName? includeUnsafe .sourceFacing rest
  | "--self-check" :: rest =>
      parseArgsLoop moduleName? includeUnsafe .selfCheck rest
  | "--exportable" :: rest =>
      parseArgsLoop moduleName? includeUnsafe .exportable rest
  | "--help" :: _ => .error usage
  | arg :: _ => .error s!"unknown argument: {arg}"

def parseArgs (args : List String) : Except String Config :=
  parseArgsLoop none false .exportable args

def moduleConstantNames (env : Lean.Environment) (moduleName : Lean.Name) :
    Except String (List Lean.Name) := do
  let some moduleIdx := env.getModuleIdx? moduleName
    | .error s!"module is not loaded: {moduleName}"
  if h : moduleIdx.toNat < env.header.moduleData.size then
    let data := env.header.moduleData[moduleIdx.toNat]
    pure (data.constNames.qsort fun left right => left.quickCmp right == .lt).toList
  else
    .error s!"module data is missing for {moduleName}"

def exportableConstant (includeUnsafe : Bool) : Lean.ConstantInfo → Bool
  | .axiomInfo value => includeUnsafe || !value.isUnsafe
  | .defnInfo value => includeUnsafe || value.safety == .safe
  | .opaqueInfo value => includeUnsafe || !value.isUnsafe
  | .inductInfo value => includeUnsafe || !value.isUnsafe
  | .ctorInfo value => includeUnsafe || !value.isUnsafe
  | .recInfo value => includeUnsafe || !value.isUnsafe
  | .thmInfo _ => true
  | .quotInfo _ => true

def exportableName (env : Lean.Environment) (includeUnsafe : Bool) (name : Lean.Name) :
    Except String Bool := do
  let some info := env.find? name
    | .error s!"module data contains unknown declaration: {name}"
  pure (exportableConstant includeUnsafe info)

def generatedSupportName (name : Lean.Name) : Bool :=
  let text := toString name
  text.contains "._" ||
    text.contains "_proof_" ||
    text.contains "_unsafe_rec" ||
    text.contains ".match_" ||
    text.contains ".noConfusion" ||
    text.endsWith ".ctorElim" ||
    text.contains "_sparseCasesOn_" ||
    text.contains "._sparseCasesOn_" ||
    text.contains ".repr" ||
    text.contains ".instDecidable" ||
    text.contains ".instRepr" ||
    text.contains ".instInhabited" ||
    text.contains ".instBEq" ||
    text.startsWith "MPC.inst"

def leanAuxSupportName (env : Lean.Environment) (name : Lean.Name) : Bool :=
  let text := toString name
  Lean.isAuxRecursor env name ||
    (text.contains ".brecOn" && (text.endsWith ".go" || text.endsWith ".eq"))

def recursiveAuxSupportName (env : Lean.Environment) (name : Lean.Name) : Bool :=
  let text := toString name
  (Lean.isAuxRecursor env name && (text.endsWith ".brecOn" || text.endsWith ".below")) ||
    (text.contains ".brecOn" && (text.endsWith ".go" || text.endsWith ".eq"))

def sourceFacingConstant (env : Lean.Environment) : Lean.ConstantInfo → Bool
  | .defnInfo value =>
      value.safety == .safe &&
        !generatedSupportName value.name &&
        !leanAuxSupportName env value.name
  | .ctorInfo value => !value.isUnsafe
  | .recInfo value => !value.isUnsafe
  | .inductInfo value => !value.isUnsafe
  | .axiomInfo value => !value.isUnsafe && !generatedSupportName value.name
  | .opaqueInfo value => !value.isUnsafe && !generatedSupportName value.name
  | .thmInfo _ => false
  | _ => true

def sourceFacingName (env : Lean.Environment) (name : Lean.Name) :
    Except String Bool := do
  let some info := env.find? name
    | .error s!"module data contains unknown declaration: {name}"
  pure (sourceFacingConstant env info)

def selfCheckName (env : Lean.Environment) (name : Lean.Name) :
    Except String Bool := do
  if recursiveAuxSupportName env name then
    pure true
  else
    sourceFacingName env name

def exportRoots (env : Lean.Environment) (config : Config) :
    Except String (List Lean.Name) := do
  let names ← moduleConstantNames env config.moduleName
  match config.mode with
  | .exportable => names.filterM (exportableName env config.includeUnsafe)
  | .sourceFacing => names.filterM (sourceFacingName env)
  | .selfCheck => names.filterM (selfCheckName env)

unsafe def loadModuleEnvironment (moduleName : Lean.Name) : IO (Except String Lean.Environment) := do
  try
    let projectLib := (← IO.currentDir) / ".lake" / "build" / "lib" / "lean"
    Lean.initSearchPath (← Lean.findSysroot) [projectLib]
    Lean.enableInitializersExecution
    let env ←
      Lean.importModules
        (leakEnv := true)
        (loadExts := true)
        #[{ module := moduleName }]
        {}
    pure (.ok env)
  catch err =>
    pure (.error err.toString)

def printRoots (roots : List Lean.Name) : IO Unit := do
  for root in roots do
    IO.println root

unsafe def run (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error err => do
      IO.eprintln usage
      if err != usage then
        IO.eprintln s!"error: {err}"
      return 2
  | .ok config => do
      match ← loadModuleEnvironment config.moduleName with
      | .error err => do
          IO.eprintln s!"error: could not load module {config.moduleName}: {err}"
          return 1
      | .ok env =>
          match exportRoots env config with
          | .error err => do
              IO.eprintln s!"error: {err}"
              return 1
          | .ok roots => do
              printRoots roots
              return 0

end MPC.ExportRoots

unsafe def main (args : List String) : IO UInt32 :=
  MPC.ExportRoots.run args
