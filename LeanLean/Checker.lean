import Lean
import LeanLean.Import

namespace LeanLean
namespace Checker

inductive Status where
  | accepted
  | rejected
  | unsupported
  | internalFailure
  deriving DecidableEq, Repr

structure Outcome where
  status : Status
  message : String
  deriving DecidableEq, Repr

namespace Outcome

def accepted (message : String) : Outcome :=
  { status := .accepted, message }

def rejected (message : String) : Outcome :=
  { status := .rejected, message }

def unsupported (message : String) : Outcome :=
  { status := .unsupported, message }

def internalFailure (message : String) : Outcome :=
  { status := .internalFailure, message }

def exitCode : Outcome → UInt32
  | { status := .accepted, .. } => 0
  | { status := .rejected, .. } => 1
  | { status := .unsupported, .. } => 2
  | { status := .internalFailure, .. } => 3

def label : Outcome → String
  | { status := .accepted, .. } => "accepted"
  | { status := .rejected, .. } => "rejected"
  | { status := .unsupported, .. } => "unsupported"
  | { status := .internalFailure, .. } => "internal"

end Outcome

def checkEnvironmentRoots (leanEnv : Lean.Environment) (roots : List Lean.Name) : Outcome :=
  match Import.translateEnvironmentClosure leanEnv roots with
  | .error err => .unsupported err
  | .ok declarations =>
      match replayDeclarations [] declarations with
      | .ok _ => .accepted s!"checked {declarations.length} declaration entries"
      | .error err => .rejected err

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

unsafe def checkModuleRoots (moduleName : Lean.Name) (roots : List Lean.Name) : IO Outcome := do
  match ← loadModuleEnvironment moduleName with
  | .ok leanEnv => pure (checkEnvironmentRoots leanEnv roots)
  | .error err => pure (.unsupported s!"could not load Lean module {moduleName}: {err}")

end Checker
end LeanLean
