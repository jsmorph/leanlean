import LeanLean.Checker

namespace LeanLean.CheckModule

structure Config where
  moduleName : Lean.Name
  roots : List Lean.Name

def usage : String :=
  "usage: leanlean-check-module --module <module> --decl <name> [--decl <name> ...]"

def parseDottedName (label input : String) : Except String Lean.Name := do
  let parts := input.splitOn "."
  if parts.isEmpty || parts.any String.isEmpty then
    .error s!"invalid {label}: {input}"
  else
    pure (parts.foldl Lean.Name.mkStr Lean.Name.anonymous)

partial def parseArgsLoop
    (moduleName? : Option Lean.Name)
    (roots : List Lean.Name) : List String → Except String Config
  | [] =>
      match moduleName?, roots with
      | none, _ => .error "missing --module"
      | some _, [] => .error "missing --decl"
      | some moduleName, roots => pure { moduleName, roots }
  | "--module" :: value :: rest => do
      let moduleName ← parseDottedName "module name" value
      parseArgsLoop (some moduleName) roots rest
  | "--module" :: [] => .error "missing value after --module"
  | "--decl" :: value :: rest => do
      let root ← parseDottedName "declaration name" value
      parseArgsLoop moduleName? (roots ++ [root]) rest
  | "--decl" :: [] => .error "missing value after --decl"
  | "--help" :: _ => .error usage
  | arg :: _ => .error s!"unknown argument: {arg}"

def parseArgs (args : List String) : Except String Config :=
  parseArgsLoop none [] args

def printRoots : List Lean.Name → IO Unit
  | [] => pure ()
  | root :: rest => do
      IO.println s!"root: {root}"
      printRoots rest

def printOutcome (config : Config) (outcome : Checker.Outcome) : IO Unit := do
  IO.println outcome.label
  IO.println s!"module: {config.moduleName}"
  printRoots config.roots
  if outcome.message != "" then
    IO.println s!"message: {outcome.message}"

unsafe def run (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error err => do
      IO.eprintln usage
      if err != usage then
        IO.eprintln s!"error: {err}"
      return 2
  | .ok config => do
      let outcome ← Checker.checkModuleRoots config.moduleName config.roots
      printOutcome config outcome
      return outcome.exitCode

end LeanLean.CheckModule

unsafe def main (args : List String) : IO UInt32 :=
  LeanLean.CheckModule.run args
