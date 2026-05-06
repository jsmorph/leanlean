import MPC.Adapters.Layer

namespace MigrateLayer

def usage : String :=
  "usage: mpc-migrate-layer <source-v2.db> <target-v3.db>"

def filePath (path : String) : IO System.FilePath :=
  pure (System.FilePath.mk path)

def run : List String → IO UInt32
  | [source, target] => do
      match ←
          MPC.Adapters.Layer.migrateSqliteToOnDemand (← filePath source)
            (← filePath target) with
      | .ok summary => do
          IO.println
            s!"migrated {summary.declarations} declaration entries; environment size {summary.envLength}; target {target}"
          pure 0
      | .error err => do
          IO.eprintln s!"error: {err.message}"
          pure 1
  | _ => do
      IO.eprintln usage
      pure 2

end MigrateLayer

def main (args : List String) : IO UInt32 :=
  MigrateLayer.run args
