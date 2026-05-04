import MPC.Configs.Poc

namespace MPC.Adapters.Script

def checkDeclarations (manifest : Manifest) (declarations : List Declaration) : Result Env :=
  replay manifest emptyEnv declarations

end MPC.Adapters.Script
