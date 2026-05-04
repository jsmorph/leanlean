import MPC.Configs.Poc

namespace MPC.Configs

def InductivePropPoc : Manifest :=
  { Poc with inductiveProp := .propOnly }

end MPC.Configs
