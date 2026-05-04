import MPC.Configs.Poc

namespace MPC.Configs

def PrimitiveNatPoc : Manifest :=
  { Poc with primitiveReductions := .nat429 }

end MPC.Configs
