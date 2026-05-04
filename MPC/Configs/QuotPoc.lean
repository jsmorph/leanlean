import MPC.Configs.Poc

namespace MPC.Configs

def QuotPoc : Manifest :=
  { Poc with equality := .primitive, quotients := .primitive }

end MPC.Configs
