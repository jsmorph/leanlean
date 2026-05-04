import MPC.Configs.Poc

namespace MPC.Configs

def QuotPoc : Manifest :=
  { Poc with quotients := .primitive }

end MPC.Configs

