import MPC.Configs.Poc

namespace MPC.Configs

def EqualityPoc : Manifest :=
  { Poc with equality := .primitive }

end MPC.Configs

