import MPC.Replay

namespace MPC.Configs

def Poc : Manifest :=
  {
    declarations := .checked
    prop := .enabled
    literals := .nat
    inductives := .simple
  }

end MPC.Configs
