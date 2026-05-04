import MPC.Replay

namespace MPC.Configs

def Poc : Manifest :=
  {
    prop := .enabled
    literals := .nat
    inductives := .simple
  }

end MPC.Configs
