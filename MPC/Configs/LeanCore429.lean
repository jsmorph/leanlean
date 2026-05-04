import MPC.Configs.Poc

namespace MPC.Configs

def LeanCore429 : Manifest :=
  {
    Poc with
    inductives := .indexed
    inductiveProp := .largeElim
    equality := .primitive
    quotients := .primitive
    projections := .core
    primitiveReductions := .nat429
    functionEta := .enabled
  }

end MPC.Configs
