import MPC.Configs.IndexedPoc

namespace MPC.Configs

def IndexedPropLargeElimPoc : Manifest :=
  { IndexedPoc with inductiveProp := .largeElim }

end MPC.Configs
