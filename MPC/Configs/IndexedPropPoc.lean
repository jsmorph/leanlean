import MPC.Configs.IndexedPoc

namespace MPC.Configs

def IndexedPropPoc : Manifest :=
  { IndexedPoc with inductiveProp := .propOnly }

end MPC.Configs
