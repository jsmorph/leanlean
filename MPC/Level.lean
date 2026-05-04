import MPC.Name

namespace MPC

inductive Level where
  | zero
  | param : Name → Level
  | succ : Level → Level
  | max : Level → Level → Level
  | imax : Level → Level → Level
  deriving BEq, Repr

abbrev LevelContext := List Name

end MPC
