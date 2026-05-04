import MPC.Basic

namespace MPC

def Error.withPrefix (label : String) (error : Error) : Error :=
  { message := label ++ ": " ++ error.message }

end MPC
