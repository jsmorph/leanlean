namespace MPC

structure Error where
  message : String
  deriving BEq, Repr

abbrev Result := Except Error

def fail {α : Type} (message : String) : Result α :=
  .error { message }

end MPC
