import LeanLean

import LeanLean

def main : IO Unit := do
  match LeanLean.demoReport with
  | .error err => throw <| IO.userError err
  | .ok lines =>
      for line in lines do
        IO.println line
