import MPC.Configs.Poc

namespace MPC.Adapters.Script

def parseLevel : String → Result Level
  | "0" => pure .zero
  | "1" => pure (.succ .zero)
  | token =>
      if token.startsWith "u:" then
        pure (.param (token.drop 2).toString)
      else
        fail s!"unknown level token: {token}"

partial def parseExpr : String → Result Expr
  | "Prop" => pure (.sort .zero)
  | "Type0" => pure (.sort (.succ .zero))
  | "Nat" => pure (.const "Nat" [])
  | token =>
      if token.startsWith "nat:" then
        match (token.drop 4).toString.toNat? with
        | some value => pure (.lit (.nat value))
        | none => fail s!"bad natural literal token: {token}"
      else if token.startsWith "forall:" then
        match token.splitOn ":" with
        | ["forall", name, domainToken, bodyToken] => do
            pure (.forallE name (← parseExpr domainToken) (← parseExpr bodyToken))
        | _ => fail s!"bad forall token: {token}"
      else
        pure (.const token [])

def parseLine (lineNumber : Nat) (line : String) : Result (Option Declaration) := do
  let line := line.trimAscii.toString
  if line.isEmpty || line.startsWith "#" then
    pure none
  else
    match line.splitOn " " with
    | ["axiom", name, typeToken] =>
        pure (some (.axiom name [] (← parseExpr typeToken)))
    | ["def", name, typeToken, valueToken] =>
        pure (some (.definition name [] (← parseExpr typeToken) (← parseExpr valueToken)))
    | ["opaque", name, typeToken, valueToken] =>
        pure (some (.opaque name [] (← parseExpr typeToken) (← parseExpr valueToken)))
    | ["theorem", name, typeToken, valueToken] =>
        pure (some (.theorem name [] (← parseExpr typeToken) (← parseExpr valueToken)))
    | ["inductive-bool", typeName, falseName, trueName] =>
        pure
          (some
            (.inductive
              {
                name := typeName
                resultLevel := .succ .zero
                constructors := [{ name := falseName }, { name := trueName }]
              }))
    | _ => fail s!"line {lineNumber}: unsupported script line: {line}"

partial def parseLinesLoop (lineNumber : Nat) (declarations : List Declaration) :
    List String → Result (List Declaration)
  | [] => pure declarations.reverse
  | line :: rest => do
      let declarations ←
        match ← parseLine lineNumber line with
        | some declaration => pure (declaration :: declarations)
        | none => pure declarations
      parseLinesLoop (lineNumber + 1) declarations rest

def parseDeclarations (input : String) : Result (List Declaration) :=
  parseLinesLoop 1 [] (input.splitOn "\n")

def checkDeclarations (manifest : Manifest) (declarations : List Declaration) : Result Env :=
  replay manifest emptyEnv declarations

def checkString (manifest : Manifest) (input : String) : Result Env := do
  checkDeclarations manifest (← parseDeclarations input)

end MPC.Adapters.Script
