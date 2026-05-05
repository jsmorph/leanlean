import Lean
import MPC.Configs.Poc

namespace MPC.Adapters.NDJSON

structure Audit where
  constructors : List Name := []
  recursors : List Name := []
  deriving BEq, Repr, Inhabited

structure ParseState where
  declarations : List Declaration := []
  audit : Audit := {}
  deriving BEq, Repr, Inhabited

def field (json : Lean.Json) (key : String) : Result Lean.Json :=
  match json.getObjVal? key with
  | .ok value => pure value
  | .error err => fail s!"missing or malformed field {key}: {err}"

def field? (json : Lean.Json) (key : String) : Option Lean.Json :=
  (json.getObjVal? key).toOption

def asString (json : Lean.Json) : Result String :=
  match json.getStr? with
  | .ok value => pure value
  | .error err => fail s!"expected string: {err}"

def asNat (json : Lean.Json) : Result Nat :=
  match json.getNat? with
  | .ok value => pure value
  | .error err => fail s!"expected natural number: {err}"

def asArray (json : Lean.Json) : Result (Array Lean.Json) :=
  match json.getArr? with
  | .ok value => pure value
  | .error err => fail s!"expected array: {err}"

def stringField (json : Lean.Json) (key : String) : Result String := do
  asString (← field json key)

def natField (json : Lean.Json) (key : String) : Result Nat := do
  asNat (← field json key)

def levelOfNat : Nat → Level
  | 0 => .zero
  | n + 1 => .succ (levelOfNat n)

partial def parseExpr (json : Lean.Json) : Result Expr := do
  match field? json "sort", field? json "const", field? json "nat",
      field? json "app", field? json "forall", field? json "lam" with
  | some levelJson, none, none, none, none, none =>
      pure (.sort (levelOfNat (← asNat levelJson)))
  | none, some nameJson, none, none, none, none =>
      pure (.const (← asString nameJson) [])
  | none, none, some valueJson, none, none, none =>
      pure (.lit (.nat (← asNat valueJson)))
  | none, none, none, some argsJson, none, none => do
      let args ← asArray argsJson
      let some fnJson := args[0]?
        | fail "application is missing function"
      let some argJson := args[1]?
        | fail "application is missing argument"
      if args.size != 2 then
        fail "application takes exactly two entries"
      pure (.app (← parseExpr fnJson) (← parseExpr argJson))
  | none, none, none, none, some binderJson, none => do
      pure
        (.forallE
          (← stringField binderJson "name")
          (← parseExpr (← field binderJson "domain"))
          (← parseExpr (← field binderJson "body")))
  | none, none, none, none, none, some binderJson => do
      pure
        (.lam
          (← stringField binderJson "name")
          (← parseExpr (← field binderJson "domain"))
          (← parseExpr (← field binderJson "body")))
  | _, _, _, _, _, _ =>
      fail "expression entry must have exactly one supported form"

def parseConstructor (json : Lean.Json) : Result SimpleConstructorSpec := do
  pure { name := (← stringField json "name") }

def parseInductive (json : Lean.Json) : Result Declaration := do
  let ctorsJson ← asArray (← field json "constructors")
  let constructors ← ctorsJson.toList.mapM parseConstructor
  pure
    (.inductive
      {
        name := (← stringField json "name")
        resultLevel := levelOfNat (← natField json "level")
        constructors
      })

def parseDeclaration (json : Lean.Json) : Result Declaration := do
  match ← stringField json "decl" with
  | "axiom" =>
      pure (.axiom (← stringField json "name") [] (← parseExpr (← field json "type")))
  | "def" =>
      pure
        (.definition
          (← stringField json "name")
          []
          (← parseExpr (← field json "type"))
          (← parseExpr (← field json "value")))
  | "opaque" =>
      pure
        (.opaque
          (← stringField json "name")
          []
          (← parseExpr (← field json "type"))
          (← parseExpr (← field json "value")))
  | "theorem" =>
      pure
        (.theorem
          (← stringField json "name")
          []
          (← parseExpr (← field json "type"))
          (← parseExpr (← field json "value")))
  | "inductive" =>
      parseInductive json
  | kind => fail s!"unsupported NDJSON declaration kind: {kind}"

def parseAudit (json : Lean.Json) : Result Audit := do
  match ← stringField json "generated" with
  | "constructor" => pure { constructors := [← stringField json "name"] }
  | "recursor" => pure { recursors := [← stringField json "name"] }
  | kind => fail s!"unsupported generated audit kind: {kind}"

def mergeAudit (left right : Audit) : Audit :=
  {
    constructors := left.constructors ++ right.constructors
    recursors := left.recursors ++ right.recursors
  }

def parseEntry (state : ParseState) (json : Lean.Json) : Result ParseState := do
  if (field? json "generated").isSome then
    pure { state with audit := mergeAudit state.audit (← parseAudit json) }
  else
    pure { state with declarations := (← parseDeclaration json) :: state.declarations }

def parseLine (lineNumber : Nat) (state : ParseState) (line : String) : Result ParseState := do
  let trimmed := line.trimAscii.toString
  if trimmed.isEmpty then
    pure state
  else
    match Lean.Json.parse trimmed with
    | .ok json => parseEntry state json
    | .error err => fail s!"line {lineNumber}: invalid JSON: {err}"

partial def parseLinesLoop (lineNumber : Nat) (state : ParseState) :
    List String → Result ParseState
  | [] => pure state
  | line :: rest => do
      let state ← parseLine lineNumber state line
      parseLinesLoop (lineNumber + 1) state rest

def parseString (input : String) : Result ParseState :=
  parseLinesLoop 1 {} (input.splitOn "\n")

def auditGenerated (env : Env) (audit : Audit) : Result Unit := do
  for name in audit.constructors do
    match env.find? name with
    | some { kind := .constructor .., .. } => pure ()
    | some _ => fail s!"generated constructor audit found non-constructor: {name}"
    | none => fail s!"generated constructor audit found unknown name: {name}"
  for name in audit.recursors do
    match env.find? name with
    | some { kind := .recursor .., .. } => pure ()
    | some { kind := .nestedRecursor .., .. } => pure ()
    | some _ => fail s!"generated recursor audit found non-recursor: {name}"
    | none => fail s!"generated recursor audit found unknown name: {name}"

def checkString (manifest : Manifest) (input : String) : Result Env := do
  let state ← parseString input
  let env ← replay manifest emptyEnv state.declarations.reverse
  auditGenerated env state.audit
  pure env

end MPC.Adapters.NDJSON
