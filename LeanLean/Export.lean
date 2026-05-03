import Lean
import LeanLean.Checker

namespace LeanLean
namespace Export

structure State where
  names : Array Lean.Name := #[Lean.Name.anonymous]
  levels : Array Level := #[.zero]
  exprs : Array Expr := #[]
  declarations : List Declaration := []
  sawQuotientPrimitives : Bool := false
  deriving Inhabited

def field? (json : Lean.Json) (key : String) : Option Lean.Json :=
  (json.getObjVal? key).toOption

def field (json : Lean.Json) (key : String) : Result Lean.Json :=
  match json.getObjVal? key with
  | .ok value => pure value
  | .error err => .error s!"missing or malformed field {key}: {err}"

def asNat (json : Lean.Json) : Result Nat :=
  match json.getNat? with
  | .ok value => pure value
  | .error err => .error s!"expected natural number: {err}"

def asString (json : Lean.Json) : Result String :=
  match json.getStr? with
  | .ok value => pure value
  | .error err => .error s!"expected string: {err}"

def asBool (json : Lean.Json) : Result Bool :=
  match json.getBool? with
  | .ok value => pure value
  | .error err => .error s!"expected boolean: {err}"

def asArray (json : Lean.Json) : Result (Array Lean.Json) :=
  match json.getArr? with
  | .ok value => pure value
  | .error err => .error s!"expected array: {err}"

def natField (json : Lean.Json) (key : String) : Result Nat := do
  asNat (← field json key)

def stringField (json : Lean.Json) (key : String) : Result String := do
  asString (← field json key)

def boolField (json : Lean.Json) (key : String) : Result Bool := do
  asBool (← field json key)

def arrayField (json : Lean.Json) (key : String) : Result (Array Lean.Json) := do
  asArray (← field json key)

def appendIndexed {α : Type} (what : String) (array : Array α) (index : Nat) (value : α) :
    Result (Array α) :=
  if index = array.size then
    pure (array.push value)
  else
    .error s!"{what} index {index} is out of order; expected {array.size}"

def getIndexed {α : Type} (what : String) (array : Array α) (index : Nat) : Result α :=
  match array[index]? with
  | some value => pure value
  | none => .error s!"unknown {what} index: {index}"

def localName (name : Lean.Name) : Name :=
  toString name

def localBinderName : Lean.Name → String
  | .anonymous => "_"
  | name => toString name

def nameAt (state : State) (index : Nat) : Result Lean.Name :=
  getIndexed "name" state.names index

def localNameAt (state : State) (index : Nat) : Result Name := do
  pure (localName (← nameAt state index))

def localBinderNameAt (state : State) (index : Nat) : Result String := do
  pure (localBinderName (← nameAt state index))

def levelAt (state : State) (index : Nat) : Result Level :=
  getIndexed "level" state.levels index

def exprAt (state : State) (index : Nat) : Result Expr :=
  getIndexed "expression" state.exprs index

def nameListAt (state : State) (json : Lean.Json) : Result (List Name) := do
  let entries ← asArray json
  entries.toList.mapM fun entry => do
    localNameAt state (← asNat entry)

def levelParamList (state : State) (json : Lean.Json) : Result LevelContext :=
  nameListAt state json

def levelListAt (state : State) (json : Lean.Json) : Result (List Level) := do
  let entries ← asArray json
  entries.toList.mapM fun entry => do
    levelAt state (← asNat entry)

def parseNameEntry (state : State) (json : Lean.Json) : Result State := do
  let index ← natField json "in"
  let name ←
    match field? json "str", field? json "num" with
    | some strJson, none => do
        let pre ← nameAt state (← natField strJson "pre")
        pure (Lean.Name.str pre (← stringField strJson "str"))
    | none, some numJson => do
        let pre ← nameAt state (← natField numJson "pre")
        pure (Lean.Name.num pre (← natField numJson "i"))
    | _, _ => .error "name entry must have exactly one of str or num"
  pure { state with names := (← appendIndexed "name" state.names index name) }

def parseLevelEntry (state : State) (json : Lean.Json) : Result State := do
  let index ← natField json "il"
  let level ←
    match field? json "succ", field? json "max", field? json "imax", field? json "param" with
    | some levelJson, none, none, none =>
        pure (.succ (← levelAt state (← asNat levelJson)))
    | none, some levelsJson, none, none => do
        let levels ← asArray levelsJson
        let some leftJson := levels[0]?
          | .error "max level entry is missing its left operand"
        let some rightJson := levels[1]?
          | .error "max level entry is missing its right operand"
        if levels.size != 2 then
          .error "max level entry has too many operands"
        pure (.max (← levelAt state (← asNat leftJson)) (← levelAt state (← asNat rightJson)))
    | none, none, some levelsJson, none => do
        let levels ← asArray levelsJson
        let some leftJson := levels[0]?
          | .error "imax level entry is missing its left operand"
        let some rightJson := levels[1]?
          | .error "imax level entry is missing its right operand"
        if levels.size != 2 then
          .error "imax level entry has too many operands"
        pure (.imax (← levelAt state (← asNat leftJson)) (← levelAt state (← asNat rightJson)))
    | none, none, none, some nameJson =>
        pure (.param (← localNameAt state (← asNat nameJson)))
    | _, _, _, _ => .error "level entry must have exactly one level constructor"
  pure { state with levels := (← appendIndexed "level" state.levels index level) }

def parseNatLiteral (json : Lean.Json) : Result Nat := do
  let raw ← asString json
  match raw.toNat? with
  | some value => pure value
  | none => .error s!"invalid natural literal: {raw}"

def parseExprEntry (state : State) (json : Lean.Json) : Result State := do
  let index ← natField json "ie"
  let expr ←
    match
      field? json "bvar",
      field? json "sort",
      field? json "const",
      field? json "app",
      field? json "lam",
      field? json "forallE",
      field? json "letE",
      field? json "proj",
      field? json "natVal",
      field? json "strVal",
      field? json "mdata" with
    | some value, none, none, none, none, none, none, none, none, none, none =>
        pure (.bvar (← asNat value))
    | none, some value, none, none, none, none, none, none, none, none, none =>
        pure (.sort (← levelAt state (← asNat value)))
    | none, none, some value, none, none, none, none, none, none, none, none => do
        pure
          (.const
            (← localNameAt state (← natField value "name"))
            (← levelListAt state (← field value "us")))
    | none, none, none, some value, none, none, none, none, none, none, none =>
        pure (.app (← exprAt state (← natField value "fn")) (← exprAt state (← natField value "arg")))
    | none, none, none, none, some value, none, none, none, none, none, none =>
        pure
          (.lam
            (← localBinderNameAt state (← natField value "name"))
            (← exprAt state (← natField value "type"))
            (← exprAt state (← natField value "body")))
    | none, none, none, none, none, some value, none, none, none, none, none =>
        pure
          (.forallE
            (← localBinderNameAt state (← natField value "name"))
            (← exprAt state (← natField value "type"))
            (← exprAt state (← natField value "body")))
    | none, none, none, none, none, none, some value, none, none, none, none =>
        pure
          (.letE
            (← localBinderNameAt state (← natField value "name"))
            (← exprAt state (← natField value "type"))
            (← exprAt state (← natField value "value"))
            (← exprAt state (← natField value "body")))
    | none, none, none, none, none, none, none, some value, none, none, none =>
        pure
          (.proj
            (← localNameAt state (← natField value "typeName"))
            (← natField value "idx")
            (← exprAt state (← natField value "struct")))
    | none, none, none, none, none, none, none, none, some value, none, none =>
        pure (.lit (.natVal (← parseNatLiteral value)))
    | none, none, none, none, none, none, none, none, none, some value, none =>
        pure (.lit (.strVal (← asString value)))
    | none, none, none, none, none, none, none, none, none, none, some value =>
        exprAt state (← natField value "expr")
    | _, _, _, _, _, _, _, _, _, _, _ => .error "expression entry must have exactly one expression constructor"
  pure { state with exprs := (← appendIndexed "expression" state.exprs index expr) }

def parseReducibilityHint (json : Lean.Json) : Result ReducibilityHint := do
  match json with
  | .str "opaque" => pure .opaque
  | .str "abbrev" => pure .abbrev
  | _ =>
      match field? json "regular" with
      | some value => pure (.regular (← asNat value))
      | none => .error s!"unsupported reducibility hint: {json.compress}"

def requireSafeDefinition (name : Name) (json : Lean.Json) : Result Unit := do
  match ← asString json with
  | "safe" => pure ()
  | "unsafe" => .error s!"trusted replay rejects unsafe definition: {name}"
  | "partial" => .error s!"partial definition is outside the local export checker: {name}"
  | other => .error s!"unknown definition safety for {name}: {other}"

def requireSafeFlag (kind name : String) (json : Lean.Json) : Result Unit := do
  if (← asBool json) then
    .error s!"trusted replay rejects unsafe {kind}: {name}"
  else
    pure ()

def parseAxiom (state : State) (json : Lean.Json) : Result Declaration := do
  let name ← localNameAt state (← natField json "name")
  requireSafeFlag "axiom" name (← field json "isUnsafe")
  pure (.axiom name (← levelParamList state (← field json "levelParams")) (← exprAt state (← natField json "type")))

def parseDefinition (state : State) (json : Lean.Json) : Result Declaration := do
  let name ← localNameAt state (← natField json "name")
  requireSafeDefinition name (← field json "safety")
  pure
    (.definitionWithHint
      name
      (← levelParamList state (← field json "levelParams"))
      (← parseReducibilityHint (← field json "hints"))
      (← exprAt state (← natField json "type"))
      (← exprAt state (← natField json "value")))

def parseTheorem (state : State) (json : Lean.Json) : Result Declaration := do
  pure
    (.theorem
      (← localNameAt state (← natField json "name"))
      (← levelParamList state (← field json "levelParams"))
      (← exprAt state (← natField json "type"))
      (← exprAt state (← natField json "value")))

def parseOpaque (state : State) (json : Lean.Json) : Result Declaration := do
  let name ← localNameAt state (← natField json "name")
  requireSafeFlag "opaque definition" name (← field json "isUnsafe")
  pure
    (.opaqueDefinition
      name
      (← levelParamList state (← field json "levelParams"))
      (← exprAt state (← natField json "type"))
      (← exprAt state (← natField json "value")))

def parseKernelConstructor (state : State) (json : Lean.Json) : Result KernelConstructorDecl := do
  let name ← localNameAt state (← natField json "name")
  requireSafeFlag "constructor" name (← field json "isUnsafe")
  pure { name, type := (← exprAt state (← natField json "type")) }

def parseKernelInductiveType
    (state : State)
    (ctors : Array Lean.Json)
    (json : Lean.Json) : Result KernelInductiveTypeDecl := do
  let name ← localNameAt state (← natField json "name")
  requireSafeFlag "inductive declaration" name (← field json "isUnsafe")
  let ctorNames ← nameListAt state (← field json "ctors")
  let ctorDecls ← ctorNames.mapM fun ctorName => do
    let some ctorJson := ctors.find? (fun candidate =>
      match (do
        let index ← natField candidate "name"
        localNameAt state index) with
      | .ok candidateName => candidateName = ctorName
      | .error _ => false)
      | .error s!"inductive {name} is missing constructor record {ctorName}"
    parseKernelConstructor state ctorJson
  pure { name, type := (← exprAt state (← natField json "type")), ctors := ctorDecls }

def parseGeneratedConstructor (state : State) (json : Lean.Json) : Result Declaration := do
  let name ← localNameAt state (← natField json "name")
  requireSafeFlag "constructor" name (← field json "isUnsafe")
  pure
    (.generatedConstructor
      name
      (← levelParamList state (← field json "levelParams"))
      (← exprAt state (← natField json "type"))
      (← localNameAt state (← natField json "induct")))

def parseGeneratedRecursorRule (state : State) (json : Lean.Json) : Result GeneratedRecursorRuleInfo := do
  pure
    {
      ctor := (← localNameAt state (← natField json "ctor"))
      nfields := (← natField json "nfields")
      rhs? := some (← exprAt state (← natField json "rhs"))
    }

def parseGeneratedRecursor (state : State) (json : Lean.Json) : Result Declaration := do
  let name ← localNameAt state (← natField json "name")
  requireSafeFlag "recursor" name (← field json "isUnsafe")
  let rulesJson ← arrayField json "rules"
  pure
    (.generatedRecursorWithInfo
      name
      (← levelParamList state (← field json "levelParams"))
      (← exprAt state (← natField json "type"))
      {
        all := (← nameListAt state (← field json "all"))
        numParams := (← natField json "numParams")
        numIndices := (← natField json "numIndices")
        numMotives := (← natField json "numMotives")
        numMinors := (← natField json "numMinors")
        rules := (← rulesJson.toList.mapM (parseGeneratedRecursorRule state))
      })

def parseInductiveGroup (state : State) (json : Lean.Json) : Result (List Declaration) := do
  let typesJson ← arrayField json "types"
  let ctorsJson ← arrayField json "ctors"
  let recsJson ← arrayField json "recs"
  let some firstType := typesJson[0]?
    | .error "inductive group has no type records"
  let kernelTypes ← typesJson.toList.mapM (parseKernelInductiveType state ctorsJson)
  let generatedCtors ← ctorsJson.toList.mapM (parseGeneratedConstructor state)
  let generatedRecs ← recsJson.toList.mapM (parseGeneratedRecursor state)
  pure <|
    (Declaration.kernelInductive
      {
        levelParams := (← levelParamList state (← field firstType "levelParams"))
        numParams := (← natField firstType "numParams")
        types := kernelTypes
      }) :: (generatedCtors ++ generatedRecs)

def parseDeclaration (state : State) (json : Lean.Json) : Result (State × List Declaration) := do
  match
    field? json "axiom",
    field? json "def",
    field? json "thm",
    field? json "opaque",
    field? json "quot",
    field? json "inductive" with
  | some value, none, none, none, none, none => pure (state, [← parseAxiom state value])
  | none, some value, none, none, none, none => pure (state, [← parseDefinition state value])
  | none, none, some value, none, none, none => pure (state, [← parseTheorem state value])
  | none, none, none, some value, none, none => pure (state, [← parseOpaque state value])
  | none, none, none, none, some _, none =>
      if state.sawQuotientPrimitives then
        pure (state, [])
      else
        pure ({ state with sawQuotientPrimitives := true }, [.quotientPrimitives])
  | none, none, none, none, none, some value => pure (state, (← parseInductiveGroup state value))
  | _, _, _, _, _, _ => .error "export declaration entry must have exactly one declaration constructor"

def parseEntry (lineNumber : Nat) (state : State) (json : Lean.Json) : Result State := do
  let parseError {α : Type} (err : String) : Result α := .error s!"line {lineNumber}: {err}"
  if (field? json "meta").isSome then
    pure state
  else if (field? json "in").isSome then
    match parseNameEntry state json with
    | .ok state => pure state
    | .error err => parseError err
  else if (field? json "il").isSome then
    match parseLevelEntry state json with
    | .ok state => pure state
    | .error err => parseError err
  else if (field? json "ie").isSome then
    match parseExprEntry state json with
    | .ok state => pure state
    | .error err => parseError err
  else
    match parseDeclaration state json with
    | .ok (state, declarations) =>
        pure { state with declarations := state.declarations ++ declarations }
    | .error err => parseError err

def parseLine (lineNumber : Nat) (state : State) (line : String) : Result State := do
  let trimmed := line.trimAscii.toString
  if trimmed.isEmpty then
    pure state
  else
    match Lean.Json.parse trimmed with
    | .ok json => parseEntry lineNumber state json
    | .error err => .error s!"line {lineNumber}: invalid JSON: {err}"

partial def parseLinesLoop (lineNumber : Nat) (state : State) : List String → Result State
  | [] => pure state
  | line :: rest => do
      let state ← parseLine lineNumber state line
      parseLinesLoop (lineNumber + 1) state rest

def parseDeclarations (input : String) : Result (List Declaration) := do
  let state ← parseLinesLoop 1 {} (input.splitOn "\n")
  pure state.declarations

def checkString (input : String) : Checker.Outcome :=
  match parseDeclarations input with
  | .error err => .unsupported err
  | .ok declarations =>
      match replayDeclarations [] declarations with
      | .ok _ => .accepted s!"checked {declarations.length} declaration entries"
      | .error err => .rejected err

end Export
end LeanLean
