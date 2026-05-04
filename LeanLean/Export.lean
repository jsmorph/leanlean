import Lean
import LeanLean.Checker

namespace LeanLean
namespace Export

structure State where
  names : Array Lean.Name := #[Lean.Name.anonymous]
  levels : Array Level := #[.zero]
  exprs : Array Expr := #[]
  declarationsRev : List Declaration := []
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
  Import.translateName name

def localBinderName : Lean.Name → String
  | .anonymous => "_"
  | name => toString name

def nameAt (state : State) (index : Nat) : Result Lean.Name :=
  getIndexed "name" state.names index

def localNameAt (state : State) (index : Nat) : Result Name := do
  let name ← nameAt state index
  pure (localName name)

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

def quotientPrimitiveForKind (kind : String) : Result (Name × PrimitiveInfo) :=
  match kind with
  | "type" => pure ("Quot", .quotType)
  | "ctor" => pure ("Quot.mk", .quotMk)
  | "lift" => pure ("Quot.lift", .quotLift)
  | "ind" => pure ("Quot.ind", .quotInd)
  | other => .error s!"unsupported quotient export kind: {other}"

def parseQuotientPrimitiveCheck (state : State) (json : Lean.Json) : Result Declaration := do
  let kind ← stringField json "kind"
  let (expectedName, primitive) ← quotientPrimitiveForKind kind
  let name ← localNameAt state (← natField json "name")
  if name != expectedName then
    .error s!"quotient export kind {kind} used unexpected name {name}"
  else
    pure
      (.primitiveCheck
        name
        (← levelParamList state (← field json "levelParams"))
        (← exprAt state (← natField json "type"))
        primitive)

def withQuotientPrimitives (state : State) (checks : List Declaration) :
    State × List Declaration :=
  if state.sawQuotientPrimitives then
    (state, checks)
  else
    ({ state with sawQuotientPrimitives := true }, .quotientPrimitives :: checks)

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
        k := (← boolField json "k")
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
  | some value, none, none, none, none, none =>
      match ← parseAxiom state value with
      | .axiom "Quot.sound" levelParams type =>
          pure <| withQuotientPrimitives state [.primitiveCheck "Quot.sound" levelParams type .quotSound]
      | declaration => pure (state, [declaration])
  | none, some value, none, none, none, none => pure (state, [← parseDefinition state value])
  | none, none, some value, none, none, none => pure (state, [← parseTheorem state value])
  | none, none, none, some value, none, none => pure (state, [← parseOpaque state value])
  | none, none, none, none, some value, none =>
      pure <| withQuotientPrimitives state [← parseQuotientPrimitiveCheck state value]
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
        pure
          {
            state with
            declarationsRev :=
              declarations.foldl
                (fun entries declaration => declaration :: entries)
                state.declarationsRev
          }
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
  pure state.declarationsRev.reverse

def rootContains (roots : List Name) (name : Name) : Bool :=
  roots.any fun root => root == name

def trustedDefinitionValueNeeded (name : Name) : Bool :=
  name == "outParam" ||
    name == "semiOutParam" ||
    name == "optParam" ||
    name == "Unit" ||
    name == "OfNat.ofNat" ||
    name == "instOfNatNat" ||
    name == "Nat.add" ||
    name == "Nat.mul" ||
    name == "Nat.pow" ||
    name == "Nat.sub" ||
    name == "Nat.beq" ||
    name == "Nat.ble" ||
    name == "DecidableEq"

def recursiveAuxSupportName (name : Name) : Bool :=
  name.endsWith ".below" ||
    name.endsWith ".brecOn" ||
    name.endsWith ".brecOn.go" ||
    name.endsWith ".brecOn.eq"

def shouldAssumeNonRoot (roots : List Name) : Declaration → Bool
  | .definition name .. =>
      !rootContains roots name && !recursiveAuxSupportName name
  | .definitionWithHint name .. =>
      !rootContains roots name && !recursiveAuxSupportName name
  | .opaqueDefinition name .. => !rootContains roots name
  | .theorem name .. => !rootContains roots name
  | .axiom name .. => !rootContains roots name
  | _ => false

def shouldTrustNonRootCheck (roots : List Name) : Declaration → Bool
  | .generatedConstructor name .. => !rootContains roots name
  | .generatedRecursor name .. => !rootContains roots name
  | .generatedRecursorWithInfo name .. => !rootContains roots name
  | .primitiveCheck name .. => !rootContains roots name
  | _ => false

def trustedBaseForDeclaration? : Declaration → Option (List ConstantInfo)
  | .axiom name levelParams type => some [ConstantInfo.mkAxiom name levelParams type]
  | .definition name levelParams type value =>
      if trustedDefinitionValueNeeded name then
        some [ConstantInfo.mkDefn name levelParams type value]
      else
        some [ConstantInfo.mkAxiom name levelParams type]
  | .definitionWithHint name levelParams hint type value =>
      if trustedDefinitionValueNeeded name then
        some [ConstantInfo.mkDefnWithHint name levelParams type value hint]
      else
        some [ConstantInfo.mkAxiom name levelParams type]
  | .opaqueDefinition name levelParams type _ => some [ConstantInfo.mkAxiom name levelParams type]
  | .theorem name levelParams type _ => some [ConstantInfo.mkAxiom name levelParams type]
  | _ => none

inductive GapStatus where
  | checked
  | generatedCompared
  | rejected
  | assumedAfterRejection
  | unsupported
  | assumed
  | trustedCheck
  deriving DecidableEq, Repr

def GapStatus.label : GapStatus → String
  | .checked => "checked"
  | .generatedCompared => "generated-compared"
  | .rejected => "rejected"
  | .assumedAfterRejection => "assumed-after-rejection"
  | .unsupported => "unsupported"
  | .assumed => "assumed"
  | .trustedCheck => "trusted-check"

def joinStringsWith (separator : String) : List String → String
  | [] => ""
  | [value] => value
  | value :: rest => value ++ separator ++ joinStringsWith separator rest

def joinStrings (values : List String) : String :=
  joinStringsWith "," values

def joinLines (values : List String) : String :=
  joinStringsWith "\n" values

def joinNames (names : List Name) : String :=
  joinStrings names

def displayNames : List Name → String
  | [] => "none"
  | names => joinNames names

def declarationKind : Declaration → String
  | .axiom .. => "axiom"
  | .definition .. => "definition"
  | .definitionWithHint .. => "definition"
  | .opaqueDefinition .. => "opaque"
  | .theorem .. => "theorem"
  | .inductive .. => "inductive"
  | .inductiveBlock .. => "inductive-block"
  | .kernelInductive .. => "kernel-inductive"
  | .generatedConstructor .. => "generated-constructor"
  | .generatedRecursor .. => "generated-recursor"
  | .generatedRecursorWithInfo .. => "generated-recursor"
  | .structureInfo .. => "structure-info"
  | .projection .. => "projection"
  | .quotientPrimitives => "quotient-primitives"
  | .primitiveCheck .. => "primitive-check"

def primaryReplayName (declaration : Declaration) : Name :=
  match declarationReplayNames declaration with
  | name :: _ => name
  | [] => "_anonymous"

def generatedClassName (name : Name) : String :=
  if recursiveAuxSupportName name then
    "recursive-aux"
  else if name.contains ".match_" then
    "match-helper"
  else if name.contains ".noConfusion" then
    "no-confusion"
  else if name.endsWith ".ctorElim" then
    "constructor-eliminator"
  else if name.contains "_sparseCasesOn_" || name.contains "._sparseCasesOn_" then
    "sparse-case-helper"
  else if name.contains ".repr" || name.contains ".instRepr" then
    "repr-support"
  else if name.contains ".instDecidable" then
    "derived-decidable"
  else if name.contains ".instInhabited" then
    "derived-inhabited"
  else if name.contains ".instBEq" || name.startsWith "inst" then
    "derived-instance"
  else if name.contains "_proof_" then
    "generated-proof"
  else if name.contains "._" then
    "private-or-aux"
  else
    "ordinary"

def declarationClassName (declaration : Declaration) : String :=
  match declaration with
  | .generatedConstructor name ..
  | .generatedRecursor name ..
  | .generatedRecursorWithInfo name ..
  | .primitiveCheck name .. => generatedClassName name
  | _ => generatedClassName (primaryReplayName declaration)

def admittedPrimitiveNames : List Name :=
  ["Nat.add", "Nat.mul", "Nat.pow", "Nat.sub", "Nat.beq", "Nat.ble"]

def declarationPrimitiveDependencies (declaration : Declaration) : List Name :=
  declaration.usedConstants.filter fun name => admittedPrimitiveNames.contains name

def generatedComparisonDeclaration : Declaration → Bool
  | .generatedConstructor .. => true
  | .generatedRecursor .. => true
  | .generatedRecursorWithInfo .. => true
  | .primitiveCheck .. => true
  | _ => false

structure GapRow where
  names : List Name
  kind : String
  className : String
  dependencyCount : Nat
  primitiveDependencies : List Name
  status : GapStatus
  message : String

structure GapSummary where
  status : GapStatus
  kind : String
  className : String
  count : Nat

structure GapReportState where
  env : Env
  rowsRev : List GapRow

def addGapSummary (summaries : List GapSummary) (row : GapRow) : List GapSummary :=
  match summaries with
  | [] => [{ status := row.status, kind := row.kind, className := row.className, count := 1 }]
  | summary :: rest =>
      if summary.status == row.status &&
          summary.kind == row.kind &&
          summary.className == row.className then
        { summary with count := summary.count + 1 } :: rest
      else
        summary :: addGapSummary rest row

def gapSummaries (rows : List GapRow) : List GapSummary :=
  rows.foldl addGapSummary []

def gapSummaryLine (summary : GapSummary) : String :=
  s!"summary: status={summary.status.label} kind={summary.kind} class={summary.className} count={summary.count}"

def gapDetailLine (row : GapRow) : String :=
  let primitiveText :=
    match row.primitiveDependencies with
    | [] => "none"
    | names => joinNames names
  let message :=
    if row.message.isEmpty then
      ""
    else
      s!" message={row.message}"
  s!"detail: status={row.status.label} kind={row.kind} class={row.className} \
    names={displayNames row.names} dependencies={row.dependencyCount} primitives={primitiveText}{message}"

def addTrustedGapEntries
    (env : Env)
    (names : List Name)
    (infos : List ConstantInfo) : Result Env := do
  let mut env := env
  for info in infos do
    if env.contains info.name then
      .error s!"duplicate trusted-base declaration: {info.name}"
    else if !names.contains info.name then
      .error s!"trusted-base declaration name mismatch: {info.name}"
    else
      env := info :: env
  pure env

def trustedEnvironmentAfterRejection (env : Env) (declaration : Declaration) :
    Result (Option Env) := do
  match trustedBaseForDeclaration? declaration with
  | none => pure none
  | some infos =>
      pure (some (← addTrustedGapEntries env declaration.definedNames infos))

def replayGapRow (declaration : Declaration) (status : GapStatus) (message : String) :
    GapRow :=
  {
    names := declarationReplayNames declaration
    kind := declarationKind declaration
    className := declarationClassName declaration
    dependencyCount := declaration.usedConstants.length
    primitiveDependencies := declarationPrimitiveDependencies declaration
    status
    message
  }

def unsupportedGapRow (message : String) : GapRow :=
  {
    names := []
    kind := "parse-entry"
    className := "unsupported"
    dependencyCount := 0
    primitiveDependencies := []
    status := .unsupported
    message
  }

def analyzeGapDeclaration
    (state : GapReportState)
    (declaration : Declaration) : Result GapReportState := do
  match addDeclaration state.env declaration with
  | .ok env =>
      let status :=
        if generatedComparisonDeclaration declaration then
          .generatedCompared
        else
          .checked
      pure { env, rowsRev := replayGapRow declaration status "" :: state.rowsRev }
  | .error err =>
      match ← trustedEnvironmentAfterRejection state.env declaration with
      | some env =>
          pure
            {
              env
              rowsRev :=
                replayGapRow declaration .assumedAfterRejection err :: state.rowsRev
            }
      | none =>
          pure
            {
              state with
              rowsRev := replayGapRow declaration .rejected err :: state.rowsRev
            }

partial def replayGapRowsWithFuel
    (fuel : Nat)
    (state : GapReportState)
    (declarations : List Declaration) : Result GapReportState := do
  match declarations with
  | [] => pure state
  | _ =>
      match fuel with
      | 0 => declarations.foldlM analyzeGapDeclaration state
      | fuel + 1 =>
          let mut state := state
          let mut remaining : List Declaration := []
          let mut progressed := false
          for declaration in declarations do
            if declarationReady state.env declaration then
              state ← analyzeGapDeclaration state declaration
              progressed := true
            else
              remaining := declaration :: remaining
          let pending := remaining.reverse
          if progressed then
            replayGapRowsWithFuel fuel state pending
          else
            pending.foldlM analyzeGapDeclaration state

def replayGapRows (declarations : List Declaration) : Result (List GapRow) := do
  let state ←
    replayGapRowsWithFuel
      (declarations.length + 1)
      { env := [], rowsRev := [] }
      declarations
  pure state.rowsRev.reverse

def formatReplayGapReport (declarations : List Declaration) : Result String := do
  let ordered : Checker.Outcome :=
    match addDeclarations [] declarations with
    | .ok _ => .accepted s!"checked {declarations.length} declaration entries"
    | .error err => .rejected err
  let dependencyAware : Checker.Outcome :=
    match replayDeclarations [] declarations with
    | .ok _ => .accepted s!"checked {declarations.length} declaration entries"
    | .error err => .rejected err
  let rows ← replayGapRows declarations
  let header :=
    s!"ordered-outcome: {ordered.label}\n" ++
    s!"ordered-message: {ordered.message}\n" ++
    s!"dependency-aware-outcome: {dependencyAware.label}\n" ++
    s!"dependency-aware-message: {dependencyAware.message}\n" ++
    s!"declarations: {declarations.length}"
  let summaries :=
    "\n" ++ joinLines ((gapSummaries rows).map gapSummaryLine)
  let rejectedRows :=
    rows.filter fun row =>
      row.status == .rejected || row.status == .assumedAfterRejection
  let details :=
    if rejectedRows.isEmpty then
      ""
    else
      "\n" ++ joinLines (rejectedRows.map gapDetailLine)
  pure (header ++ summaries ++ details)

def formatUnsupportedGapReport (message : String) : String :=
  let row := unsupportedGapRow message
  "parse-outcome: unsupported\n" ++
    s!"parse-message: {message}\n" ++
    "declarations: 0\n" ++
    gapSummaryLine { status := .unsupported, kind := row.kind, className := row.className, count := 1 } ++
    "\n" ++ gapDetailLine row

structure RootedCheckResult where
  env : Env
  checked : Nat
  assumed : Nat
  trustedChecks : Nat

structure RootedGapState where
  env : Env
  rowsRev : List GapRow

def addTrustedBaseEntries
    (state : RootedCheckResult)
    (names : List Name)
    (infos : List ConstantInfo) : Result RootedCheckResult := do
  let mut env := state.env
  let mut assumed := state.assumed
  for info in infos do
    if env.contains info.name then
      .error s!"duplicate trusted-base declaration: {info.name}"
    else if !names.contains info.name then
      .error s!"trusted-base declaration name mismatch: {info.name}"
    else
      env := info :: env
      assumed := assumed + 1
  pure { state with env, assumed }

def checkRootedDeclaration
    (roots : List Name)
    (state : RootedCheckResult)
    (declaration : Declaration) : Result RootedCheckResult := do
  if shouldTrustNonRootCheck roots declaration then
    pure { state with trustedChecks := state.trustedChecks + 1 }
  else if shouldAssumeNonRoot roots declaration then
    match trustedBaseForDeclaration? declaration with
    | some infos => addTrustedBaseEntries state declaration.definedNames infos
    | none =>
        .error s!"cannot assume declaration: {repr declaration.definedNames}"
  else
    match addDeclaration state.env declaration with
    | .ok env => pure { state with env, checked := state.checked + 1 }
    | .error err =>
        .error s!"while replaying {repr (declarationReplayNames declaration)}: {err}"

def analyzeRootedGapDeclaration
    (roots : List Name)
    (state : RootedGapState)
    (declaration : Declaration) : RootedGapState :=
  if shouldTrustNonRootCheck roots declaration then
    { state with rowsRev := replayGapRow declaration .trustedCheck "" :: state.rowsRev }
  else if shouldAssumeNonRoot roots declaration then
    match trustedBaseForDeclaration? declaration with
    | some infos =>
        match addTrustedGapEntries state.env declaration.definedNames infos with
        | .ok env =>
            {
              env
              rowsRev := replayGapRow declaration .assumed "" :: state.rowsRev
            }
        | .error err =>
            { state with rowsRev := replayGapRow declaration .rejected err :: state.rowsRev }
    | none =>
        let err := s!"cannot assume declaration: {repr declaration.definedNames}"
        { state with rowsRev := replayGapRow declaration .rejected err :: state.rowsRev }
  else
    match addDeclaration state.env declaration with
    | .ok env =>
        let status :=
          if generatedComparisonDeclaration declaration then
            .generatedCompared
          else
            .checked
        { env, rowsRev := replayGapRow declaration status "" :: state.rowsRev }
    | .error err =>
        let message := s!"while replaying {repr (declarationReplayNames declaration)}: {err}"
        { state with rowsRev := replayGapRow declaration .rejected message :: state.rowsRev }

def rootedReplayGapRows (roots : List Name) (declarations : List Declaration) : List GapRow :=
  let state :=
    declarations.foldl
      (fun state declaration => analyzeRootedGapDeclaration roots state declaration)
      { env := [], rowsRev := [] }
  state.rowsRev.reverse

def rootedGapOutcomeLine (declarations : List Declaration) (rows : List GapRow) : String :=
  match rows.find? (fun row => row.status == .rejected) with
  | some row =>
      "rooted-outcome: rejected\n" ++
        s!"rooted-message: {row.message}"
  | none =>
      "rooted-outcome: accepted\n" ++
        s!"rooted-message: classified {declarations.length} declaration entries"

def formatRootedReplayGapReport
    (roots : List Name)
    (declarations : List Declaration) : String :=
  let rows := rootedReplayGapRows roots declarations
  let header :=
    rootedGapOutcomeLine declarations rows ++ "\n" ++
    s!"roots: {roots.length}\n" ++
    s!"declarations: {declarations.length}"
  let summaries :=
    "\n" ++ joinLines ((gapSummaries rows).map gapSummaryLine)
  let rejectedRows := rows.filter fun row => row.status == .rejected
  let details :=
    if rejectedRows.isEmpty then
      ""
    else
      "\n" ++ joinLines (rejectedRows.map gapDetailLine)
  header ++ summaries ++ details

def checkDeclarationsWithRootAssumptions
    (roots : List Name)
    (declarations : List Declaration) : Checker.Outcome :=
  match
    declarations.foldlM
      (fun state declaration => checkRootedDeclaration roots state declaration)
      { env := [], checked := 0, assumed := 0, trustedChecks := 0 }
  with
  | .ok state =>
      .accepted
        (s!"checked {state.checked} declaration entries; assumed {state.assumed} trusted-base entries; " ++
          s!"trusted {state.trustedChecks} generated or primitive checks")
  | .error err => .rejected err

def checkDeclarationsOrdered (declarations : List Declaration) : Checker.Outcome :=
  match addDeclarations [] declarations with
  | .ok _ => .accepted s!"checked {declarations.length} declaration entries"
  | .error err => .rejected err

def checkDeclarationsDependencyAware (declarations : List Declaration) : Checker.Outcome :=
  match replayDeclarations [] declarations with
  | .ok _ => .accepted s!"checked {declarations.length} declaration entries"
  | .error err => .rejected err

def checkStringOrdered (input : String) : Checker.Outcome :=
  match parseDeclarations input with
  | .error err => .unsupported err
  | .ok declarations => checkDeclarationsOrdered declarations

def checkStringDependencyAware (input : String) : Checker.Outcome :=
  match parseDeclarations input with
  | .error err => .unsupported err
  | .ok declarations => checkDeclarationsDependencyAware declarations

def checkStringWithRootAssumptions (input : String) (roots : List Name) : Checker.Outcome :=
  match parseDeclarations input with
  | .error err => .unsupported err
  | .ok declarations => checkDeclarationsWithRootAssumptions roots declarations

def replayGapReportString (input : String) : Checker.Outcome :=
  match parseDeclarations input with
  | .error err => .accepted (formatUnsupportedGapReport err)
  | .ok declarations =>
      match formatReplayGapReport declarations with
      | .ok report => .accepted report
      | .error err => .internalFailure err

def rootedReplayGapReportString (input : String) (roots : List Name) : Checker.Outcome :=
  match parseDeclarations input with
  | .error err => .accepted (formatUnsupportedGapReport err)
  | .ok declarations => .accepted (formatRootedReplayGapReport roots declarations)

def checkString (input : String) : Checker.Outcome :=
  checkStringOrdered input

end Export
end LeanLean
