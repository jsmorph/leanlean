import Lean
import MPC.Configs.LeanCore429

namespace MPC.Adapters.Export

structure Audit where
  constructors : List Name := []
  recursors : List Name := []
  deriving BEq, Repr, Inhabited

structure ParseState where
  declarations : List Declaration := []
  audit : Audit := {}
  deriving BEq, Repr, Inhabited

structure State where
  names : Array Lean.Name := #[Lean.Name.anonymous]
  levels : Array Level := #[.zero]
  exprs : Array Expr := #[]
  declarationsRev : List Declaration := []
  audit : Audit := {}
  sawEqualityPrimitives : Bool := false
  sawQuotientPrimitives : Bool := false
  deriving Inhabited

structure KernelConstructorDecl where
  name : Name
  type : Expr
  deriving BEq, Repr, Inhabited

structure KernelInductiveTypeDecl where
  name : Name
  type : Expr
  ctors : List KernelConstructorDecl
  deriving BEq, Repr, Inhabited

structure KernelInductiveDecl where
  levelParams : LevelContext := []
  numParams : Nat
  types : List KernelInductiveTypeDecl
  deriving BEq, Repr, Inhabited

def field? (json : Lean.Json) (key : String) : Option Lean.Json :=
  (json.getObjVal? key).toOption

def field (json : Lean.Json) (key : String) : Result Lean.Json :=
  match json.getObjVal? key with
  | .ok value => pure value
  | .error err => fail s!"missing or malformed field {key}: {err}"

def asNat (json : Lean.Json) : Result Nat :=
  match json.getNat? with
  | .ok value => pure value
  | .error err => fail s!"expected natural number: {err}"

def asString (json : Lean.Json) : Result String :=
  match json.getStr? with
  | .ok value => pure value
  | .error err => fail s!"expected string: {err}"

def asBool (json : Lean.Json) : Result Bool :=
  match json.getBool? with
  | .ok value => pure value
  | .error err => fail s!"expected boolean: {err}"

def asArray (json : Lean.Json) : Result (Array Lean.Json) :=
  match json.getArr? with
  | .ok value => pure value
  | .error err => fail s!"expected array: {err}"

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
    fail s!"{what} index {index} is out of order; expected {array.size}"

def getIndexed {α : Type} (what : String) (array : Array α) (index : Nat) : Result α :=
  match array[index]? with
  | some value => pure value
  | none => fail s!"unknown {what} index: {index}"

def encodedNamePrefix : String :=
  "__leanlean_name:"

def ordinaryNameComponent (component : String) : Bool :=
  toString (Lean.Name.str Lean.Name.anonymous component) == component

def ordinaryLeanName : Lean.Name → Bool
  | .anonymous => true
  | .str parent component =>
      ordinaryLeanName parent && ordinaryNameComponent component
  | .num parent _ =>
      ordinaryLeanName parent

def encodeLeanNameStructural : Lean.Name → String
  | .anonymous => "A"
  | .str parent component =>
      "S" ++ encodeLeanNameStructural parent ++ toString component.length ++ ":" ++ component
  | .num parent index =>
      "N" ++ encodeLeanNameStructural parent ++ toString index ++ ";"

def localName (name : Lean.Name) : Name :=
  let text := toString name
  if ordinaryLeanName name && !text.startsWith encodedNamePrefix then
    text
  else
    encodedNamePrefix ++ encodeLeanNameStructural name

def localBinderName : Lean.Name → String
  | .anonymous => "_"
  | name => localName name

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
    | _, _ => fail "name entry must have exactly one of str or num"
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
          | fail "max level entry is missing its left operand"
        let some rightJson := levels[1]?
          | fail "max level entry is missing its right operand"
        if levels.size != 2 then
          fail "max level entry has too many operands"
        pure (.max (← levelAt state (← asNat leftJson)) (← levelAt state (← asNat rightJson)))
    | none, none, some levelsJson, none => do
        let levels ← asArray levelsJson
        let some leftJson := levels[0]?
          | fail "imax level entry is missing its left operand"
        let some rightJson := levels[1]?
          | fail "imax level entry is missing its right operand"
        if levels.size != 2 then
          fail "imax level entry has too many operands"
        pure (.imax (← levelAt state (← asNat leftJson)) (← levelAt state (← asNat rightJson)))
    | none, none, none, some nameJson =>
        pure (.param (← localNameAt state (← asNat nameJson)))
    | _, _, _, _ => fail "level entry must have exactly one level constructor"
  pure { state with levels := (← appendIndexed "level" state.levels index level) }

def parseNatLiteral (json : Lean.Json) : Result Nat := do
  let raw ← asString json
  match raw.toNat? with
  | some value => pure value
  | none => fail s!"invalid natural literal: {raw}"

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
    | none, none, some value, none, none, none, none, none, none, none, none =>
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
        pure (.lit (.nat (← parseNatLiteral value)))
    | none, none, none, none, none, none, none, none, none, some value, none =>
        pure (.lit (.str (← asString value)))
    | none, none, none, none, none, none, none, none, none, none, some value =>
        exprAt state (← natField value "expr")
    | _, _, _, _, _, _, _, _, _, _, _ => fail "expression entry must have exactly one expression constructor"
  pure { state with exprs := (← appendIndexed "expression" state.exprs index expr) }

def requireSafeDefinition (name : Name) (json : Lean.Json) : Result Unit := do
  match ← asString json with
  | "safe" => pure ()
  | "unsafe" => fail s!"trusted replay rejects unsafe definition: {name}"
  | "partial" => fail s!"partial definition is outside the MPC export adapter: {name}"
  | other => fail s!"unknown definition safety for {name}: {other}"

def requireSafeFlag (kind name : String) (json : Lean.Json) : Result Unit := do
  if (← asBool json) then
    fail s!"trusted replay rejects unsafe {kind}: {name}"
  else
    pure ()

def withEqualityPrimitives (state : State) : State × List Declaration :=
  if state.sawEqualityPrimitives then
    (state, [])
  else
    ({ state with sawEqualityPrimitives := true }, [.equalityPrimitives])

def withQuotientPrimitives (state : State) : State × List Declaration :=
  let (state, equalityDecls) := withEqualityPrimitives state
  if state.sawQuotientPrimitives then
    (state, equalityDecls)
  else
    ({ state with sawQuotientPrimitives := true }, equalityDecls ++ [.quotientPrimitives])

def parseAxiom (state : State) (json : Lean.Json) : Result (State × List Declaration) := do
  let name ← localNameAt state (← natField json "name")
  requireSafeFlag "axiom" name (← field json "isUnsafe")
  if name == "Quot.sound" then
    pure (withQuotientPrimitives state)
  else
    pure
      (state,
        [.axiom name (← levelParamList state (← field json "levelParams"))
          (← exprAt state (← natField json "type"))])

def expectedQuotientName (kind : String) : Result Name :=
  match kind with
  | "type" => pure "Quot"
  | "ctor" => pure "Quot.mk"
  | "lift" => pure "Quot.lift"
  | "ind" => pure "Quot.ind"
  | other => fail s!"unsupported quotient export kind: {other}"

def parseQuotientPrimitive (state : State) (json : Lean.Json) : Result (State × List Declaration) := do
  let kind ← stringField json "kind"
  let expectedName ← expectedQuotientName kind
  let name ← localNameAt state (← natField json "name")
  if name != expectedName then
    fail s!"quotient export kind {kind} used unexpected name {name}"
  else
    pure (withQuotientPrimitives state)

def parseDefinition (state : State) (json : Lean.Json) : Result Declaration := do
  let name ← localNameAt state (← natField json "name")
  requireSafeDefinition name (← field json "safety")
  pure
    (.definition
      name
      (← levelParamList state (← field json "levelParams"))
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
    (.opaque
      name
      (← levelParamList state (← field json "levelParams"))
      (← exprAt state (← natField json "type"))
      (← exprAt state (← natField json "value")))

def decomposeForalls : Expr → List Binder × Expr
  | .forallE name type body =>
      let (binders, result) := decomposeForalls body
      ({ name, type } :: binders, result)
  | expr => ([], expr)

def splitAt? (n : Nat) (xs : List α) : Option (List α × List α) :=
  if n <= xs.length then
    some (xs.take n, xs.drop n)
  else
    none

def binderTypesAlphaEq (left right : List Binder) : Bool :=
  left.length == right.length &&
    (left.zip right).all fun pair => pair.1.type.alphaEq pair.2.type

def exprListAlphaEq (left right : List Expr) : Bool :=
  left.length == right.length &&
    (left.zip right).all fun pair => pair.1.alphaEq pair.2

def levelListDefEq (left right : List Level) : Bool :=
  left.length == right.length &&
    (left.zip right).all fun pair => pair.1.defEq pair.2

def expectedLevelArgs (levelParams : LevelContext) : List Level :=
  levelParams.map .param

def parseKernelConstructor (state : State) (json : Lean.Json) : Result KernelConstructorDecl := do
  let name ← localNameAt state (← natField json "name")
  requireSafeFlag "constructor" name (← field json "isUnsafe")
  pure { name, type := (← exprAt state (← natField json "type")) }

def parseGeneratedConstructorName (state : State) (json : Lean.Json) : Result Name := do
  let name ← localNameAt state (← natField json "name")
  requireSafeFlag "constructor" name (← field json "isUnsafe")
  pure name

def parseGeneratedRecursorName (state : State) (json : Lean.Json) : Result Name := do
  let name ← localNameAt state (← natField json "name")
  requireSafeFlag "recursor" name (← field json "isUnsafe")
  pure name

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
      | .ok candidateName => candidateName == ctorName
      | .error _ => false)
      | fail s!"inductive {name} is missing constructor record {ctorName}"
    parseKernelConstructor state ctorJson
  pure { name, type := (← exprAt state (← natField json "type")), ctors := ctorDecls }

def constructorTargetIndices
    (decl : KernelInductiveDecl)
    (specName : Name)
    (params fields : List Binder)
    (target : Expr) : Result (List Expr) := do
  let (head, args) := target.getAppFnArgs
  match head with
  | .const name levels =>
      if name != specName then
        fail s!"constructor target uses {name}, expected {specName}"
      else if !exprListAlphaEq (args.take params.length) (sourceOrderBvars params.length fields.length) then
        fail s!"constructor target for {specName} has unexpected parameter arguments"
      else if !levelListDefEq levels (expectedLevelArgs decl.levelParams) then
        fail s!"constructor target for {specName} has unexpected universe arguments"
      else
        pure (args.drop params.length)
  | _ => fail s!"constructor target for {specName} is not an inductive application"

def kernelTypeHeader
    (decl : KernelInductiveDecl)
    (typeDecl : KernelInductiveTypeDecl) :
    Result (List Binder × List Binder × Level) := do
  let (binders, result) := decomposeForalls typeDecl.type
  let some (params, indices) := splitAt? decl.numParams binders
    | fail s!"kernel inductive {typeDecl.name} has fewer parameters than declared"
  let .sort resultLevel := result
    | fail s!"kernel inductive {typeDecl.name} type must end in a sort"
  pure (params, indices, resultLevel)

def kernelConstructorToIndexed
    (decl : KernelInductiveDecl)
    (specName : Name)
    (params : List Binder)
    (ctor : KernelConstructorDecl) : Result IndexedConstructorSpec := do
  let (binders, target) := decomposeForalls ctor.type
  let some (ctorParams, fields) := splitAt? decl.numParams binders
    | fail s!"kernel constructor {ctor.name} has fewer parameters than declared"
  if !binderTypesAlphaEq ctorParams params then
    fail s!"kernel constructor {ctor.name} parameter telescope does not match {specName}"
  let targetIndices ← constructorTargetIndices decl specName params fields target
  pure { name := ctor.name, fields, targetIndices }

def kernelConstructorToSimple
    (decl : KernelInductiveDecl)
    (specName : Name)
    (params : List Binder)
    (ctor : KernelConstructorDecl) : Result SimpleConstructorSpec := do
  let indexed ← kernelConstructorToIndexed decl specName params ctor
  if indexed.targetIndices.isEmpty then
    pure { name := indexed.name, fields := indexed.fields }
  else
    fail s!"kernel constructor {ctor.name} targets indexed form of non-indexed {specName}"

def lowerKernelInductive (decl : KernelInductiveDecl) : Result Declaration := do
  match decl.types with
  | [] => fail "kernel inductive declaration must contain at least one type"
  | _ :: _ :: _ => fail "mutual inductive groups are outside the first MPC export adapter"
  | [typeDecl] => do
      let (params, indices, resultLevel) ← kernelTypeHeader decl typeDecl
      if indices.isEmpty then
        let constructors ←
          typeDecl.ctors.mapM fun ctor =>
            kernelConstructorToSimple decl typeDecl.name params ctor
        pure
          (.inductive
            {
              name := typeDecl.name
              levelParams := decl.levelParams
              params
              resultLevel
              constructors
            })
      else
        let constructors ←
          typeDecl.ctors.mapM fun ctor =>
            kernelConstructorToIndexed decl typeDecl.name params ctor
        pure
          (.indexedInductive
            {
              name := typeDecl.name
              levelParams := decl.levelParams
              params
              indices
              resultLevel
              constructors
            })

def parseInductiveGroup (state : State) (json : Lean.Json) :
    Result (State × List Declaration × Audit) := do
  let typesJson ← arrayField json "types"
  let ctorsJson ← arrayField json "ctors"
  let recsJson ← arrayField json "recs"
  let some firstType := typesJson[0]?
    | fail "inductive group has no type records"
  let kernelTypes ← typesJson.toList.mapM (parseKernelInductiveType state ctorsJson)
  let generatedCtors ← ctorsJson.toList.mapM (parseGeneratedConstructorName state)
  let generatedRecs ← recsJson.toList.mapM (parseGeneratedRecursorName state)
  let decl :=
    {
      levelParams := (← levelParamList state (← field firstType "levelParams"))
      numParams := (← natField firstType "numParams")
      types := kernelTypes
    }
  if kernelTypes.length == 1 && kernelTypes.head!.name == "Eq" then
    let (state, decls) := withEqualityPrimitives state
    pure (state, decls, { constructors := generatedCtors, recursors := generatedRecs })
  else
    pure
      (state,
        [← lowerKernelInductive decl],
        { constructors := generatedCtors, recursors := generatedRecs })

def parseDeclaration (state : State) (json : Lean.Json) :
    Result (State × List Declaration × Audit) := do
  match
    field? json "axiom",
    field? json "def",
    field? json "thm",
    field? json "opaque",
    field? json "quot",
    field? json "inductive" with
  | some value, none, none, none, none, none => do
      let (state, declarations) ← parseAxiom state value
      pure (state, declarations, {})
  | none, some value, none, none, none, none =>
      pure (state, [← parseDefinition state value], {})
  | none, none, some value, none, none, none =>
      pure (state, [← parseTheorem state value], {})
  | none, none, none, some value, none, none =>
      pure (state, [← parseOpaque state value], {})
  | none, none, none, none, some value, none => do
      let (state, declarations) ← parseQuotientPrimitive state value
      pure (state, declarations, {})
  | none, none, none, none, none, some value =>
      parseInductiveGroup state value
  | _, _, _, _, _, _ => fail "export declaration entry must have exactly one declaration constructor"

def mergeAudit (left right : Audit) : Audit :=
  {
    constructors := left.constructors ++ right.constructors
    recursors := left.recursors ++ right.recursors
  }

def parseEntry (lineNumber : Nat) (state : State) (json : Lean.Json) : Result State := do
  let parseError {α : Type} (err : Error) : Result α :=
    .error { message := s!"line {lineNumber}: {err.message}" }
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
    | .ok (state, declarations, audit) =>
        pure
          {
            state with
            declarationsRev :=
              declarations.foldl
                (fun entries declaration => declaration :: entries)
                state.declarationsRev
            audit := mergeAudit state.audit audit
          }
    | .error err => parseError err

def parseLine (lineNumber : Nat) (state : State) (line : String) : Result State := do
  let trimmed := line.trimAscii.toString
  if trimmed.isEmpty then
    pure state
  else
    match Lean.Json.parse trimmed with
    | .ok json => parseEntry lineNumber state json
    | .error err => fail s!"line {lineNumber}: invalid JSON: {err}"

partial def parseLinesLoop (lineNumber : Nat) (state : State) : List String → Result State
  | [] => pure state
  | line :: rest => do
      let state ← parseLine lineNumber state line
      parseLinesLoop (lineNumber + 1) state rest

def parseString (input : String) : Result ParseState := do
  let state ← parseLinesLoop 1 {} (input.splitOn "\n")
  pure { declarations := state.declarationsRev.reverse, audit := state.audit }

def declarationNameLabel : Declaration → String
  | .axiom name .. => name
  | .definition name .. => name
  | .opaque name .. => name
  | .theorem name .. => name
  | .inductive spec => spec.name
  | .indexedInductive spec => spec.name
  | .equalityPrimitives => "equality primitives"
  | .quotientPrimitives => "quotient primitives"

def declarationKindLabel : Declaration → String
  | .axiom .. => "axiom"
  | .definition .. => "definition"
  | .opaque .. => "opaque"
  | .theorem .. => "theorem"
  | .inductive .. => "inductive"
  | .indexedInductive .. => "indexed-inductive"
  | .equalityPrimitives => "equality-primitives"
  | .quotientPrimitives => "quotient-primitives"

partial def replayDeclarations (manifest : Manifest) : Env → List Declaration → Result Env
  | env, [] => pure env
  | env, declaration :: rest => do
      match addDecl manifest env declaration with
      | .ok env => replayDeclarations manifest env rest
      | .error err =>
          fail s!"while replaying {declarationKindLabel declaration} {declarationNameLabel declaration}: {err.message}"

def auditGenerated (env : Env) (audit : Audit) : Result Unit := do
  for name in audit.constructors do
    match env.find? name with
    | some { kind := .constructor .., .. } => pure ()
    | some { kind := .equalityRefl, .. } => pure ()
    | some _ => fail s!"generated constructor audit found non-constructor: {name}"
    | none => fail s!"generated constructor audit found unknown name: {name}"
  for name in audit.recursors do
    match env.find? name with
    | some { kind := .recursor .., .. } => pure ()
    | some { kind := .indexedRecursor .., .. } => pure ()
    | some { kind := .equalityRec, .. } => pure ()
    | some { kind := .equalityNdRec, .. } => pure ()
    | some _ => fail s!"generated recursor audit found non-recursor: {name}"
    | none => fail s!"generated recursor audit found unknown name: {name}"

def replayParsed (manifest : Manifest) (state : ParseState) : Result Env := do
  let env ← replayDeclarations manifest emptyEnv state.declarations
  auditGenerated env state.audit
  pure env

def checkString (input : String) : Result Env := do
  let state ← parseString input
  replayParsed MPC.Configs.LeanCore429 state

end MPC.Adapters.Export
