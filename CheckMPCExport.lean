import MPC.Adapters.Layer

namespace MPC.CheckExport

inductive TelemetryFormat where
  | off
  | text
  | jsonl
  | profileJsonl
  deriving BEq, Inhabited

structure ReplayOptions where
  trace : Bool := false
  telemetry : TelemetryFormat := .off
  deriving Inhabited

structure Config where
  inputPath : System.FilePath
  checkedLayerPath? : Option System.FilePath := none
  saveLayerPath? : Option System.FilePath := none
  loadLayerPath? : Option System.FilePath := none
  cacheLayerPath? : Option System.FilePath := none
  limit? : Option Nat := none
  profileDeclaration? : Option Nat := none
  replayOptions : ReplayOptions := {}
  diagnosticAssumeGenerated : Bool := false

def usage : String :=
  "usage: mpc-check-export [<export.ndjson>]\n" ++
  "       mpc-check-export --input <export.ndjson>\n" ++
  "       mpc-check-export --checked-layer <base.ndjson> <export.ndjson>\n" ++
  "       mpc-check-export --save-layer <layer.json|layer.sqlite> <export.ndjson>\n" ++
  "       mpc-check-export --load-layer <layer.json|layer.sqlite> <export.ndjson>\n" ++
  "       mpc-check-export --cache-layer <layer.db> <export.ndjson>\n" ++
  "       mpc-check-export [--limit <n>] [--trace] [--stats|--stats-jsonl|--profile-jsonl] [--diagnostic-assume-generated] <export.ndjson>\n" ++
  "       mpc-check-export --profile-declaration <n> <export.ndjson>\n" ++
  "       mpc-check-export [--assume-generated] <export.ndjson>  (alias for diagnostic mode)\n" ++
  "       IN=<export.ndjson> mpc-check-export"

def filePath (path : String) : Except String System.FilePath :=
  if path.isEmpty then
    .error "empty input path"
  else
    pure (System.FilePath.mk path)

def configFromPath
    (checkedLayerPath? : Option System.FilePath)
    (saveLayerPath? : Option System.FilePath)
    (loadLayerPath? : Option System.FilePath)
    (cacheLayerPath? : Option System.FilePath)
    (limit? : Option Nat)
    (profileDeclaration? : Option Nat)
    (replayOptions : ReplayOptions)
    (diagnosticAssumeGenerated : Bool)
    (path : String) :
    Except String Config := do
  pure { inputPath := (← filePath path), checkedLayerPath?, saveLayerPath?, loadLayerPath?, cacheLayerPath?, limit?, profileDeclaration?, replayOptions, diagnosticAssumeGenerated }

def configFromEnv
    (checkedLayerPath? : Option System.FilePath)
    (saveLayerPath? : Option System.FilePath)
    (loadLayerPath? : Option System.FilePath)
    (cacheLayerPath? : Option System.FilePath)
    (limit? : Option Nat)
    (profileDeclaration? : Option Nat)
    (replayOptions : ReplayOptions)
    (diagnosticAssumeGenerated : Bool) : IO (Except String Config) := do
  match ← IO.getEnv "IN" with
  | some path => pure (configFromPath checkedLayerPath? saveLayerPath? loadLayerPath? cacheLayerPath? limit? profileDeclaration? replayOptions diagnosticAssumeGenerated path)
  | none => pure (.error "missing input path")

def setInputPath (input? : Option String) (path : String) : Except String (Option String) := do
  if input?.isSome then
    .error "multiple input paths"
  else if path.isEmpty then
    .error "empty input path"
  else
    pure (some path)

def parseNatArgument (label value : String) : Except String Nat :=
  match value.toNat? with
  | some n => pure n
  | none => .error s!"invalid {label}: {value}"

def setTelemetryFormat
    (options : ReplayOptions)
    (format : TelemetryFormat) :
    Except String ReplayOptions :=
  if options.telemetry != .off then
    .error "multiple telemetry formats"
  else
    pure { options with telemetry := format }

partial def parseArgsLoop
    (input? : Option String)
    (checkedLayerPath? : Option System.FilePath)
    (saveLayerPath? : Option System.FilePath)
    (loadLayerPath? : Option System.FilePath)
    (cacheLayerPath? : Option System.FilePath)
    (limit? : Option Nat)
    (profileDeclaration? : Option Nat)
    (replayOptions : ReplayOptions)
    (diagnosticAssumeGenerated : Bool) :
    List String → Except String (Option String × Option System.FilePath × Option System.FilePath × Option System.FilePath × Option System.FilePath × Option Nat × Option Nat × ReplayOptions × Bool)
  | [] => pure (input?, checkedLayerPath?, saveLayerPath?, loadLayerPath?, cacheLayerPath?, limit?, profileDeclaration?, replayOptions, diagnosticAssumeGenerated)
  | "--input" :: path :: rest => do
      parseArgsLoop (← setInputPath input? path) checkedLayerPath? saveLayerPath? loadLayerPath? cacheLayerPath? limit? profileDeclaration? replayOptions diagnosticAssumeGenerated rest
  | "--input" :: [] => .error "missing value after --input"
  | "--checked-layer" :: path :: rest => do
      if checkedLayerPath?.isSome then
        .error "multiple checked layers"
      else
        parseArgsLoop input? (some (← filePath path)) saveLayerPath? loadLayerPath? cacheLayerPath? limit? profileDeclaration? replayOptions diagnosticAssumeGenerated rest
  | "--checked-layer" :: [] => .error "missing value after --checked-layer"
  | "--save-layer" :: path :: rest => do
      if saveLayerPath?.isSome then
        .error "multiple save layer paths"
      else
        parseArgsLoop input? checkedLayerPath? (some (← filePath path)) loadLayerPath? cacheLayerPath? limit? profileDeclaration? replayOptions diagnosticAssumeGenerated rest
  | "--save-layer" :: [] => .error "missing value after --save-layer"
  | "--load-layer" :: path :: rest => do
      if loadLayerPath?.isSome then
        .error "multiple load layer paths"
      else
        parseArgsLoop input? checkedLayerPath? saveLayerPath? (some (← filePath path)) cacheLayerPath? limit? profileDeclaration? replayOptions diagnosticAssumeGenerated rest
  | "--load-layer" :: [] => .error "missing value after --load-layer"
  | "--cache-layer" :: path :: rest => do
      if cacheLayerPath?.isSome then
        .error "multiple cache layer paths"
      else
        parseArgsLoop input? checkedLayerPath? saveLayerPath? loadLayerPath? (some (← filePath path)) limit? profileDeclaration? replayOptions diagnosticAssumeGenerated rest
  | "--cache-layer" :: [] => .error "missing value after --cache-layer"
  | "--limit" :: value :: rest => do
      if limit?.isSome then
        .error "multiple limits"
      else
        parseArgsLoop input? checkedLayerPath? saveLayerPath? loadLayerPath? cacheLayerPath? (some (← parseNatArgument "limit" value)) profileDeclaration? replayOptions diagnosticAssumeGenerated rest
  | "--limit" :: [] => .error "missing value after --limit"
  | "--profile-declaration" :: value :: rest => do
      if profileDeclaration?.isSome then
        .error "multiple profile declaration indexes"
      else
        parseArgsLoop input? checkedLayerPath? saveLayerPath? loadLayerPath? cacheLayerPath? limit? (some (← parseNatArgument "profile declaration index" value)) replayOptions diagnosticAssumeGenerated rest
  | "--profile-declaration" :: [] => .error "missing value after --profile-declaration"
  | "--trace" :: rest =>
      parseArgsLoop input? checkedLayerPath? saveLayerPath? loadLayerPath? cacheLayerPath? limit? profileDeclaration? { replayOptions with trace := true } diagnosticAssumeGenerated rest
  | "--stats" :: rest => do
      parseArgsLoop input? checkedLayerPath? saveLayerPath? loadLayerPath? cacheLayerPath? limit? profileDeclaration? (← setTelemetryFormat replayOptions .text) diagnosticAssumeGenerated rest
  | "--stats-jsonl" :: rest => do
      parseArgsLoop input? checkedLayerPath? saveLayerPath? loadLayerPath? cacheLayerPath? limit? profileDeclaration? (← setTelemetryFormat replayOptions .jsonl) diagnosticAssumeGenerated rest
  | "--profile-jsonl" :: rest => do
      parseArgsLoop input? checkedLayerPath? saveLayerPath? loadLayerPath? cacheLayerPath? limit? profileDeclaration? (← setTelemetryFormat replayOptions .profileJsonl) diagnosticAssumeGenerated rest
  | "--diagnostic-assume-generated" :: rest =>
      parseArgsLoop input? checkedLayerPath? saveLayerPath? loadLayerPath? cacheLayerPath? limit? profileDeclaration? replayOptions true rest
  | "--assume-generated" :: rest =>
      parseArgsLoop input? checkedLayerPath? saveLayerPath? loadLayerPath? cacheLayerPath? limit? profileDeclaration? replayOptions true rest
  | "--help" :: _ => .error usage
  | arg :: rest =>
      if arg.startsWith "-" then
        .error s!"unknown argument: {arg}"
      else do
        parseArgsLoop (← setInputPath input? arg) checkedLayerPath? saveLayerPath? loadLayerPath? cacheLayerPath? limit? profileDeclaration? replayOptions diagnosticAssumeGenerated rest

def parseArgs : List String → IO (Except String Config)
  | args => do
      match parseArgsLoop none none none none none none none {} false args with
      | .error err => pure (.error err)
      | .ok (some path, checkedLayerPath?, saveLayerPath?, loadLayerPath?, cacheLayerPath?, limit?, profileDeclaration?, replayOptions, diagnosticAssumeGenerated) =>
          pure (configFromPath checkedLayerPath? saveLayerPath? loadLayerPath? cacheLayerPath? limit? profileDeclaration? replayOptions diagnosticAssumeGenerated path)
      | .ok (none, checkedLayerPath?, saveLayerPath?, loadLayerPath?, cacheLayerPath?, limit?, profileDeclaration?, replayOptions, diagnosticAssumeGenerated) =>
          configFromEnv checkedLayerPath? saveLayerPath? loadLayerPath? cacheLayerPath? limit? profileDeclaration? replayOptions diagnosticAssumeGenerated

def printOutcome (status : String) (path : System.FilePath) (message : String) : IO Unit := do
  IO.println status
  IO.println s!"artifact: {path}"
  if message != "" then
    IO.println s!"message: {message}"

inductive ReplayStatus where
  | checked
  | reused
  | rejected

def ReplayStatus.label : ReplayStatus → String
  | .checked => "checked"
  | .reused => "reused"
  | .rejected => "rejected"

def jsonNat (value : Nat) : Lean.Json :=
  Lean.Json.num (Lean.JsonNumber.fromNat value)

structure ExprProfile where
  nodes : Nat := 0
  appNodes : Nat := 0
  headApps : Nat := 0
  maxAppArgs : Nat := 0
  definitionHeadApps : Nat := 0
  simpleRecursorHeadApps : Nat := 0
  mutualRecursorHeadApps : Nat := 0
  indexedRecursorHeadApps : Nat := 0
  nestedRecursorHeadApps : Nat := 0
  equalityRecHeadApps : Nat := 0
  equalityNdRecHeadApps : Nat := 0
  quotientLiftHeadApps : Nat := 0
  primitiveNatHeadApps : Nat := 0
  lamNodes : Nat := 0
  forallNodes : Nat := 0
  letNodes : Nat := 0
  projectionNodes : Nat := 0
  constNodes : Nat := 0
  definitionConsts : Nat := 0
  theoremConsts : Nat := 0
  opaqueConsts : Nat := 0
  axiomConsts : Nat := 0
  simpleRecursorConsts : Nat := 0
  mutualRecursorConsts : Nat := 0
  indexedRecursorConsts : Nat := 0
  nestedRecursorConsts : Nat := 0
  equalityRecConsts : Nat := 0
  equalityNdRecConsts : Nat := 0
  quotientLiftConsts : Nat := 0
  primitiveNatConsts : Nat := 0
  deriving Inhabited

def ExprProfile.add (left right : ExprProfile) : ExprProfile :=
  {
    nodes := left.nodes + right.nodes
    appNodes := left.appNodes + right.appNodes
    headApps := left.headApps + right.headApps
    maxAppArgs := Nat.max left.maxAppArgs right.maxAppArgs
    definitionHeadApps := left.definitionHeadApps + right.definitionHeadApps
    simpleRecursorHeadApps := left.simpleRecursorHeadApps + right.simpleRecursorHeadApps
    mutualRecursorHeadApps := left.mutualRecursorHeadApps + right.mutualRecursorHeadApps
    indexedRecursorHeadApps := left.indexedRecursorHeadApps + right.indexedRecursorHeadApps
    nestedRecursorHeadApps := left.nestedRecursorHeadApps + right.nestedRecursorHeadApps
    equalityRecHeadApps := left.equalityRecHeadApps + right.equalityRecHeadApps
    equalityNdRecHeadApps := left.equalityNdRecHeadApps + right.equalityNdRecHeadApps
    quotientLiftHeadApps := left.quotientLiftHeadApps + right.quotientLiftHeadApps
    primitiveNatHeadApps := left.primitiveNatHeadApps + right.primitiveNatHeadApps
    lamNodes := left.lamNodes + right.lamNodes
    forallNodes := left.forallNodes + right.forallNodes
    letNodes := left.letNodes + right.letNodes
    projectionNodes := left.projectionNodes + right.projectionNodes
    constNodes := left.constNodes + right.constNodes
    definitionConsts := left.definitionConsts + right.definitionConsts
    theoremConsts := left.theoremConsts + right.theoremConsts
    opaqueConsts := left.opaqueConsts + right.opaqueConsts
    axiomConsts := left.axiomConsts + right.axiomConsts
    simpleRecursorConsts := left.simpleRecursorConsts + right.simpleRecursorConsts
    mutualRecursorConsts := left.mutualRecursorConsts + right.mutualRecursorConsts
    indexedRecursorConsts := left.indexedRecursorConsts + right.indexedRecursorConsts
    nestedRecursorConsts := left.nestedRecursorConsts + right.nestedRecursorConsts
    equalityRecConsts := left.equalityRecConsts + right.equalityRecConsts
    equalityNdRecConsts := left.equalityNdRecConsts + right.equalityNdRecConsts
    quotientLiftConsts := left.quotientLiftConsts + right.quotientLiftConsts
    primitiveNatConsts := left.primitiveNatConsts + right.primitiveNatConsts
  }

def primitiveNatName (name : Name) : Bool :=
  name == "Nat.add" ||
    name == "Nat.mul" ||
    name == "Nat.pow" ||
    name == "Nat.sub" ||
    name == "Nat.beq" ||
    name == "Nat.ble"

def profileConst (env : Env) (name : Name) : ExprProfile :=
  let base : ExprProfile :=
    {
      nodes := 1
      constNodes := 1
      primitiveNatConsts := if primitiveNatName name then 1 else 0
    }
  match env.find? name with
  | some info =>
      match info.kind with
      | .definition => { base with definitionConsts := base.definitionConsts + 1 }
      | .theorem => { base with theoremConsts := base.theoremConsts + 1 }
      | .opaque => { base with opaqueConsts := base.opaqueConsts + 1 }
      | .axiom => { base with axiomConsts := base.axiomConsts + 1 }
      | .recursor .. => { base with simpleRecursorConsts := base.simpleRecursorConsts + 1 }
      | .mutualRecursor .. => { base with mutualRecursorConsts := base.mutualRecursorConsts + 1 }
      | .indexedRecursor .. => { base with indexedRecursorConsts := base.indexedRecursorConsts + 1 }
      | .nestedRecursor .. => { base with nestedRecursorConsts := base.nestedRecursorConsts + 1 }
      | .equalityRec => { base with equalityRecConsts := base.equalityRecConsts + 1 }
      | .equalityNdRec => { base with equalityNdRecConsts := base.equalityNdRecConsts + 1 }
      | .quotientLift => { base with quotientLiftConsts := base.quotientLiftConsts + 1 }
      | _ => base
  | none => base

def profileHeadApp (env : Env) (expr : Expr) : ExprProfile :=
  let (head, args) := expr.getAppFnArgs
  let base : ExprProfile :=
    {
      headApps := 1
      maxAppArgs := args.length
    }
  match head with
  | .const name _ =>
      let base :=
        { base with primitiveNatHeadApps := if primitiveNatName name then 1 else 0 }
      match env.find? name with
      | some info =>
          match info.kind with
          | .definition => { base with definitionHeadApps := base.definitionHeadApps + 1 }
          | .recursor .. => { base with simpleRecursorHeadApps := base.simpleRecursorHeadApps + 1 }
          | .mutualRecursor .. => { base with mutualRecursorHeadApps := base.mutualRecursorHeadApps + 1 }
          | .indexedRecursor .. => { base with indexedRecursorHeadApps := base.indexedRecursorHeadApps + 1 }
          | .nestedRecursor .. => { base with nestedRecursorHeadApps := base.nestedRecursorHeadApps + 1 }
          | .equalityRec => { base with equalityRecHeadApps := base.equalityRecHeadApps + 1 }
          | .equalityNdRec => { base with equalityNdRecHeadApps := base.equalityNdRecHeadApps + 1 }
          | .quotientLift => { base with quotientLiftHeadApps := base.quotientLiftHeadApps + 1 }
          | _ => base
      | none => base
  | _ => base

partial def profileExpr (env : Env) (parentIsApp : Bool) : Expr → ExprProfile
  | .bvar _ => { nodes := 1 }
  | .sort _ => { nodes := 1 }
  | .const name _ => profileConst env name
  | .lit _ => { nodes := 1 }
  | expr@(.app fn arg) =>
      let headProfile :=
        if parentIsApp then
          {}
        else
          profileHeadApp env expr
      ({ nodes := 1, appNodes := 1 } : ExprProfile)
        |>.add headProfile
        |>.add (profileExpr env true fn)
        |>.add (profileExpr env false arg)
  | .lam _ type body =>
      ({ nodes := 1, lamNodes := 1 } : ExprProfile)
        |>.add (profileExpr env false type)
        |>.add (profileExpr env false body)
  | .forallE _ type body =>
      ({ nodes := 1, forallNodes := 1 } : ExprProfile)
        |>.add (profileExpr env false type)
        |>.add (profileExpr env false body)
  | .letE _ type value body =>
      ({ nodes := 1, letNodes := 1 } : ExprProfile)
        |>.add (profileExpr env false type)
        |>.add (profileExpr env false value)
        |>.add (profileExpr env false body)
  | .proj _ _ target =>
      ({ nodes := 1, projectionNodes := 1 } : ExprProfile)
        |>.add (profileExpr env false target)

def profileExprRoot (env : Env) (expr : Expr) : ExprProfile :=
  profileExpr env false expr

def profileBinder (env : Env) (binder : Binder) : ExprProfile :=
  profileExprRoot env binder.type

def profileBinders (env : Env) (binders : List Binder) : ExprProfile :=
  binders.foldl (fun profile binder => profile.add (profileBinder env binder)) {}

def profileSimpleConstructor (env : Env) (ctor : SimpleConstructorSpec) : ExprProfile :=
  profileBinders env ctor.fields

def profileIndexedConstructor (env : Env) (ctor : IndexedConstructorSpec) : ExprProfile :=
  (profileBinders env ctor.fields).add
    (ctor.targetIndices.foldl (fun profile index => profile.add (profileExprRoot env index)) {})

structure DeclarationProfile where
  typeNodes : Nat := 0
  valueNodes : Nat := 0
  exprs : ExprProfile := {}
  deriving Inhabited

def profileDeclaration (env : Env) : Declaration → DeclarationProfile
  | .axiom _ _ type =>
      let typeProfile := profileExprRoot env type
      { typeNodes := typeProfile.nodes, exprs := typeProfile }
  | .definition _ _ type value
  | .opaque _ _ type value
  | .theorem _ _ type value =>
      let typeProfile := profileExprRoot env type
      let valueProfile := profileExprRoot env value
      {
        typeNodes := typeProfile.nodes
        valueNodes := valueProfile.nodes
        exprs := typeProfile.add valueProfile
      }
  | .inductive spec =>
      let profile :=
        (profileBinders env spec.params).add
          (spec.constructors.foldl
            (fun profile ctor => profile.add (profileSimpleConstructor env ctor))
            {})
      { typeNodes := profile.nodes, exprs := profile }
  | .inductiveBlock block =>
      let profile :=
        block.specs.foldl
          (fun profile spec =>
            profile.add
              ((profileBinders env spec.params).add
                (spec.constructors.foldl
                  (fun ctorProfile ctor => ctorProfile.add (profileSimpleConstructor env ctor))
                  {})))
          {}
      { typeNodes := profile.nodes, exprs := profile }
  | .indexedInductive spec =>
      let profile :=
        (profileBinders env spec.params).add
          ((profileBinders env spec.indices).add
            (spec.constructors.foldl
              (fun profile ctor => profile.add (profileIndexedConstructor env ctor))
              {}))
      { typeNodes := profile.nodes, exprs := profile }
  | .equalityPrimitives
  | .quotientPrimitives => {}

def DeclarationProfile.toJsonFields (profile : DeclarationProfile) : List (String × Lean.Json) :=
  let exprs := profile.exprs
  [
    ("profile_type_nodes", jsonNat profile.typeNodes),
    ("profile_value_nodes", jsonNat profile.valueNodes),
    ("profile_nodes", jsonNat exprs.nodes),
    ("profile_app_nodes", jsonNat exprs.appNodes),
    ("profile_head_apps", jsonNat exprs.headApps),
    ("profile_max_app_args", jsonNat exprs.maxAppArgs),
    ("profile_definition_head_apps", jsonNat exprs.definitionHeadApps),
    ("profile_simple_recursor_head_apps", jsonNat exprs.simpleRecursorHeadApps),
    ("profile_mutual_recursor_head_apps", jsonNat exprs.mutualRecursorHeadApps),
    ("profile_indexed_recursor_head_apps", jsonNat exprs.indexedRecursorHeadApps),
    ("profile_nested_recursor_head_apps", jsonNat exprs.nestedRecursorHeadApps),
    ("profile_eq_rec_head_apps", jsonNat exprs.equalityRecHeadApps),
    ("profile_eq_ndrec_head_apps", jsonNat exprs.equalityNdRecHeadApps),
    ("profile_quot_lift_head_apps", jsonNat exprs.quotientLiftHeadApps),
    ("profile_primitive_nat_head_apps", jsonNat exprs.primitiveNatHeadApps),
    ("profile_lam_nodes", jsonNat exprs.lamNodes),
    ("profile_forall_nodes", jsonNat exprs.forallNodes),
    ("profile_let_nodes", jsonNat exprs.letNodes),
    ("profile_projection_nodes", jsonNat exprs.projectionNodes),
    ("profile_const_nodes", jsonNat exprs.constNodes),
    ("profile_definition_consts", jsonNat exprs.definitionConsts),
    ("profile_theorem_consts", jsonNat exprs.theoremConsts),
    ("profile_opaque_consts", jsonNat exprs.opaqueConsts),
    ("profile_axiom_consts", jsonNat exprs.axiomConsts),
    ("profile_simple_recursor_consts", jsonNat exprs.simpleRecursorConsts),
    ("profile_mutual_recursor_consts", jsonNat exprs.mutualRecursorConsts),
    ("profile_indexed_recursor_consts", jsonNat exprs.indexedRecursorConsts),
    ("profile_nested_recursor_consts", jsonNat exprs.nestedRecursorConsts),
    ("profile_eq_rec_consts", jsonNat exprs.equalityRecConsts),
    ("profile_eq_ndrec_consts", jsonNat exprs.equalityNdRecConsts),
    ("profile_quot_lift_consts", jsonNat exprs.quotientLiftConsts),
    ("profile_primitive_nat_consts", jsonNat exprs.primitiveNatConsts)
  ]

structure DeclarationTelemetry where
  index : Nat
  kind : String
  name : String
  elapsedMs : Nat
  cumulativeMs : Nat
  status : ReplayStatus
  profile? : Option DeclarationProfile := none

def DeclarationTelemetry.toJson (entry : DeclarationTelemetry) : Lean.Json :=
  let fields := [
    ("event", Lean.Json.str "declaration"),
    ("index", jsonNat entry.index),
    ("kind", Lean.Json.str entry.kind),
    ("name", Lean.Json.str entry.name),
    ("status", Lean.Json.str entry.status.label),
    ("elapsed_ms", jsonNat entry.elapsedMs),
    ("cumulative_ms", jsonNat entry.cumulativeMs)
  ]
  let fields :=
    match entry.profile? with
    | some profile => fields ++ profile.toJsonFields
    | none => fields
  Lean.Json.mkObj fields

def DeclarationTelemetry.text (entry : DeclarationTelemetry) : String :=
  s!"stats: index={entry.index} status={entry.status.label} elapsed_ms={entry.elapsedMs} cumulative_ms={entry.cumulativeMs} kind={entry.kind} name={entry.name}"

def emitDeclarationTelemetry
    (format : TelemetryFormat)
    (entry : DeclarationTelemetry) :
    IO Unit := do
  match format with
  | .off => pure ()
  | .text => IO.println entry.text
  | .jsonl
  | .profileJsonl => IO.println entry.toJson.compress
  if format != .off then
    (← IO.getStdout).flush

partial def replayLoop
    (manifest : Manifest)
    (options : ReplayOptions) :
    Nat → Nat → Env → List Declaration → IO (Result Env)
  | _, _, env, [] => pure (.ok env)
  | index, cumulativeMs, env, declaration :: rest => do
      if options.telemetry == .off then
        if options.trace then
          let kind := MPC.Adapters.Export.declarationKindLabel declaration
          let name := MPC.Adapters.Export.declarationNameLabel declaration
          IO.println s!"replay: {index} {kind} {name}"
          (← IO.getStdout).flush
        match addDecl manifest env declaration with
        | .ok env => replayLoop manifest options (index + 1) cumulativeMs env rest
        | .error err =>
            let kind := MPC.Adapters.Export.declarationKindLabel declaration
            let name := MPC.Adapters.Export.declarationNameLabel declaration
            pure (.error { message := s!"while replaying {kind} {name}: {err.message}" })
      else
        let kind := MPC.Adapters.Export.declarationKindLabel declaration
        let name := MPC.Adapters.Export.declarationNameLabel declaration
        let profile? :=
          if options.telemetry == .profileJsonl then
            some (profileDeclaration env declaration)
          else
            none
        if options.trace then
          IO.println s!"replay: {index} {kind} {name}"
          (← IO.getStdout).flush
        let startMs ← IO.monoMsNow
        match addDecl manifest env declaration with
        | .ok env =>
            let stopMs ← IO.monoMsNow
            let elapsedMs := stopMs - startMs
            let cumulativeMs := cumulativeMs + elapsedMs
            emitDeclarationTelemetry options.telemetry {
              index,
              kind,
              name,
              elapsedMs,
              cumulativeMs,
              status := .checked,
              profile? := profile?
            }
            replayLoop manifest options (index + 1) cumulativeMs env rest
        | .error err =>
            let stopMs ← IO.monoMsNow
            let elapsedMs := stopMs - startMs
            let cumulativeMs := cumulativeMs + elapsedMs
            emitDeclarationTelemetry options.telemetry {
              index,
              kind,
              name,
              elapsedMs,
              cumulativeMs,
              status := .rejected,
              profile? := profile?
            }
            pure (.error { message := s!"while replaying {kind} {name}: {err.message}" })

def generatedSupportAssumptionName (name : Name) : Bool :=
  name.endsWith ".noConfusion" ||
    name.startsWith "noConfusion_of_"

def generatedSupportAssumption : Declaration → Bool
  | .definition name .. => generatedSupportAssumptionName name
  | .theorem name .. => generatedSupportAssumptionName name
  | .opaque name .. => generatedSupportAssumptionName name
  | _ => false

def assumeGeneratedSupport : Declaration → Declaration
  | .definition name levelParams type value =>
      if generatedSupportAssumptionName name then
        .axiom name levelParams type
      else
        .definition name levelParams type value
  | .theorem name levelParams type value =>
      if generatedSupportAssumptionName name then
        .axiom name levelParams type
      else
        .theorem name levelParams type value
  | .opaque name levelParams type value =>
      if generatedSupportAssumptionName name then
        .axiom name levelParams type
      else
        .opaque name levelParams type value
  | declaration => declaration

def prepareDeclarations (config : Config) (state : MPC.Adapters.Export.ParseState) :
    List Declaration :=
  let declarations :=
    match config.limit? with
    | some limit => state.declarations.take limit
    | none => state.declarations
  if config.diagnosticAssumeGenerated then
    declarations.map fun declaration =>
      if generatedSupportAssumption declaration then
        assumeGeneratedSupport declaration
      else
        declaration
  else
    declarations

def generatedAssumptionCount (config : Config) (state : MPC.Adapters.Export.ParseState) : Nat :=
  if config.diagnosticAssumeGenerated then
    (prepareDeclarations { config with diagnosticAssumeGenerated := false } state).filter generatedSupportAssumption |>.length
  else
    0

def replayConfig (config : Config) (state : MPC.Adapters.Export.ParseState) :
    IO (Result Env) := do
  let declarations := prepareDeclarations config state
  match ← replayLoop MPC.Configs.LeanCore429 config.replayOptions 0 0 emptyEnv declarations with
  | .error err => pure (.error err)
  | .ok env =>
      match config.limit? with
      | some _ => pure (.ok env)
      | none =>
          match MPC.Adapters.Export.auditGenerated env state.audit with
          | .ok () => pure (.ok env)
          | .error err => pure (.error err)

structure LayerReplayResult where
  env : Env
  reused : Nat
  checked : Nat

def buildCheckedLayerFromFile (path : System.FilePath) :
    IO (Result MPC.Adapters.Layer.CheckedLayer) := do
  let input ← IO.FS.readFile path
  match MPC.Adapters.Export.parseString input with
  | .error err => pure (.error err)
  | .ok state => pure (MPC.Adapters.Layer.build MPC.Configs.LeanCore429 state)

def replayWithLayer (config : Config) (state : MPC.Adapters.Export.ParseState)
    (layer : MPC.Adapters.Layer.CheckedLayer) : Result LayerReplayResult := do
  let declarations := prepareDeclarations config state
  let audit :=
    match config.limit? with
    | some _ => {}
    | none => state.audit
  match MPC.Adapters.Layer.replay MPC.Configs.LeanCore429 layer audit declarations with
  | .error err => .error err
  | .ok summary =>
      pure { env := summary.env, reused := summary.reused, checked := summary.checked }

def replayWithCheckedLayer (config : Config) (state : MPC.Adapters.Export.ParseState)
    (layerPath : System.FilePath) : IO (Result LayerReplayResult) := do
  if config.profileDeclaration?.isSome then
    pure (.error { message := "--checked-layer cannot be combined with --profile-declaration" })
  else if config.saveLayerPath?.isSome || config.loadLayerPath?.isSome || config.cacheLayerPath?.isSome then
    pure (.error { message := "--checked-layer cannot be combined with --save-layer, --load-layer, or --cache-layer" })
  else if config.replayOptions.telemetry != .off then
    pure (.error { message := "--checked-layer cannot be combined with telemetry output" })
  else if config.replayOptions.trace then
    pure (.error { message := "--checked-layer cannot be combined with --trace" })
  else if config.diagnosticAssumeGenerated then
    pure (.error { message := "--checked-layer cannot be combined with diagnostic generated assumptions" })
  else
    match ← buildCheckedLayerFromFile layerPath with
    | .error err => pure (.error { message := s!"while checking layer {layerPath}: {err.message}" })
    | .ok layer =>
        pure (replayWithLayer config state layer)

def replayWithSavedLayer (config : Config) (state : MPC.Adapters.Export.ParseState)
    (layerPath : System.FilePath) : IO (Result LayerReplayResult) := do
  if config.profileDeclaration?.isSome then
    pure (.error { message := "--load-layer cannot be combined with --profile-declaration" })
  else if config.checkedLayerPath?.isSome || config.saveLayerPath?.isSome || config.cacheLayerPath?.isSome then
    pure (.error { message := "--load-layer cannot be combined with --checked-layer, --save-layer, or --cache-layer" })
  else if config.replayOptions.telemetry == .profileJsonl then
    pure (.error { message := "--load-layer cannot be combined with --profile-jsonl" })
  else if config.replayOptions.telemetry != .off && !MPC.Adapters.Layer.sqlitePath layerPath then
    pure (.error { message := "--load-layer telemetry requires a SQLite layer" })
  else if config.replayOptions.trace then
    pure (.error { message := "--load-layer cannot be combined with --trace" })
  else if config.diagnosticAssumeGenerated then
    pure (.error { message := "--load-layer cannot be combined with diagnostic generated assumptions" })
  else
    let declarations := prepareDeclarations config state
    let audit :=
      match config.limit? with
      | some _ => {}
      | none => state.audit
    if MPC.Adapters.Layer.sqlitePath layerPath then
      let observer? : Option MPC.Adapters.Layer.ReplayObserver :=
        match config.replayOptions.telemetry with
        | .off => none
        | .text | .jsonl =>
            some fun step => do
              let status :=
                match step.status with
                | .reused => ReplayStatus.reused
                | .checked => ReplayStatus.checked
                | .rejected => ReplayStatus.rejected
              emitDeclarationTelemetry config.replayOptions.telemetry {
                index := step.index,
                kind := MPC.Adapters.Export.declarationKindLabel step.declaration,
                name := MPC.Adapters.Export.declarationNameLabel step.declaration,
                elapsedMs := step.elapsedMs,
                cumulativeMs := step.cumulativeMs,
                status,
                profile? := none
              }
        | .profileJsonl => none
      match ← MPC.Adapters.Layer.replaySqliteWithObserver MPC.Configs.LeanCore429 layerPath audit declarations observer? with
      | .error err => pure (.error { message := s!"while loading layer {layerPath}: {err.message}" })
      | .ok summary =>
          pure (.ok { env := summary.env, reused := summary.reused, checked := summary.checked })
    else
      match ← MPC.Adapters.Layer.load layerPath with
      | .error err => pure (.error { message := s!"while loading layer {layerPath}: {err.message}" })
      | .ok layer => pure (replayWithLayer config state layer)

def replayWithCacheLayer (config : Config) (state : MPC.Adapters.Export.ParseState)
    (layerPath : System.FilePath) : IO (Result LayerReplayResult) := do
  if config.profileDeclaration?.isSome then
    pure (.error { message := "--cache-layer cannot be combined with --profile-declaration" })
  else if config.checkedLayerPath?.isSome || config.saveLayerPath?.isSome || config.loadLayerPath?.isSome then
    pure (.error { message := "--cache-layer cannot be combined with --checked-layer, --save-layer, or --load-layer" })
  else if config.limit?.isSome then
    pure (.error { message := "--cache-layer cannot be combined with --limit" })
  else if !MPC.Adapters.Layer.sqlitePath layerPath then
    pure (.error { message := "--cache-layer requires a SQLite layer path" })
  else if config.replayOptions.telemetry == .profileJsonl then
    pure (.error { message := "--cache-layer cannot be combined with --profile-jsonl" })
  else if config.replayOptions.trace then
    pure (.error { message := "--cache-layer cannot be combined with --trace" })
  else if config.diagnosticAssumeGenerated then
    pure (.error { message := "--cache-layer cannot be combined with diagnostic generated assumptions" })
  else
    let declarations := prepareDeclarations config state
    let observer? : Option MPC.Adapters.Layer.ReplayObserver :=
      match config.replayOptions.telemetry with
      | .off => none
      | .text | .jsonl =>
          some fun step => do
            let status :=
              match step.status with
              | .reused => ReplayStatus.reused
              | .checked => ReplayStatus.checked
              | .rejected => ReplayStatus.rejected
            emitDeclarationTelemetry config.replayOptions.telemetry {
              index := step.index,
              kind := MPC.Adapters.Export.declarationKindLabel step.declaration,
              name := MPC.Adapters.Export.declarationNameLabel step.declaration,
              elapsedMs := step.elapsedMs,
              cumulativeMs := step.cumulativeMs,
              status,
              profile? := none
            }
      | .profileJsonl => none
    match ← MPC.Adapters.Layer.cacheSqliteWithObserver MPC.Configs.LeanCore429 layerPath state.audit declarations observer? with
    | .error err => pure (.error { message := s!"while using cache layer {layerPath}: {err.message}" })
    | .ok summary =>
        pure (.ok { env := summary.env, reused := summary.reused, checked := summary.checked })

def saveLayerConfig (config : Config) (state : MPC.Adapters.Export.ParseState)
    (layerPath : System.FilePath) : IO (Result MPC.Adapters.Layer.SaveSummary) := do
  if config.checkedLayerPath?.isSome || config.loadLayerPath?.isSome || config.cacheLayerPath?.isSome then
    pure (.error { message := "--save-layer cannot be combined with --checked-layer, --load-layer, or --cache-layer" })
  else if config.limit?.isSome then
    pure (.error { message := "--save-layer cannot be combined with --limit" })
  else if config.profileDeclaration?.isSome then
    pure (.error { message := "--save-layer cannot be combined with --profile-declaration" })
  else if config.replayOptions.telemetry != .off then
    pure (.error { message := "--save-layer cannot be combined with telemetry output" })
  else if config.replayOptions.trace then
    pure (.error { message := "--save-layer cannot be combined with --trace" })
  else if config.diagnosticAssumeGenerated then
    pure (.error { message := "--save-layer cannot be combined with diagnostic generated assumptions" })
  else
    match ← MPC.Adapters.Layer.checkSavePath layerPath with
    | .error err => pure (.error err)
    | .ok () =>
        MPC.Adapters.Layer.saveFromState MPC.Configs.LeanCore429 layerPath state

def profileDeclarationAt (config : Config) (state : MPC.Adapters.Export.ParseState)
    (index : Nat) : IO (Result Unit) := do
  let declarations := prepareDeclarations { config with limit? := none } state
  let prefixDeclarations := declarations.take index
  let some declaration := declarations[index]?
    | pure (.error { message := s!"profile declaration index {index} is out of range" })
  match ← replayLoop MPC.Configs.LeanCore429 {} 0 0 emptyEnv prefixDeclarations with
  | .error err => pure (.error err)
  | .ok env =>
      let telemetry : DeclarationTelemetry := {
        index,
        kind := MPC.Adapters.Export.declarationKindLabel declaration,
        name := MPC.Adapters.Export.declarationNameLabel declaration,
        elapsedMs := 0,
        cumulativeMs := 0,
        status := .checked,
        profile? := some (profileDeclaration env declaration)
      }
      IO.println telemetry.toJson.compress
      pure (.ok ())

def run (args : List String) : IO UInt32 := do
  match ← parseArgs args with
  | .error err => do
      IO.eprintln usage
      if err != usage then
        IO.eprintln s!"error: {err}"
      return 2
  | .ok config => do
      let input ← IO.FS.readFile config.inputPath
      match MPC.Adapters.Export.parseString input with
      | .error err => do
          printOutcome "unsupported" config.inputPath err.message
          return 2
      | .ok state =>
          match config.saveLayerPath? with
          | some layerPath =>
              match ← saveLayerConfig config state layerPath with
              | .ok summary => do
                  printOutcome "layer-saved" config.inputPath
                    s!"layer: {layerPath}; checked {summary.declarations} declaration entries; environment size {summary.envLength}"
                  return 0
              | .error err => do
                  printOutcome "rejected" config.inputPath err.message
                  return 1
          | none => pure ()
          match config.loadLayerPath? with
          | some layerPath =>
              match ← replayWithSavedLayer config state layerPath with
              | .ok result => do
                  let checkedTotal :=
                    match config.limit? with
                    | some limit => Nat.min limit state.declarations.length
                    | none => state.declarations.length
                  let prefixText :=
                    match config.limit? with
                    | some _ => "prefix "
                    | none => ""
                  printOutcome "layer-accepted" config.inputPath
                    s!"reused {result.reused} declaration entries; checked {prefixText}{result.checked} declaration entries; target declarations {checkedTotal}; environment size {result.env.length}"
                  return 0
              | .error err => do
                  printOutcome "rejected" config.inputPath err.message
                  return 1
          | none => pure ()
          match config.cacheLayerPath? with
          | some layerPath =>
              match ← replayWithCacheLayer config state layerPath with
              | .ok result => do
                  printOutcome "cache-accepted" config.inputPath
                    s!"reused {result.reused} declaration entries; checked {result.checked} declaration entries; target declarations {state.declarations.length}; environment size {result.env.length}; cache layer {layerPath}"
                  return 0
              | .error err => do
                  printOutcome "rejected" config.inputPath err.message
                  return 1
          | none => pure ()
          match config.checkedLayerPath? with
          | some layerPath =>
              match ← replayWithCheckedLayer config state layerPath with
              | .ok result => do
                  let checkedTotal :=
                    match config.limit? with
                    | some limit => Nat.min limit state.declarations.length
                    | none => state.declarations.length
                  let prefixText :=
                    match config.limit? with
                    | some _ => "prefix "
                    | none => ""
                  printOutcome "layer-accepted" config.inputPath
                    s!"reused {result.reused} declaration entries; checked {prefixText}{result.checked} declaration entries; target declarations {checkedTotal}; environment size {result.env.length}"
                  return 0
              | .error err => do
                  printOutcome "rejected" config.inputPath err.message
                  return 1
          | none => pure ()
          match config.profileDeclaration? with
          | some index =>
              match ← profileDeclarationAt config state index with
              | .ok () => return 0
              | .error err => do
                  printOutcome "rejected" config.inputPath err.message
                  return 1
          | none => pure ()
          match ← replayConfig config state with
          | .error err => do
              printOutcome "rejected" config.inputPath err.message
              return 1
          | .ok env => do
              let checked :=
                match config.limit? with
                | some limit => Nat.min limit state.declarations.length
                | none => state.declarations.length
              let prefixText :=
                match config.limit? with
                | some _ => "prefix "
                | none => ""
              let assumptionText :=
                let count := generatedAssumptionCount config state
                if !config.diagnosticAssumeGenerated then
                  ""
                else
                  s!"; assumed {count} generated-support declarations"
              let status :=
                if config.diagnosticAssumeGenerated then
                  "diagnostic-accepted"
                else
                  "accepted"
              printOutcome status config.inputPath s!"checked {prefixText}{checked} declaration entries; environment size {env.length}{assumptionText}"
              return 0

end MPC.CheckExport

def main (args : List String) : IO UInt32 :=
  MPC.CheckExport.run args
