import MPC.Adapters.Export

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
  limit? : Option Nat := none
  replayOptions : ReplayOptions := {}
  diagnosticAssumeGenerated : Bool := false

def usage : String :=
  "usage: mpc-check-export [<export.ndjson>]\n" ++
  "       mpc-check-export --input <export.ndjson>\n" ++
  "       mpc-check-export [--limit <n>] [--trace] [--stats|--stats-jsonl|--profile-jsonl] [--diagnostic-assume-generated] <export.ndjson>\n" ++
  "       mpc-check-export [--assume-generated] <export.ndjson>  (alias for diagnostic mode)\n" ++
  "       IN=<export.ndjson> mpc-check-export"

def filePath (path : String) : Except String System.FilePath :=
  if path.isEmpty then
    .error "empty input path"
  else
    pure (System.FilePath.mk path)

def configFromPath
    (limit? : Option Nat)
    (replayOptions : ReplayOptions)
    (diagnosticAssumeGenerated : Bool)
    (path : String) :
    Except String Config := do
  pure { inputPath := (← filePath path), limit?, replayOptions, diagnosticAssumeGenerated }

def configFromEnv
    (limit? : Option Nat)
    (replayOptions : ReplayOptions)
    (diagnosticAssumeGenerated : Bool) : IO (Except String Config) := do
  match ← IO.getEnv "IN" with
  | some path => pure (configFromPath limit? replayOptions diagnosticAssumeGenerated path)
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
    (limit? : Option Nat)
    (replayOptions : ReplayOptions)
    (diagnosticAssumeGenerated : Bool) :
    List String → Except String (Option String × Option Nat × ReplayOptions × Bool)
  | [] => pure (input?, limit?, replayOptions, diagnosticAssumeGenerated)
  | "--input" :: path :: rest => do
      parseArgsLoop (← setInputPath input? path) limit? replayOptions diagnosticAssumeGenerated rest
  | "--input" :: [] => .error "missing value after --input"
  | "--limit" :: value :: rest => do
      if limit?.isSome then
        .error "multiple limits"
      else
        parseArgsLoop input? (some (← parseNatArgument "limit" value)) replayOptions diagnosticAssumeGenerated rest
  | "--limit" :: [] => .error "missing value after --limit"
  | "--trace" :: rest =>
      parseArgsLoop input? limit? { replayOptions with trace := true } diagnosticAssumeGenerated rest
  | "--stats" :: rest => do
      parseArgsLoop input? limit? (← setTelemetryFormat replayOptions .text) diagnosticAssumeGenerated rest
  | "--stats-jsonl" :: rest => do
      parseArgsLoop input? limit? (← setTelemetryFormat replayOptions .jsonl) diagnosticAssumeGenerated rest
  | "--profile-jsonl" :: rest => do
      parseArgsLoop input? limit? (← setTelemetryFormat replayOptions .profileJsonl) diagnosticAssumeGenerated rest
  | "--diagnostic-assume-generated" :: rest =>
      parseArgsLoop input? limit? replayOptions true rest
  | "--assume-generated" :: rest =>
      parseArgsLoop input? limit? replayOptions true rest
  | "--help" :: _ => .error usage
  | arg :: rest =>
      if arg.startsWith "-" then
        .error s!"unknown argument: {arg}"
      else do
        parseArgsLoop (← setInputPath input? arg) limit? replayOptions diagnosticAssumeGenerated rest

def parseArgs : List String → IO (Except String Config)
  | args => do
      match parseArgsLoop none none {} false args with
      | .error err => pure (.error err)
      | .ok (some path, limit?, replayOptions, diagnosticAssumeGenerated) =>
          pure (configFromPath limit? replayOptions diagnosticAssumeGenerated path)
      | .ok (none, limit?, replayOptions, diagnosticAssumeGenerated) =>
          configFromEnv limit? replayOptions diagnosticAssumeGenerated

def printOutcome (status : String) (path : System.FilePath) (message : String) : IO Unit := do
  IO.println status
  IO.println s!"artifact: {path}"
  if message != "" then
    IO.println s!"message: {message}"

inductive ReplayStatus where
  | checked
  | rejected

def ReplayStatus.label : ReplayStatus → String
  | .checked => "checked"
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
  indexedRecursorHeadApps : Nat := 0
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
  indexedRecursorConsts : Nat := 0
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
    indexedRecursorHeadApps := left.indexedRecursorHeadApps + right.indexedRecursorHeadApps
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
    indexedRecursorConsts := left.indexedRecursorConsts + right.indexedRecursorConsts
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
      | .indexedRecursor .. => { base with indexedRecursorConsts := base.indexedRecursorConsts + 1 }
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
          | .indexedRecursor .. => { base with indexedRecursorHeadApps := base.indexedRecursorHeadApps + 1 }
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
    ("profile_indexed_recursor_head_apps", jsonNat exprs.indexedRecursorHeadApps),
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
    ("profile_indexed_recursor_consts", jsonNat exprs.indexedRecursorConsts),
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
