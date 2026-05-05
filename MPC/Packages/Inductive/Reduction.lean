import MPC.Env

namespace MPC

abbrev WhnfFn := Manifest → Env → LevelContext → Expr → Result Expr

def findConstructorIndex? (name : Name) : List SimpleConstructorSpec → Nat → Option Nat
  | [], _ => none
  | ctor :: rest, index =>
      if ctor.name == name then some index else findConstructorIndex? name rest (index + 1)

def findSimpleRecursorConstructor? (name : Name) : List SimpleRecursorConstructorInfo →
    Option SimpleRecursorConstructorInfo
  | [] => none
  | ctor :: rest =>
      if ctor.name == name then some ctor else findSimpleRecursorConstructor? name rest

def findMutualRecursorConstructor? (name : Name) : List MutualRecursorConstructorInfo →
    Option MutualRecursorConstructorInfo
  | [] => none
  | ctor :: rest =>
      if ctor.name == name then some ctor else findMutualRecursorConstructor? name rest

def findIndexedConstructor? (name : Name) : List IndexedRecursorConstructorInfo →
    Option IndexedRecursorConstructorInfo
  | [] => none
  | ctor :: rest =>
      if ctor.name == name then some ctor else findIndexedConstructor? name rest

def findNestedConstructor? (name : Name) : List NestedRecursorConstructorInfo →
    Option NestedRecursorConstructorInfo
  | [] => none
  | ctor :: rest =>
      if ctor.name == name then some ctor else findNestedConstructor? name rest

def nestedMinorIndex? (targets : List NestedRecursorTargetInfo) (targetIndex : Nat)
    (ctorName : Name) : Option Nat :=
  let rec loopTargets (offset index : Nat) : List NestedRecursorTargetInfo → Option Nat
    | [] => none
    | target :: rest =>
        if index == targetIndex then
          match target.constructors.findIdx? (fun ctor => ctor.name == ctorName) with
          | some ctorIndex => some (offset + ctorIndex)
          | none => none
        else
          loopTargets (offset + target.constructors.length) (index + 1) rest
  loopTargets 0 0 targets

def levelListsDefEq (left right : List Level) : Bool :=
  left.length == right.length &&
    (left.zip right).all fun pair => pair.1.defEq pair.2

def exprListsAlphaEq (left right : List Expr) : Bool :=
  left.length == right.length &&
    (left.zip right).all fun pair => pair.1.alphaEq pair.2

def recursorSourceOrderBvars (count offset : Nat) : List Expr :=
  (List.range count).map fun index =>
    .bvar (offset + count - 1 - index)

def liftExprs (amount : Nat) (exprs : List Expr) : List Expr :=
  exprs.map fun expr => expr.lift amount

def instantiateSourceArgsAfterLocals (expr : Expr) (localCount : Nat) (args : List Expr) :
    Expr :=
  expr.instantiateManyFrom localCount args

def instantiateRecursiveFieldBinderType
    (paramArgs fieldArgs : List Expr) (boundLocals : Nat) (binder : Binder) : Expr :=
  instantiateSourceArgsAfterLocals binder.type boundLocals (paramArgs ++ fieldArgs)

def recursiveFieldBody
    (recursor motive : Expr)
    (paramArgs minorArgs fieldArgs : List Expr)
    (fieldValue : Expr)
    (rec : IndexedRecursiveFieldInfo)
    (boundLocals : Nat) : Expr :=
  let localArgs := recursorSourceOrderBvars boundLocals 0
  let recursiveIndices :=
    rec.indices.map fun index =>
      instantiateSourceArgsAfterLocals index boundLocals (paramArgs ++ fieldArgs)
  let target := Expr.mkApps (fieldValue.lift boundLocals) localArgs
  Expr.mkApps recursor
    (liftExprs boundLocals paramArgs ++
      [motive.lift boundLocals] ++
      liftExprs boundLocals minorArgs ++
      recursiveIndices ++
      [target])

partial def recursiveFieldResult
    (recursor motive : Expr)
    (paramArgs minorArgs fieldArgs : List Expr)
    (fieldValue : Expr)
    (rec : IndexedRecursiveFieldInfo) :
    Nat → List Binder → Expr
  | boundLocals, [] =>
      recursiveFieldBody recursor motive paramArgs minorArgs fieldArgs fieldValue rec boundLocals
  | boundLocals, binder :: rest =>
      .lam binder.name
        (instantiateRecursiveFieldBinderType paramArgs fieldArgs boundLocals binder)
        (recursiveFieldResult recursor motive paramArgs minorArgs fieldArgs fieldValue rec
          (boundLocals + 1) rest)

def nestedRecursiveFieldBody
    (targets : List NestedRecursorTargetInfo)
    (levels : List Level)
    (paramArgs motiveArgs minorArgs fieldArgs : List Expr)
    (fieldValue : Expr)
    (rec : NestedRecursiveFieldInfo)
    (boundLocals : Nat) : Result Expr := do
  let some recTarget := listGet? targets rec.targetIndex
    | fail s!"unknown nested recursor target {rec.targetIndex}"
  let localArgs := recursorSourceOrderBvars boundLocals 0
  let targetArgs :=
    rec.targetArgs.map fun arg =>
      instantiateSourceArgsAfterLocals arg boundLocals (paramArgs ++ fieldArgs)
  let target := Expr.mkApps (fieldValue.lift boundLocals) localArgs
  pure
    (Expr.mkApps (.const recTarget.recursorName levels)
      (liftExprs boundLocals paramArgs ++
        liftExprs boundLocals motiveArgs ++
        liftExprs boundLocals minorArgs ++
        targetArgs ++
        [target]))

partial def nestedRecursiveFieldResult
    (targets : List NestedRecursorTargetInfo)
    (levels : List Level)
    (paramArgs motiveArgs minorArgs fieldArgs : List Expr)
    (fieldValue : Expr)
    (rec : NestedRecursiveFieldInfo) :
    Nat → List Binder → Result Expr
  | boundLocals, [] =>
      nestedRecursiveFieldBody
        targets
        levels
        paramArgs
        motiveArgs
        minorArgs
        fieldArgs
        fieldValue
        rec
        boundLocals
  | boundLocals, binder :: rest => do
      pure
        (.lam binder.name
          (instantiateRecursiveFieldBinderType paramArgs fieldArgs boundLocals binder)
          (← nestedRecursiveFieldResult
            targets
            levels
            paramArgs
            motiveArgs
            minorArgs
            fieldArgs
            fieldValue
            rec
            (boundLocals + 1)
            rest))

partial def reduceSimpleRecursorCtor?
    (name : Name)
    (levels : List Level)
    (spec : SimpleInductiveSpec)
    (info : SimpleRecursorInfo)
    (paramArgs : List Expr)
    (motive : Expr)
    (minorArgs : List Expr)
    (trailing : List Expr)
    (ctorName : Name)
    (fieldArgs : List Expr) : Result (Option Expr) := do
  let some ctorIndex := findConstructorIndex? ctorName spec.constructors 0
    | pure none
  let some ctorInfo := findSimpleRecursorConstructor? ctorName info.constructors
    | pure none
  let some minor := listGet? minorArgs ctorIndex
    | pure none
  if fieldArgs.length != ctorInfo.fieldCount then
    pure none
  else
    let recursor := .const name levels
    let recursiveResults ←
      ctorInfo.recursiveFields.mapM fun rec => do
        let some fieldValue := listGet? fieldArgs rec.fieldIndex
          | fail s!"missing recursive field {rec.fieldIndex} for {ctorName}"
        pure
          (Expr.mkApps recursor
            (paramArgs ++ [motive] ++ minorArgs ++ [fieldValue]))
    let value := Expr.mkApps minor (fieldArgs ++ recursiveResults)
    pure (some (Expr.mkApps value trailing))

partial def reduceSimpleRecursor? (whnfFn : WhnfFn) (manifest : Manifest) (env : Env)
    (levelParams : LevelContext) (name : Name) (info : SimpleRecursorInfo)
    (levels : List Level) (args : List Expr) : Result (Option Expr) := do
  if !manifest.supportsSimpleInductives then
    pure none
  else
    match env.find? info.inductiveName with
    | some inductInfo =>
        match inductInfo.kind with
        | .inductiveType spec =>
            let required := spec.params.length + 1 + spec.constructors.length + 1
            if args.length < required then
              pure none
            else
              let paramArgs := args.take spec.params.length
              let some motive := listGet? args spec.params.length
                | pure none
              let minorArgs := (args.drop (spec.params.length + 1)).take spec.constructors.length
              let some target := listGet? args (required - 1)
                | pure none
              let trailing := args.drop required
              let targetWhnf ← whnfFn manifest env levelParams target
              let (targetHead, targetArgs) := Expr.getAppFnArgs targetWhnf
              match targetWhnf with
              | .lit (.nat value) =>
                  if spec.name != "Nat" then
                    pure none
                  else
                    match value with
                    | 0 =>
                        reduceSimpleRecursorCtor? name levels spec info paramArgs motive minorArgs trailing
                          "Nat.zero" []
                    | pred + 1 =>
                        reduceSimpleRecursorCtor? name levels spec info paramArgs motive minorArgs trailing
                          "Nat.succ" [.lit (.nat pred)]
              | _ =>
                  match targetHead with
                  | Expr.const ctorName ctorLevels =>
                      if ctorLevels.length != spec.levelParams.length then
                        pure none
                      else
                        reduceSimpleRecursorCtor? name levels spec info paramArgs motive minorArgs trailing
                          ctorName (targetArgs.drop spec.params.length)
                  | _ => pure none
        | _ => pure none
    | none => pure none

partial def reduceMutualRecursor? (whnfFn : WhnfFn) (manifest : Manifest) (env : Env)
    (levelParams : LevelContext) (name : Name) (info : MutualRecursorInfo)
    (levels : List Level) (args : List Expr) : Result (Option Expr) := do
  if !manifest.supportsInductiveBlocks then
    pure none
  else
    let some targetName := listGet? info.inductiveNames info.targetIndex
      | pure none
    if name != targetName ++ ".rec" then
      pure none
    else
      match env.find? targetName with
      | some { kind := .inductiveType targetSpec, .. } =>
          let motiveCount := info.inductiveNames.length
          let minorCount := info.constructors.length
          let required := targetSpec.params.length + motiveCount + minorCount + 1
          if args.length < required then
            pure none
          else
            let paramArgs := args.take targetSpec.params.length
            let rest := args.drop targetSpec.params.length
            let motiveArgs := rest.take motiveCount
            let rest := rest.drop motiveCount
            let minorArgs := rest.take minorCount
            let some target := listGet? rest minorCount
              | pure none
            let trailing := rest.drop (minorCount + 1)
            let targetWhnf ← whnfFn manifest env levelParams target
            let (targetHead, targetArgs) := targetWhnf.getAppFnArgs
            match targetHead with
            | Expr.const ctorName ctorLevels =>
                if ctorLevels.length != targetSpec.levelParams.length then
                  pure none
                else
                  let some ctorInfo := findMutualRecursorConstructor? ctorName info.constructors
                    | pure none
                  if ctorInfo.inductiveIndex != info.targetIndex then
                    pure none
                  else
                    let some ctorIndex :=
                        info.constructors.findIdx? (fun ctor => ctor.name == ctorName)
                      | pure none
                    let some minor := listGet? minorArgs ctorIndex
                      | pure none
                    let fieldArgs := targetArgs.drop targetSpec.params.length
                    if fieldArgs.length != ctorInfo.fieldCount then
                      pure none
                    else
                      let recursiveResults ←
                        ctorInfo.recursiveFields.mapM fun rec => do
                          let some fieldValue := listGet? fieldArgs rec.fieldIndex
                            | fail s!"missing recursive field {rec.fieldIndex} for {ctorName}"
                          let some recName := listGet? info.inductiveNames rec.targetIndex
                            | fail s!"unknown mutual recursive target {rec.targetIndex}"
                          let recursor := .const (recName ++ ".rec") levels
                          pure (Expr.mkApps recursor
                            (paramArgs ++ motiveArgs ++ minorArgs ++ [fieldValue]))
                      let value := Expr.mkApps minor (fieldArgs ++ recursiveResults)
                      pure (some (Expr.mkApps value trailing))
            | _ => pure none
      | _ => pure none

partial def reduceNestedRecursor? (whnfFn : WhnfFn) (manifest : Manifest) (env : Env)
    (levelParams : LevelContext) (name : Name) (info : NestedRecursorInfo)
    (levels : List Level) (args : List Expr) : Result (Option Expr) := do
  if !manifest.supportsLean429NestedContainers then
    pure none
  else
    let some targetInfo := listGet? info.targets info.targetIndex
      | pure none
    if name != targetInfo.recursorName then
      pure none
    else
      match env.find? info.rootName with
      | some { kind := .inductiveType rootSpec, .. } =>
          let motiveCount := info.targets.length
          let minorCount :=
            info.targets.foldl (fun count target => count + target.constructors.length) 0
          let targetLocalCount := targetInfo.locals.length
          let required := rootSpec.params.length + motiveCount + minorCount + targetLocalCount + 1
          if args.length < required then
            pure none
          else
            let paramArgs := args.take rootSpec.params.length
            let rest := args.drop rootSpec.params.length
            let motiveArgs := rest.take motiveCount
            let rest := rest.drop motiveCount
            let minorArgs := rest.take minorCount
            let rest := rest.drop minorCount
            let targetLocalArgs := rest.take targetLocalCount
            let some target := listGet? rest targetLocalCount
              | pure none
            let trailing := rest.drop (targetLocalCount + 1)
            let targetWhnf ← whnfFn manifest env levelParams target
            let (targetHead, targetArgs) := targetWhnf.getAppFnArgs
            match targetHead with
            | Expr.const ctorName ctorLevels =>
                if !levelListsDefEq ctorLevels targetInfo.levels then
                  pure none
                else
                  let some ctorInfo := findNestedConstructor? ctorName targetInfo.constructors
                    | pure none
                  let some minorIndex := nestedMinorIndex? info.targets info.targetIndex ctorName
                    | pure none
                  let some minor := listGet? minorArgs minorIndex
                    | pure none
                  let fieldArgs := targetArgs.drop targetInfo.paramCount
                  if fieldArgs.length != ctorInfo.fields.length then
                    pure none
                  else
                    let expectedTargetLocalArgs :=
                      ctorInfo.targetArgs.map fun arg =>
                        instantiateSourceArgsAfterLocals arg 0 (paramArgs ++ fieldArgs)
                    if !exprListsAlphaEq targetLocalArgs expectedTargetLocalArgs then
                      pure none
                    else
                      let recursiveResults ←
                        ctorInfo.recursiveFields.mapM fun rec => do
                          let some fieldValue := listGet? fieldArgs rec.fieldIndex
                            | fail s!"missing recursive field {rec.fieldIndex} for {ctorName}"
                          nestedRecursiveFieldResult
                            info.targets
                            levels
                            paramArgs
                            motiveArgs
                            minorArgs
                            fieldArgs
                            fieldValue
                            rec
                            0
                            rec.binders
                      let value := Expr.mkApps minor (fieldArgs ++ recursiveResults)
                      pure (some (Expr.mkApps value trailing))
            | _ => pure none
      | _ => pure none

partial def reduceIndexedRecursor? (whnfFn : WhnfFn) (manifest : Manifest) (env : Env)
    (levelParams : LevelContext) (name : Name) (info : IndexedRecursorInfo)
    (levels : List Level) (args : List Expr) : Result (Option Expr) := do
  if !manifest.supportsIndexedInductives then
    pure none
  else
    match env.find? info.inductiveName with
    | some inductInfo =>
        match inductInfo.kind with
        | .indexedInductiveType spec =>
            let required := spec.params.length + 1 + spec.constructors.length + spec.indices.length + 1
            if args.length < required then
              pure none
            else
              let paramArgs := args.take spec.params.length
              let some motive := listGet? args spec.params.length
                | pure none
              let minorArgs := (args.drop (spec.params.length + 1)).take spec.constructors.length
              let some target := listGet? args (required - 1)
                | pure none
              let trailing := args.drop required
              let targetWhnf ← whnfFn manifest env levelParams target
              let (targetHead, targetArgs) := targetWhnf.getAppFnArgs
              match targetHead with
              | Expr.const ctorName ctorLevels =>
                  if ctorLevels.length != spec.levelParams.length then
                    pure none
                  else
                    let some ctorInfo := findIndexedConstructor? ctorName info.constructors
                      | pure none
                    let some ctorIndex := info.constructors.findIdx? (fun ctor => ctor.name == ctorName)
                      | pure none
                    let some minor := listGet? minorArgs ctorIndex
                      | pure none
                    let fieldArgs := targetArgs.drop spec.params.length
                    if fieldArgs.length != ctorInfo.fieldCount then
                      pure none
                    else
                      let recursor := .const name levels
                      let recursiveResults ←
                        ctorInfo.recursiveFields.mapM fun rec => do
                          let some fieldValue := listGet? fieldArgs rec.fieldIndex
                            | fail s!"missing recursive field {rec.fieldIndex} for {ctorName}"
                          pure
                            (recursiveFieldResult recursor motive paramArgs minorArgs fieldArgs
                              fieldValue rec 0 rec.binders)
                      let value := Expr.mkApps minor (fieldArgs ++ recursiveResults)
                      pure (some (Expr.mkApps value trailing))
              | _ => pure none
        | _ => pure none
    | none => pure none

end MPC
