import MPC.Env

namespace MPC

def listGet? : List α → Nat → Option α
  | [], _ => none
  | value :: _, 0 => some value
  | _ :: rest, index + 1 => listGet? rest index

def findConstructorIndex? (name : Name) : List SimpleConstructorSpec → Nat → Option Nat
  | [], _ => none
  | ctor :: rest, index =>
      if ctor.name == name then some index else findConstructorIndex? name rest (index + 1)

def findIndexedConstructor? (name : Name) : List IndexedRecursorConstructorInfo →
    Option IndexedRecursorConstructorInfo
  | [] => none
  | ctor :: rest =>
      if ctor.name == name then some ctor else findIndexedConstructor? name rest

def instantiateSourceArgs (expr : Expr) (args : List Expr) : Expr :=
  args.reverse.foldl (fun expr arg => Expr.instantiate1 expr arg) expr

mutual

partial def reduceSimpleRecursor? (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (_name : Name) (info : SimpleRecursorInfo) (_levels : List Level) (args : List Expr) :
    Result (Option Expr) := do
  if manifest.inductives != .simple then
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
              let minorArgs := (args.drop (spec.params.length + 1)).take spec.constructors.length
              let some target := listGet? args (required - 1)
                | pure none
              let trailing := args.drop required
              let targetWhnf ← whnf manifest env levelParams target
              let (targetHead, targetArgs) := Expr.getAppFnArgs targetWhnf
              match targetHead with
              | Expr.const ctorName ctorLevels =>
                  match findConstructorIndex? ctorName spec.constructors 0 with
                  | some ctorIndex =>
                      if ctorLevels.length != spec.levelParams.length then
                        pure none
                      else
                        let some minor := listGet? minorArgs ctorIndex
                          | pure none
                        let value := Expr.mkApps minor (targetArgs.drop spec.params.length)
                        pure (some (Expr.mkApps value trailing))
                  | none => pure none
              | _ => pure none
        | _ => pure none
    | none => pure none

partial def reduceIndexedRecursor? (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (name : Name) (info : IndexedRecursorInfo) (levels : List Level) (args : List Expr) :
    Result (Option Expr) := do
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
              let targetWhnf ← whnf manifest env levelParams target
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
                          let recursiveIndices :=
                            rec.indices.map fun index =>
                              instantiateSourceArgs index (paramArgs ++ fieldArgs)
                          pure
                            (Expr.mkApps recursor
                              (paramArgs ++ [motive] ++ minorArgs ++ recursiveIndices ++ [fieldValue]))
                      let value := Expr.mkApps minor (fieldArgs ++ recursiveResults)
                      pure (some (Expr.mkApps value trailing))
              | _ => pure none
        | _ => pure none
    | none => pure none

partial def whnf (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (expr : Expr) : Result Expr := do
  match expr with
  | .letE _ _ value body =>
      whnf manifest env levelParams (Expr.instantiate1 body value)
  | .app fn arg =>
      let appExpr := Expr.app fn arg
      let (head, args) := Expr.getAppFnArgs appExpr
      let head ← whnf manifest env levelParams head
      match head with
      | Expr.const name levels =>
          match env.find? name with
          | some { kind := .recursor info, .. } =>
              match ← reduceSimpleRecursor? manifest env levelParams name info levels args with
              | some reduced => whnf manifest env levelParams reduced
              | none => pure (Expr.mkApps head args)
          | some { kind := .indexedRecursor info, .. } =>
              match ← reduceIndexedRecursor? manifest env levelParams name info levels args with
              | some reduced => whnf manifest env levelParams reduced
              | none => pure (Expr.mkApps head args)
          | _ => pure (Expr.mkApps head args)
      | .lam _ _ body =>
          match args with
          | first :: rest =>
              whnf manifest env levelParams (Expr.mkApps (Expr.instantiate1 body first) rest)
          | [] => pure head
      | _ => pure (Expr.mkApps head args)
  | .const name levels =>
      match env.find? name with
      | some info =>
          match info.kind, info.instantiateValue? levels with
          | .definition, some value =>
              whnf manifest env levelParams value
          | _, _ => pure (.const name levels)
      | none => pure (.const name levels)
  | _ => pure expr

end

partial def normalize (manifest : Manifest) (env : Env) (levelParams : LevelContext)
    (expr : Expr) : Result Expr := do
  let expr ← whnf manifest env levelParams expr
  match expr with
  | .app fn arg => pure (.app (← normalize manifest env levelParams fn) (← normalize manifest env levelParams arg))
  | .lam name type body =>
      pure (.lam name (← normalize manifest env levelParams type) (← normalize manifest env levelParams body))
  | .forallE name type body =>
      pure (.forallE name (← normalize manifest env levelParams type) (← normalize manifest env levelParams body))
  | .letE name type value body =>
      pure
        (.letE name
          (← normalize manifest env levelParams type)
          (← normalize manifest env levelParams value)
          (← normalize manifest env levelParams body))
  | _ => pure expr

end MPC
