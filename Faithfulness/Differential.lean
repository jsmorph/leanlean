import Faithfulness.Fragments
import LeanLean.Import

open Lean Elab Command Term Meta

namespace LeanLeanFaithfulness.Differential

def liftResult (label : String) : LeanLean.Result α → CommandElabM α
  | .ok value => pure value
  | .error err => Lean.throwError m!"{label}: {err}"

def elabClosedTerm (stx : Syntax) : CommandElabM Expr :=
  liftTermElabM do
    let term ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars term

def reduceClosedTerm (term : Expr) : CommandElabM (Expr × Expr) :=
  liftTermElabM do
    let type ← instantiateMVars (← inferType term)
    let value ← instantiateMVars (← reduce term)
    pure (type, value)

def termRoots (term type value : Expr) : List Name :=
  LeanLean.Import.appendLeanNames
    (LeanLean.Import.appendLeanNames
      (LeanLean.Import.leanExprConstants term)
      (LeanLean.Import.leanExprConstants type))
    (LeanLean.Import.leanExprConstants value)

def zeroLevelInstantiation (info : Lean.ConstantInfo) : List Lean.Level :=
  info.levelParams.map fun _ => .zero

def translateLevels (levels : List Lean.Level) : LeanLean.Result (List LeanLean.Level) :=
  levels.mapM LeanLean.Import.translateLevel

def compareConstantType
    (label : String)
    (localEnv : LeanLean.Env)
    (info : Lean.ConstantInfo) : CommandElabM Unit := do
  let levels := zeroLevelInstantiation info
  let localLevels ← liftResult label <| translateLevels levels
  let localConst := LeanLean.Expr.const (LeanLean.Import.translateName info.name) localLevels
  let leanType := info.instantiateTypeLevelParams levels
  let localType ← liftResult label <| LeanLean.Import.translateExpr leanType
  let inferred ← liftResult label <| LeanLean.infer localEnv [] localConst
  liftResult label <| LeanLean.checkDefEq localEnv inferred localType

def compareDefinitionReduction
    (label : String)
    (localEnv : LeanLean.Env)
    (info : Lean.ConstantInfo) : CommandElabM Unit := do
  match info with
  | .defnInfo _ =>
      let levels := zeroLevelInstantiation info
      let localLevels ← liftResult label <| translateLevels levels
      let leanConst := Lean.Expr.const info.name levels
      let leanValue ← liftTermElabM do
        instantiateMVars (← reduce leanConst)
      let localExpected ← liftResult label <| LeanLean.Import.translateExpr leanValue
      let localConst := LeanLean.Expr.const (LeanLean.Import.translateName info.name) localLevels
      let normalized ← liftResult label <| LeanLean.normalize localEnv localConst
      liftResult label <| LeanLean.checkDefEq localEnv normalized localExpected
  | _ => pure ()

def compareImportedConstant
    (fragmentLabel : String)
    (localEnv : LeanLean.Env)
    (info : Lean.ConstantInfo) : CommandElabM Unit := do
  let label := s!"{fragmentLabel}: {info.name}"
  compareConstantType label localEnv info
  compareDefinitionReduction label localEnv info

def compareFragment (fragment : LeanLeanFaithfulness.Fragments.Fragment) : CommandElabM Unit := do
  let leanEnv ← Lean.getEnv
  let infos ←
    liftResult fragment.label <|
      LeanLean.Import.collectEnvironmentClosure leanEnv fragment.roots
  let localEnv ←
    liftResult fragment.label <|
      LeanLean.Import.replayEnvironmentClosure [] leanEnv fragment.roots
  for info in infos do
    compareImportedConstant fragment.label localEnv info

def compareTerm (label : String) (stx : Syntax) : CommandElabM Unit := do
  let term ← elabClosedTerm stx
  let (type, value) ← reduceClosedTerm term
  let leanEnv ← Lean.getEnv
  let localEnv ←
    liftResult label <| LeanLean.Import.replayEnvironmentClosure [] leanEnv (termRoots term type value)
  let localTerm ← liftResult label <| LeanLean.Import.translateExpr term
  let localType ← liftResult label <| LeanLean.Import.translateExpr type
  let localValue ← liftResult label <| LeanLean.Import.translateExpr value
  let inferred ← liftResult label <| LeanLean.infer localEnv [] localTerm
  liftResult label <| LeanLean.checkDefEq localEnv inferred localType
  let normalized ← liftResult label <| LeanLean.normalize localEnv localTerm
  liftResult label <| LeanLean.checkDefEq localEnv normalized localValue

run_cmd
  compareTerm
    "transparent definition type and value"
    (← `(LeanLeanFaithfulness.Accepted.transparentId true))
  compareTerm
    "abbreviation value"
    (← `(LeanLeanFaithfulness.Accepted.abbrevTrue))
  compareTerm
    "natural literal value"
    (← `(LeanLeanFaithfulness.Accepted.literalNat))
  compareTerm
    "primitive Nat recursor value"
    (← `(
      LeanLeanFaithfulness.Accepted.LocalNat.rec
        (motive := fun _ => LeanLeanFaithfulness.Accepted.LocalNat)
        LeanLeanFaithfulness.Accepted.LocalNat.zero
        (fun _ ih => LeanLeanFaithfulness.Accepted.LocalNat.succ ih)
        LeanLeanFaithfulness.Accepted.two))
  compareTerm
    "large Prop recursor value"
    (← `(
      LeanLeanFaithfulness.Accepted.PTrue.rec
        (motive := fun _ => Bool)
        true
        LeanLeanFaithfulness.Accepted.PTrue.intro))
  compareTerm
    "equality recursor value"
    (← `(
      @Eq.rec Bool true (fun _ _ => Bool) false true rfl))
  compareTerm
    "sort-polymorphic unit recursor value"
    (← `(
      @PUnit.rec.{1, 0} (fun _ => Bool) true PUnit.unit))
  compareTerm
    "Sigma projection value"
    (← `(LeanLeanFaithfulness.Accepted.sigmaPair.2))
  compareTerm
    "Subtype projection value"
    (← `(LeanLeanFaithfulness.Accepted.subtypeTrue.val))
  compareTerm
    "dependent projection value"
    (← `(
      LeanLeanFaithfulness.Accepted.SigmaBox.value
        { α := Bool, value := true }))
  compareTerm
    "core Decidable recursor value"
    (← `(
      @Decidable.rec True
        (fun _ => Bool)
        (fun _ => false)
        (fun _ => true)
        (Decidable.isTrue True.intro)))
  for fragment in LeanLeanFaithfulness.Fragments.broadReplayFragments do
    compareFragment fragment

end LeanLeanFaithfulness.Differential

def main : IO Unit :=
  pure ()
