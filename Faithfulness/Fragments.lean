import Faithfulness.Accepted
import Faithfulness.ModuleB

namespace LeanLeanFaithfulness.Fragments

structure Fragment where
  label : String
  roots : List Lean.Name

def acceptedRoots : List Lean.Name :=
  [
    `LeanLeanFaithfulness.Accepted.transparentId,
    `LeanLeanFaithfulness.Accepted.abbrevTrue,
    `LeanLeanFaithfulness.Accepted.opaqueTrue,
    `LeanLeanFaithfulness.Accepted.LocalNat,
    `LeanLeanFaithfulness.Accepted.two,
    `LeanLeanFaithfulness.Accepted.literalNat,
    `LeanLeanFaithfulness.Accepted.PolyBox,
    `LeanLeanFaithfulness.Accepted.PTrue,
    `LeanLeanFaithfulness.Accepted.POr,
    `LeanLeanFaithfulness.Accepted.MutEven,
    `LeanLeanFaithfulness.Accepted.MutNestA,
    `LeanLeanFaithfulness.Accepted.MutNestB,
    `LeanLeanFaithfulness.Accepted.ProofBox,
    `LeanLeanFaithfulness.Accepted.rel,
    `LeanLeanFaithfulness.Accepted.q,
    `LeanLeanFaithfulness.Accepted.liftedBool,
    `LeanLeanFaithfulness.Accepted.liftedTrue,
    `LeanLeanFaithfulness.Accepted.sigmaPair,
    `LeanLeanFaithfulness.Accepted.subtypeTrue,
    `LeanLeanFaithfulness.Accepted.SigmaBox,
    `LeanLeanFaithfulness.Accepted.trueTheorem,
    ``Eq,
    ``Quot,
    ``Nat,
    ``Bool,
    ``List,
    `LeanLeanFaithfulness.Accepted.IndexSingleton,
    `LeanLeanFaithfulness.Accepted.Vec1,
    `LeanLeanFaithfulness.Accepted.Pair,
    `LeanLeanFaithfulness.Accepted.Parent,
    `LeanLeanFaithfulness.Accepted.Child
  ]

def moduleBoundaryRoots : List Lean.Name :=
  [
    `LeanLeanFaithfulness.ModuleA.Boundary,
    `LeanLeanFaithfulness.ModuleA.value,
    `LeanLeanFaithfulness.ModuleB.importedValue
  ]

def coreLogicRoots : List Lean.Name :=
  [
    ``True,
    ``False,
    ``And,
    ``Or,
    ``Exists,
    ``Eq,
    ``Decidable
  ]

def coreDataRoots : List Lean.Name :=
  [
    ``Nat,
    ``Bool,
    ``List,
    ``Subtype,
    ``Sigma,
    ``Prod,
    ``PEmpty,
    ``PUnit,
    ``Unit,
    ``Empty,
    ``Option,
    ``ULift,
    ``PLift,
    ``PSigma,
    ``Quot
  ]

def replayRoots : List Lean.Name :=
  acceptedRoots ++ moduleBoundaryRoots ++ coreLogicRoots ++ coreDataRoots

def broadReplayFragments : List Fragment :=
  [
    {
      label := "accepted corpus and module boundary"
      roots := acceptedRoots ++ moduleBoundaryRoots
    },
    {
      label := "core logic fragment"
      roots := coreLogicRoots
    },
    {
      label := "core data fragment"
      roots := coreDataRoots
    },
    {
      label := "combined replay fragment"
      roots := replayRoots
    }
  ]

end LeanLeanFaithfulness.Fragments
