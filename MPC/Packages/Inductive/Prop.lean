import MPC.Check

namespace MPC.Packages.Inductive.Prop

def isPropLevel (level : Level) : Bool :=
  level.defEq .zero

def requiresPropPackage (manifest : Manifest) : Result Unit := do
  if manifest.prop == .enabled then
    pure ()
  else
    fail "Prop inductives require the Prop package"

def checkPropInductiveEnabled (manifest : Manifest) : Result Unit := do
  requiresPropPackage manifest
  if manifest.supportsPropInductives then
    pure ()
  else
    fail "proposition-valued inductives are disabled by the manifest"

def recursorMotiveLevel (specResultLevel : Level) : Level :=
  if isPropLevel specResultLevel then .zero else .param "u"

def recursorLevelParams (specResultLevel : Level) (specLevelParams : LevelContext) :
    LevelContext :=
  if isPropLevel specResultLevel then specLevelParams else "u" :: specLevelParams

end MPC.Packages.Inductive.Prop
