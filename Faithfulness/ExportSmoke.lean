namespace LeanLeanFaithfulness.ExportSmoke

universe u

inductive Box (α : Type u) : Type u where
  | mk : α → Box α

def rebox {α : Type u} : Box α → Box α
  | Box.mk value => Box.mk value

def unbox {α : Type u} : Box α → α
  | Box.mk value => value

end LeanLeanFaithfulness.ExportSmoke
