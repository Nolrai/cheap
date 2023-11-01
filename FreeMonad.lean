import Std

unsafe
inductive FreeM (f : Type u → Type u) : Type u → Type (u+1) where
  | pure {α : Type u} : α → FreeM f α
  | bind {α : Type u}  : FreeM f (α → β) → FreeM f α → FreeM f β
