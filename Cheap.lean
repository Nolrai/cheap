
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Germ

def Star (α : Type u) : Type u := Σ F : Filter ℕ, germ F
