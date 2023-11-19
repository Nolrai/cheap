import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Rat.Order
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.Order.Archimedean
import Mathlib.Init.Set
import Mathlib.Order.Zorn
import std
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Cofinite
import Mathlib.Order.Filter.Ultrafilter

def Filter.lift_setoid (F : Filter β) (S : Setoid α) : Setoid (β → α) where
  r a b := ∀ᶠ i in F, S.r (a i) (b i)
  iseqv := {
    refl := λ x ↦ Filter.eventually_of_forall λ i => S.refl (x i)
    symm := λ {_x _y} x_y ↦ Eventually.mp x_y $ Filter.eventually_of_forall (λ _ => S.symm)
    trans := λ {_x _y _z} x_y y_z ↦ Eventually.mp y_z $ Eventually.mp x_y $ eventually_of_forall $
      λ _i x_y' y_z' ↦ S.trans x_y' y_z'
  }

def Setoid.trivial α : Setoid α where
  r a b := a = b
  iseqv := ⟨by simp, by simp, by simp⟩

def Star (α : Sort v) := Quotient
  ∘ Filter.lift_setoid ((Filter.hyperfilter ℕ).toFilter)
  $ Setoid.trivial α

instance : Functor Star where
  map f := Quotient.lift (f ∘ ·)


