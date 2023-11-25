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

open Filter

instance Star.Setoid {α} : Setoid (ℕ → α) where
  r a b := a =ᶠ[Filter.hyperfilter ℕ] b
  iseqv := ⟨Filter.EventuallyEq.refl _, Filter.EventuallyEq.symm, Filter.EventuallyEq.trans⟩

theorem Star.r_def (f₁ f₂ : ℕ → α) : (f₁ ≈ f₂) = (f₁ =ᶠ[Filter.hyperfilter ℕ] f₂) := rfl

def Star (α : Type u) := Quotient (Star.Setoid (α := α))

abbrev Star.mk : (ℕ → α) → Star α := Quotient.mk (Star.Setoid (α := α))

def Star.map
  (g : ((ℕ → α) → (ℕ → β)))
  (hyp : ∀ a b, ∀ᶠ (i : ℕ) in ↑(Filter.hyperfilter ℕ), a i = b i → g a i = g b i)
  : Star α → Star β
  := Quotient.map g (λ a b a_eqv_b ↦ Eventually.mp a_eqv_b (hyp a b))

def Star.lift
  {α β : Type u}
  (g : ((ℕ → α) → β))
  (hyp : ∀ a b : ℕ → α, (∀ᶠ (x : ℕ) in ↑(Filter.hyperfilter ℕ), (a x) = (b x)) → g a = g b)
  : Star α → β := Quotient.lift (s := Star.Setoid) g hyp

def Star.seq {α β : Type u} (mf : Star (α → β)) (mx : Unit → Star α) : Star β := by
  apply Quotient.map₂' (λ f a i ↦ f i (a i)) _ mf (mx () )
  intros mf₁ mf₂ mf_equiv mx₁ mx₂ mx_equiv
  simp
  filter_upwards [mx_equiv, mf_equiv]
  intros i mx_eq mf_eq
  clear * - mx_eq mf_eq
  rw [mx_eq, mf_eq]

def Star.mk_mk (f : ℕ → ℕ → α) : Star (Star α) := Star.mk (Star.mk ∘ f)

noncomputable
def Star.out_out (s : Star (Star α)) : ℕ → ℕ → α :=
  Quotient.out ∘ s.out

theorem Star.mk_mk_out_out {α : Type u} (m : Star (Star α)) : Star.mk_mk m.out_out = m := by
  simp_rw [Star.out_out, Star.mk_mk, Function.comp, Star.mk]
  rw [← Quotient.out_eq' m]
  simp

noncomputable
def Star.lift_map_spec {α β : Type u} (f : (ℕ → ℕ → α) → β) ( ss : Star (Star α)) : β :=
  f ss.out_out

def Function.join : (α → α → β) → α → β :=
  λ f a ↦ f a a

noncomputable
def Star.join_spec {α : Type u} (ss : Star (Star α)) : Star α :=
  ss.lift_map_spec (λ x ↦ Star.mk $ (Function.join : (ℕ → ℕ → α) → ℕ → α) x)

def Star.functor_map {α β : Type u} (f : α → β) : Star α → Star β := by
  apply Star.map
  case g => use (f ∘ ·)
  case hyp =>
    intros a b
    filter_upwards
    intros i a_eq_b
    simp [a_eq_b]

instance : Applicative Star where
  map := Star.functor_map
  pure a := Star.mk (λ _ ↦ a)
  seq := Star.seq

