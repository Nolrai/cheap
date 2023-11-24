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

@[simp]
theorem Setoid.trivial.def : (Setoid.trivial α).r = (· = ·) := rfl

def Star.Setoid {α : Sort v} : Setoid (ℕ → α) :=
  Filter.lift_setoid (Filter.hyperfilter ℕ).toFilter $ Setoid.trivial α

infix:60 " ≋ " => λ a b ↦ Star.Setoid.r a b

def Star (α : Sort v) := Quotient $ Star.Setoid (α := α)

abbrev Star.mk : (ℕ → α) → Star α := Quotient.mk''

def Star.map
  (g : ((ℕ → α) → (ℕ → β)))
  (hyp : ∀ a b, ∀ᶠ (x : ℕ) in ↑(Filter.hyperfilter ℕ), (a x) = (b x) → (g a x) = (g b x))
  : Star α → Star β := Quotient.map' (s₁ := Star.Setoid) (s₂ := Star.Setoid) g $ by
    intros x y
    have : ∀ {α} (a b : ℕ → α), Star.Setoid.r a b = ∀ᶠ i in _, a i = b i := λ _ _ ↦ rfl
    rw [this, this (α := β)]; clear this
    intros h₁
    apply Filter.Eventually.mp h₁
    apply hyp

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
  have : ∀ (τ : Type u) x y, (Setoid.trivial τ).r x y = (x = y) := λ _ _ _ ↦ rfl
  simp [this] at *
  clear * - mx_eq mf_eq
  rw [mx_eq, mf_eq]

def Star.mk_mk (f : ℕ → ℕ → α) : Star (Star α) := Star.mk (Star.mk ∘ f)

noncomputable
def Star.out_out (s : Star (Star α)) : ℕ → ℕ → α :=
  Quotient.out' ∘ s.out'

theorem Star.mk_mk_out_out {α : Type u} (m : Star (Star α)) : Star.mk_mk m.out_out = m := by
  simp_rw [Star.out_out, Star.mk_mk, Function.comp, Star.mk]
  rw [← Quotient.out_eq' m]
  simp

noncomputable
def Star.lift_map_spec (f : (ℕ → ℕ → α) → β) : Star (Star α) → Star α

instance : Monad (Star : Type u → Type u) where
  map f := Star.map (f ∘ ·) _
  pure a := Star.mk (λ _ ↦ a)
  seq := Star.seq
  bind := sorry
