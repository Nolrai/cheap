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

def F (α : Sort u) : Sort (imax 1 u) := ℕ → α

namespace F

def head {α : Sort u} (s : F α) : α := s 0
def tail {α : Sort u} (s : F α) : F α := λ n ↦ s (n + 1)
def drop {α : Sort u} (n : ℕ) (s : F α) : F α := λ m ↦ s (m + n)
def nth {α : Sort u} (n : ℕ) (s : F α) : α := s n
def map {α β : Sort u} (f : α → β) (s : F α) : F β := λ n ↦ f (s n)
def zip {α β γ : Sort u} (f : α → β → γ) (s₁ : F α) (s₂ : F β) : F γ := λ n ↦ f (s₁ n) (s₂ n)
def iterate {α : Sort u} (f : α → α) (a : α) : F α := λ n ↦ n.recOn a (λ _ ih ↦ f ih)
def eventually {α : Sort u} (p : α → Prop) (s : F α) : Prop := ∃ n, ∀ m, n ≤ m → p (s m)
def infinitely_often {α : Sort u} (p : α → Prop) (s : F α) : Prop := ∀ n, ∃ m, n ≤ m ∧ p (s m)

theorem markov {P : ℕ → Prop} (hyp : ¬ (∀ n, ¬ P n)) : ∃ n, P n := by
  classical!
  apply by_contradiction
  intros hyp₀
  apply hyp
  intros n
  by_cases h : ¬ P n
  · exact h
  · exfalso
    apply hyp₀
    use n
    apply by_contradiction h

instance : Functor F := { map := @F.map, mapConst := λ {α _} (a : α) _ _ ↦ a }

instance : Applicative F :=
  { pure := λ a _ ↦ a
  , seq := λ f g ↦ λ n ↦ f n (g () n)
  }

instance : Monad F :=
  { bind := λ f g ↦ λ n ↦ g (f n) n
  }

instance : LawfulFunctor F :=
  { id_map := by {intros; funext; rfl}
  , comp_map := by {intros; funext; rfl}
  , map_const := by {intros; funext; rfl}
  }

instance : LawfulApplicative F :=
  { pure_seq := by {intros; funext; rfl}
  , seq_pure := by {intros; funext; rfl}
  , seq_assoc := by {intros; funext; rfl}
  , map_pure := by {intros; funext; rfl}
  , seqLeft_eq := by {intros; funext; rfl}
  , seqRight_eq := by {intros; funext; rfl}
  }

instance : LawfulMonad F :=
  { pure_bind := by {intros; funext; rfl}
  , bind_pure_comp := by {intros; funext; rfl}
  , bind_assoc := by {intros; funext; rfl}
  , bind_map := by {intros; funext; rfl}
  }

notation:60 "∼" p => (¬ ·) ∘ p

def preorderF [Preorder α] : Preorder (F α) where
  le := λ x y => eventually id (λ n => x n ≤ y n)
  le_refl := λ x => ⟨0, λ m _ => le_refl _⟩
  le_trans := λ x y z ⟨n_xy, xy_h⟩ ⟨n_yz, yz_h⟩ =>
    let m := max n_xy n_yz
    ⟨m, λ k m_le_k ↦ by
      simp
      apply le_trans (xy_h _ _) (yz_h _ _)
      · apply le_trans (le_max_left _ _) m_le_k
      · apply le_trans (le_max_right _ _) m_le_k
    ⟩

instance lattice {α : Type} [Lattice α] : Lattice (F α) where
  inf (p q : F α) := λ n => p n ⊓ q n
  sup (p q : F α) := λ n => p n ⊔ q n
  le (p q : F α) := ∀ n, p n ≤ q n
  le_refl (p : F α) := λ n ↦ le_refl (p n)
  le_trans (p q r: F α) (pq qr) := λ n ↦ le_trans (pq n) (qr n)
  le_antisymm (p q : F α) (pq qp) := by
    funext n
    apply le_antisymm (pq n) (qp n)
  le_sup_left (p q : F α) := λ n ↦ le_sup_left
  le_sup_right (p q : F α) := λ n ↦ le_sup_right
  sup_le (p q r : F α) := λ pr qr => λ n ↦ sup_le (pr n) (qr n)
  inf_le_left (p q : F α) := λ n ↦ inf_le_left
  inf_le_right (p q : F α) := λ n ↦ inf_le_right
  le_inf (p q r : F α) := λ pr qr => λ n ↦ le_inf (pr n) (qr n)

def std : F α → Prop := λ x => ∃ y, x = pure y

def limited {α : Type} [Preorder (F α)] (x : F α) : Prop := ∃ a b : F α, std a ∧ std b ∧ a ≤ x ∧ x ≤ b

end F

axiom markov (p : Set ℕ) [DecidablePred p] : Decidable (∃ n, p n)

noncomputable
instance
  markov_instance (p : Set ℕ) [DecidablePred p]
  : Decidable (∃ n, p n)
  := markov p

theorem markov_or (p : Set ℕ) [DecidablePred p] : (∀ n, ¬ p n) ∨ (∃ n, p n) :=
  if h : ∃ n, p n
    then Or.inr h
    else Or.inl λ n p_n ↦ h ⟨n, p_n⟩

noncomputable
instance markov_forall (p : Set ℕ) [DecidablePred p] :
  Decidable (∀ n, p n) :=
  if h : ∃ n, ¬ p n
    then isFalse λ all_p ↦
      have ⟨n, not_p_n⟩ := h
      not_p_n (all_p n)
    else isTrue λ n ↦
      if h_n : p n
      then h_n
      else (h ⟨n, h_n⟩).elim

open Filter

prefix:100 "~" => ((¬ ·) ∘ ·)

def extend (𝔽 : Filter ℕ) [DecidablePred (· ∈ 𝔽)] (p : Set ℕ) [DecidablePred p] :=
  have g :=
    if (p ∈ 𝔽) ∨ (~ p ∈ 𝔽) then 𝔽
    else if ~ ~ p ∈ 𝔽 then 𝓟 p
    else 𝓟 ((¬ ·) ∘ p)
  𝔽 ⊔ g

theorem extend_monotonic (𝔽 : Filter ℕ) [DecidablePred (· ∈ 𝔽)] (p : Set ℕ) [DecidablePred p]
  : 𝔽 ≤ (extend 𝔽 p) := by
    rw [extend]
    simp
