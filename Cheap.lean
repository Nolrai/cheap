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

structure Prefilter (α : Type) : Type where
  big : Set (Set α)
  upwards_closed (p q : Set α) : p ≤ q → big p → big q
  pure_true : big Set.univ
  pure_false : ¬ big ∅

instance : SetLike (Prefilter α) (Set α) where
  coe := Prefilter.big
  coe_injective'
    | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

theorem lift_forall (𝔽 : Prefilter α) : (∀ n, p n) → p ∈ 𝔽 := by
  intros all_p
  have : p = λ _ ↦ True := funext λ n => eq_true (all_p n)
  rw [this]
  apply Prefilter.pure_true

structure Filter (α) extends Prefilter α where
  lift_and (p q : Set α) : big p → big q → big (p ⊓ q)

instance : SetLike (Filter α) (Set α) where
  coe := Prefilter.big ∘ Filter.toPrefilter
  coe_injective'
    | ⟨⟨_, _, _, _⟩, _⟩, ⟨⟨_, _, _, _⟩, _⟩, rfl => by simp

open Filter
open Prefilter

structure Cofilter (α) extends Prefilter α where
  lower_or (p q : Set α) : big (p ⊔ q) → big p ∨ big q

def cofinite_prefilter : Prefilter ℕ where
  big := eventually id
  upwards_closed (p q p_le_q) :=
    λ ⟨n, proof_of_p⟩ ↦ ⟨n, λ m h ↦ by
        simp
        apply p_le_q
        apply proof_of_p _ h
      ⟩
  pure_true := ⟨0, λ m  _=> True.intro⟩
  pure_false
    | ⟨n, p⟩ => p n (le_refl _)

def cofinite_filter : Filter ℕ :=
  {cofinite_prefilter with
    lift_and :=
      λ _p _q ⟨n₀, np⟩ ⟨n₁, nq⟩ =>
        ⟨max n₀ n₁, λ k k_ge =>
          have n₀_le_k : n₀ ≤ k := le_trans (le_max_left _ _) k_ge
          have n₁_le_k : n₁ ≤ k := le_trans (le_max_right _ _) k_ge
          ⟨np k n₀_le_k, nq k n₁_le_k⟩
        ⟩
    }

theorem Or.elim_inr : p ∨ q → ¬ q → p :=
  λ p_or_q not_q ↦ p_or_q.elim id (False.elim ∘ not_q)

theorem Or.elim_inl : p ∨ q → ¬ p → q :=
  λ p_or_q not_p ↦ p_or_q.elim (False.elim ∘ not_p) id

def infinite_cofilter : Cofilter ℕ where
  big x := ∀ n, ∃ m, n ≤ m ∧ m ∈ x
  upwards_closed := _

class UltraFilter (α : Type) extends Filter α, Cofilter α where

theorem UltraFilter.ultra (𝕌 : UltraFilter α) {p} : 𝕌.big p ∨ 𝕌.big (∼ p) := by
  apply lower_or
  apply lift_forall
  intros n
  simp_rw [Sup.sup]
  simp
  classical
  apply em

def principlFilter (s : Set α) (nonempty : s ≠ ∅) : Filter α where
   big x := s ⊆ x
   upwards_closed p q p_le_q p_big := subset_trans p_big p_le_q
   pure_false hyp := nonempty ( Set.subset_empty_iff.mp hyp )
   pure_true := Set.subset_univ _
   lift_and p q p_big q_big := by
    simp at *
    exact ⟨p_big, q_big⟩

def extend_filter :

open Filter

theorem cap_in_ge_filter {f₀ f₁ : Filter α} {p q} : f₀ ⊆ f₁ → p ∈ f₀ → q ∈ f₁ → p ⊓ q ∈ f₁ := by
  intros g₁_filter f₀_le_f₁ p_in_f₀ q_in_f₁
  apply g₁_filter.lift_and p q _ q_in_f₁
  apply f₀_le_f₁
  exact p_in_f₀

instance sUnion_of_chain_of_filters_is_filter  (c : Set (Set (F Prop))) (c_IsChain : IsChain (· ⊆ ·) c) (nonempty: Set.Nonempty c) (all_filters : ∀ f, f ∈ c → Filter f) : Filter (⋃₀ c) where

  upwards_closed := by
    intros p q p_le_q p_in_union
    rw [← Set.mem_def (s := ⋃₀ c), Set.mem_sUnion] at *
    have ⟨t, t_in_c, p_in_t⟩ := p_in_union
    use t
    apply And.intro t_in_c
    have : Filter t := all_filters t t_in_c
    apply this.upwards_closed
    intros n
    apply p_le_q
    apply p_in_t

  pure_true := by
    have ⟨f, f_in_c⟩ := nonempty
    have : Filter f := all_filters f f_in_c
    use f; apply And.intro f_in_c
    apply this.pure_true

  pure_false
    | ⟨f, f_in_c, pure_false_in_f⟩ => by
      have f_is_filter := all_filters f f_in_c
      apply f_is_filter.pure_false
      apply pure_false_in_f

  lift_and
    | p, q, p_in_union, q_in_union => by
      rw [← Set.mem_def (s := ⋃₀ c), Set.mem_sUnion] at *
      have ⟨f₁, f₁_in_c, p_in_f₁⟩ := p_in_union
      have ⟨f₂, f₂_in_c, q_in_f₂⟩ := q_in_union
      cases IsChain.total c_IsChain f₁_in_c f₂_in_c with
      | inl f₁_le_f₂ =>
        use f₂
        apply And.intro (by assumption)
        have q_is_filter := all_filters _ f₂_in_c
        apply cap_in_ge_filter q_is_filter f₁_le_f₂ p_in_f₁ q_in_f₂
      | inr f₂_le_f₁ =>
        use f₁
        apply And.intro (by assumption)
        have q_is_filter := all_filters _ f₁_in_c
        rw [inf_comm]
        apply cap_in_ge_filter q_is_filter f₂_le_f₁ q_in_f₂ p_in_f₁

theorem to_ultraFilter.aux
  (𝔽 : Set (F Prop))
  [Filter 𝔽]
  (c : Set (Set (F Prop))) :
    c ⊆ {f | Filter f} →
    IsChain (· ⊆ ·) c →
    Set.Nonempty c →
    ∃ ub ∈ {f | Filter f}, ∀ (s : Set (F Prop)), s ∈ c → s ⊆ ub := by
  intro c_only_filters c_is_chain c_nonempty
  use (⋃₀ c)
  apply And.intro
  · rw [Set.mem_def, setOf]
    apply sUnion_of_chain_of_filters_is_filter
    · assumption
    · assumption
    · assumption
  · intros s s_in_c
    apply Set.subset_sUnion_of_mem
    assumption

def to_ultraFilter (𝔽) [inst : Filter 𝔽] : Subtype UltraFilter := by
    have p : ∃ u, _ :=
      zorn_subset_nonempty
      {f : Set (F Prop) | Filter f }
      (to_ultraFilter.aux 𝔽)
      𝔽
      (by apply inst)
    have ⟨u, u_is_Filter, 𝔽_sub_u, u_maximal⟩ := Classical.subtype_of_exists p
    use u
    simp [Set.mem_def, setOf] at *
    have : Cofilter u :=
      { lower_or := by
          intros p q u_p_sup_q

      }

def ultraFilter.equiv (𝕌 : {f // UltraFilter f}) (a b ) := ((· = ·) <$> a <*> b)

-- inductive Simple : ∀ {α} [Ring α], F α → Prop where
--   | const : ∀ {α} [Ring α] (c : α), Simple (λ _ ↦ c)
--   | omega : ∀ {α} [Ring α], Simple (λ n ↦ (↑n : α))
--   | add : ∀ {α} [Ring α] (f g : F α), Simple f → Simple g → Simple (λ x ↦ f x + g x)
--   | mul : ∀ {α} [Ring α] (f g : F α), Simple f → Simple g → Simple (λ x ↦ f x * g x)
--   | neg : ∀ {α} [Ring α] (f : F α), Simple f → Simple (λ x ↦ - f x)
--   | pow : ∀ {α} [Ring α] (f : F α) (n : ℕ), Simple f → Simple (λ x ↦ f x ^ n)

-- def Star R [Ring R] := {f : F R // Simple f}

-- notation:50 "★" R => Star R

-- def nice [OrderedRing R] (f : ★ R) := ∀ r : R, □ ((r ≤ · ) <$> f.val) ∨ □ ((· ≤ r) <$> f.val)

-- theorem simple_is_nice [LinearOrderedRing R] [Archimedean R] : ∀ (f : ★ R), nice f
--   | ⟨_, Simple.const c⟩ => by
--     intros x
--     if h : x ≤ c
--       then exact Or.inl ⟨0, λ _ _ => h⟩
--       else
--         exact Or.inr ⟨0, λ _ _ => le_of_not_le h⟩
--   | ⟨ _, Simple.omega ⟩ => by
--     intros x
--     have ⟨n, n_big⟩ := exists_nat_ge x
--     apply Or.inl
--     exists n
--     intros m m_hyp
--     simp_rw [Functor.map, F.map, id]
--     apply le_trans (b := ↑n) n_big

--   | ⟨ _, Simple.pow _ _ _ ⟩ => _
--   | ⟨ _, Simple.neg _ _ ⟩ => _
--   | ⟨ _, Simple.mul _ _ _ _ ⟩ => _
--   | ⟨ _, Simple.add _ _ _ _ ⟩ => _

end Stream
