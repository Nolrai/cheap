import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Rat.Order
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.Order.Archimedean
import std

namespace Stream

#check OptionT

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

notation:50 " □""(" f ")" => eventually id f
notation:50 " ◇""(" f ")" => infinitely_often id f

@[simp]
theorem eventually_true : □ (λ _ => True) := by
  use 0
  intro m _
  simp

end F

theorem diw_of_Box {p : F Prop} : □(p) → ◇(p)
  | ⟨m, h'⟩, n =>  ⟨max m n, le_max_right _ _, h' _ (le_max_left _ _)⟩

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
  le := λ x y => □ (λ n => x n ≤ y n)
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

class Prefilter (𝔽 : F Prop → Prop) where
  upwards_closed (p q : F Prop) : (∀ n, p n → q n) → 𝔽 p → 𝔽 q
  pure_true : 𝔽 (pure True)
  pure_false : ¬ 𝔽 (pure False)

theorem lift_forall [Prefilter 𝔽] : (∀ n, p n) → (𝔽 p) := by
  intros all_p
  have : p = λ _ ↦ True := funext λ n => eq_true (all_p n)
  rw [this]
  apply Prefilter.pure_true

class Filter (𝔽 : F Prop → Prop) extends Prefilter 𝔽 where
  lift_and (p q : F Prop) : 𝔽 p → 𝔽 q → 𝔽 (p ⊓ q)

class Cofilter (𝔽 : F Prop → Prop) extends Prefilter 𝔽 where
  lower_or (p q : F Prop) : 𝔽 (p ⊔ q) → 𝔽 p ∨ 𝔽 q 

instance : Filter (□ ( · ) ) where
  upwards_closed (p q p_le_q) :=
    λ ⟨n, proof_of_p⟩ ↦ ⟨n, λ m h ↦ by 
        simp
        apply p_le_q
        apply proof_of_p _ h
      ⟩
  pure_true := F.eventually_true
  pure_false := λ ⟨n, h⟩ => h n (le_refl _)
  lift_and (p q : F Prop) :=
    λ ⟨pn, p_proof⟩ ⟨qn, q_proof⟩ ↦ 
      let k := max pn qn
      ⟨k, λ m m_big ↦ 
        have np_le_m : pn ≤ m := le_trans (le_max_left _ _) m_big
        have nq_le_m : qn ≤ m := le_trans (le_max_right _ _) m_big
        ⟨p_proof m np_le_m, q_proof m nq_le_m⟩
      ⟩

theorem Or.elim_inr : p ∨ q → ¬ q → p :=
  λ p_or_q not_q ↦ p_or_q.elim id (False.elim ∘ not_q)

theorem Or.elim_inl : p ∨ q → ¬ p → q :=
  λ p_or_q not_p ↦ p_or_q.elim (False.elim ∘ not_p) id  

instance : Cofilter (◇ (·)) where
  upwards_closed (p q : F Prop) p_le_q := 
    λ diw_p n ↦ 
      have ⟨m, m_big, p_m⟩ := diw_p n
      ⟨m, m_big, p_le_q _ p_m⟩

  pure_true := λ n => ⟨n, le_refl n, by simp [pure]⟩
  pure_false := λ h => 
    have ⟨m, _, h⟩ := h 0
    h
  lower_or (p q) 𝔽_p_or_q := by
    classical!
    by_cases h : □ (∼ p)
    · have ⟨n₀, h⟩ := h
      simp at *
      right
      intros n₁
      have ⟨n₂, n₂_big, p_or_q⟩ := 𝔽_p_or_q (max n₀ n₁)
      use n₂
      constructor
      · apply le_trans _ n₂_big
        apply le_max_right
      · simp
        simp_rw [id, Sup.sup] at p_or_q
        apply Or.elim_inl p_or_q
        apply h
        simp [] at n₂_big
        exact n₂_big.1
    · left
      intros n
      simp at *
      apply markov
      intros hyp
      apply h
      use n
      simp
      intros m m_big p_m
      apply hyp m ⟨m_big, p_m⟩

class UltraFilter (𝔽 : F Prop → Prop) extends Filter 𝔽, Cofilter 𝔽

theorem UltraFilter.ultra [UltraFilter (𝔽 : F Prop → Prop)] {p } : 𝔽 p ∨ 𝔽 (∼ p) := by
  apply lower_or
  apply lift_forall
  intros n
  simp_rw [Sup.sup]
  simp
  classical
  apply em



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
