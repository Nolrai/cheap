import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Rat.Order
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.List.Basic
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

notation:10 " □""(" f ")" => eventually id f

@[simp]
theorem eventually_true : □ (λ _ => True) := by
  use 0
  intro m _
  simp

end F

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

inductive Simple : ∀ {α} [Ring α], F α → Prop where
  | const : ∀ {α} [Ring α] (c : α), Simple (λ _ ↦ c)
  | omega : ∀ {α} [Ring α], Simple (λ n ↦ (↑n : α))
  | add : ∀ {α} [Ring α] (f g : F α), Simple f → Simple g → Simple (λ x ↦ f x + g x)
  | mul : ∀ {α} [Ring α] (f g : F α), Simple f → Simple g → Simple (λ x ↦ f x * g x)
  | neg : ∀ {α} [Ring α] (f : F α), Simple f → Simple (λ x ↦ - f x)
  | pow : ∀ {α} [Ring α] (f : F α) (n : ℕ), Simple f → Simple (λ x ↦ f x ^ n)

def NStar := {f : F ℤ // Simple f}

open Int

@[simp]
theorem Int.sign_square_eq_one : ∀ (z : ℤ), z ≠ 0 → sign (z * z) = 1
  | 0 => by simp
  | Nat.succ n => by simp
  | Int.negSucc n => by simp

theorem Int.sign_pow_even_nat : ∀ (n : ℕ) (z : ℤ), z ≠ 0 → sign (z ^ (2 * n)) = 1
  | 0, 0 => by simp
  | 0, z => by simp 
  | n+1, z => by
    intro z_ne_zero
    rw [left_distrib, pow_succ, pow_succ, ← mul_assoc, sign_mul]
    rw [Int.sign_square_eq_one z z_ne_zero, Int.sign_pow_even_nat n z z_ne_zero]
    simp

theorem NStar_eventually_single_signed : ∀ f : NStar,  □ (λ n => sign (f.val n) = sign (f.val (n+1))) 
  | ⟨_, Simple.const c⟩ => by simp
  | ⟨_, Simple.omega⟩ => by 
    simp
    use 1
    intro m m_big
    apply Int.sign_eq_one_of_pos
    simp
    apply lt_of_lt_of_le zero_lt_one m_big
  | ⟨_, Simple.add f g hf hg⟩ => by
    have ⟨n_f, hf'⟩ := NStar_eventually_single_signed ⟨f, hf⟩
    have ⟨n_g, hg'⟩ := NStar_eventually_single_signed ⟨g, hg⟩
    simp [F.eventually] at *
    use max n_f n_g
    intros m m_big
    rw [sign_add_eq_of_sign_eq]

  | ⟨_, Simple.mul f g hf hg⟩ => by
    have ⟨n_f, hf'⟩ := NStar_eventually_single_signed ⟨f, hf⟩
    have ⟨n_g, hg'⟩ := NStar_eventually_single_signed ⟨g, hg⟩ 
    simp [F.eventually] at *
    use max n_f n_g
    intro m m_big
    rw [hf', hg']
    · apply le_trans (b := max n_f n_g) _ m_big
      apply le_max_right
    · apply le_trans (b := max n_f n_g) _ m_big
      apply le_max_left
  | ⟨_, Simple.neg f hf⟩ => by
    have ⟨n_f, hf'⟩ := NStar_eventually_single_signed ⟨f, hf⟩
    simp [F.eventually] at *
    use n_f
  | ⟨_, Simple.pow f n hf⟩ => by
    have ⟨n_f, hf'⟩ := NStar_eventually_single_signed ⟨f, hf⟩
    simp [F.eventually] at *
    simp_rw [Int.sign_pow_nat]
    induction n with
      | zero => simp
      | succ n ih => 
        intro m m_big
        simp [pow_succ, hf', ih m m_big]

end Stream
