import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Rat.Order
import Mathlib.Data.Nat.Cast.Basic
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

def RingExp := ∀ α, [Ring α] → α → α

