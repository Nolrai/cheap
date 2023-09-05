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

open Set

structure SetIdeal (α : Type u) where
  small : (Set α) → Prop 
  nonempty : ∃ s, small s
  lower : ∀ {s t}, small s → t ⊆ s → small t
  union : ∀ {s t}, small s → small t → small (s ∪ t)

structure ProperIdeal (α : Type u) extends SetIdeal α where
  proper : ∀ {s}, small s → ∃ x, x ∉ s 

theorem proper' (I : ProperIdeal α) : ¬ I.small univ :=
  λ h => let ⟨x, hx⟩ := I.proper h
         hx (Set.mem_univ x)

structure FreeIdeal (α : Type u) extends ProperIdeal α where
  free : ∀ {x} {s}, small s → x ∉ s → small (insert x s)

structure PrimeIdeal (α : Type u) extends ProperIdeal α where
  prime : ∀ {s t}, small (s ∩ t) → small s ∨ small t

structure Ultraideal (α : Type u) extends PrimeIdeal α where
  ultra : ∀ p, small p ∨ small (pᶜ) 

def isErr {α β} : α ⊕' β → Bool
  | .inl _ => true
  | .inr _ => false 

@[reducible]
def box (I : ProperIdeal ℕ) (α : Sort u) := {μ : F (⊤ ⊕' α) // I.small (λ n ↦ isErr (μ n) : ℕ → Prop)}

def box.head {I : ProperIdeal ℕ} {α : Sort u} (s : box I α) : Nonempty α := by
  let ⟨μ, hμ⟩ := s
  let ⟨n, hn⟩ := I.proper hμ
  simp_rw [Set.mem_def] at *
  clear hμ s
  revert hn
  cases μ n with
  | inl _ => intro; contradiction
  | inr a => intro; exact ⟨a⟩

