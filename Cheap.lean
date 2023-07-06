import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Basic

namespace Stream

def F (α : Type u) : Type u := ℕ → α

namespace F

def head {α : Type u} (s : F α) : α := s 0
def tail {α : Type u} (s : F α) : F α := λ n ↦ s (n + 1)
def drop {α : Type u} (n : ℕ) (s : F α) : F α := λ m ↦ s (m + n)
def nth {α : Type u} (n : ℕ) (s : F α) : α := s n
def map {α β : Type u} (f : α → β) (s : F α) : F β := λ n ↦ f (s n)
def zip {α β γ : Type u} (f : α → β → γ) (s₁ : F α) (s₂ : F β) : F γ := λ n ↦ f (s₁ n) (s₂ n)
def iterate {α : Type u} (f : α → α) (a : α) : F α := λ n ↦ n.recOn a (λ _ ih ↦ f ih)
def eventually {α : Type u} (p : α → Prop) (s : F α) : Prop := ∃ n, ∀ m, n ≤ m → p (s m)
def infinitely_often {α : Type u} (p : α → Prop) (s : F α) : Prop := ∀ n, ∃ m, n ≤ m ∧ p (s m)

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

def forall_to_eventually (p : α → Prop) (s : F α) : (∀ n, p (s n)) → F.eventually p s := 
  λ h ↦ ⟨0, λ _ _ ↦ h _⟩

def eventually_to_infinately_often (p : α → Prop) (s : F α) : F.eventually p s → F.infinitely_often p s :=
  λ ⟨n, h⟩ m ↦ by
    use max n m
    constructor
    · apply Nat.le_max_right n m
    · apply h
      apply Nat.le_max_left n m

def infinately_often_to_thereExists (p : α → Prop) (s : F α) : F.infinitely_often p s → ∃ n, p (s n) :=
  λ h ↦ by 
    have ⟨m, h⟩ := h 0
    use m
    apply h.right


notation:50 " □" => F.eventually

def unlimited_unit : F ℕ := λ n ↦ n + 1

def is_std : F α → Prop := λ s ↦ ∃ n, ∀ m, n ≤ m → s m = s n

def unlimited (s : F α) [LE α] [Abs α] : Prop := ∀ a : α, s.eventually (abs a ≤ ·)

instance : Abs Nat := ⟨id⟩

theorem unlimited_unit_is_unlimited : unlimited unlimited_unit := by
  intro a
  use a
  intro m h
  simp [unlimited_unit, abs]
  apply le_trans h
  apply Nat.le_succ

def delta : F ℚ := λ n ↦ 1 / (n + (1 : ℚ))

def infinitesmal [LT α] [Abs α] : F α → Prop := λ s ↦ ∀ a, s.eventually ((· < abs a) ∘ abs)

instance : Abs ℚ := ⟨λ q ↦ if q < 0 then -q else q⟩

def delta_is_infinitesimal : infinitesmal delta := by
  intro a
  have ⟨num, denom, denomPos, h⟩ := a
  use 0
  intro m h
  simp [delta, abs]

  

