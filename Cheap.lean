import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Rat.Order
import Mathlib.Data.Nat.Cast.Basic

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

notation:50 " □" => F.eventually
notation:50 " ◇" => F.infinitely_often

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

def delta : F ℚ := λ n ↦ by
  apply @Rat.mk' 1 (n + 1)
  simp
  simp

def infinitesmal [LT α] [Abs α] [Zero α] : F α → Prop := λ s ↦ ∀ a, 0 < a → s.eventually ((· < abs a) ∘ abs)

instance : Abs ℚ := ⟨λ q ↦ if q < 0 then -q else q⟩

def delta_is_infinitesimal : infinitesmal delta := by
  intro a aPos
  have ⟨num, denom, denomPos, h⟩ := a
  rw [Rat.lt_def] at aPos
  simp at aPos
  use denom
  intro m h
  simp [delta, abs]
  rw [← gt_iff_lt]
  rw [if_neg, if_neg]
  rw [gt_iff_lt, Rat.lt_def]
  simp
  apply lt_of_lt_of_le (a := ↑denom) (b := (m + 1 : ℤ ))
  apply lt_of_le_of_lt (b := (m : ℤ))
  rw [@Nat.cast_le ℤ]
  exact h
  simp
  simp
  apply aPos
  · rw [Rat.lt_def]
    simp
  · rw [Rat.lt_def]
    simp
    apply le_of_lt aPos

structure Filter (α : Type u) where
  sets : Set (Set α)
  univ : Set.univ ∈ sets
  superset : ∀ {a b}, a ∈ sets → (∀ n, n ∈ a → n ∈ b) → b ∈ sets
  inter : ∀ {a b}, a ∈ sets → b ∈ sets → a ∩ b ∈ sets

instance : Membership (Set α) (Filter α) where
  mem := λ a s ↦ a ∈ s.sets

def F.equiv (f : Filter ℕ) (α) (s₁ s₂ : F α) : Prop := (λ n ↦ s₁ n = s₂ n) ∈ f

theorem Filter.inter' {α : Type u} (f : Filter α) {a b c : Set α} : 
  a ∈ f → b ∈ f → (∀ n, a n → b n → c n) → c ∈ f := by
  intro aInF bInF h
  apply f.superset (a := a ∩ b)
  apply f.inter aInF bInF
  intro m
  rw [Set.mem_inter_iff]
  intro ⟨h₁, h₂⟩
  apply h m h₁ h₂

theorem F.equiv_iseqv (f : Filter ℕ) {α} : Equivalence (F.equiv f α) where
  refl := by
    intros x
    simp [F.equiv]
    apply f.univ
  symm := by
    intros x y
    simp [F.equiv]
    intro h
    apply f.superset h
    intro n
    simp [Set.mem_def]
    apply symm
  trans := by
    intros x y z xy yz
    simp [F.equiv] at *
    apply f.inter' xy yz
    intros n xyn yzn
    rw [xyn, ← yzn]

universe u

instance F.Setoid (𝔽 : Filter ℕ) (α) : Setoid (F α) where
  r := F.equiv 𝔽 α
  iseqv := F.equiv_iseqv 𝔽

@[reducible]
def Star (𝔽 : Filter ℕ) (α : Type u) := Quotient (F.Setoid 𝔽 α)
  
def Star.mk {𝔽 : Filter ℕ} (α : Type u) : F α → Star 𝔽 α := Quotient.mk _

def Star.ind {𝔽 : Filter ℕ} {α : Type u} {β : Star 𝔽 α → Prop} : (∀ s : F α, β (Star.mk α s)) → ∀ s : Star 𝔽 α, β s := by
  intro h
  intro s
  induction s using Quotient.ind
  apply h

def Star.map (𝔽 : Filter ℕ) {α β} (f : α → β) : Star 𝔽 α → Star 𝔽 β := 
  Quotient.map' (F.map f) $
    by
    intros Fa Fb h
    simp [F.map] at *
    apply 𝔽.superset h
    intros n hn
    simp [Set.mem_def] at *
    rw [hn]

instance : Functor (Star 𝔽) := 
  { map := λ {α β} ↦ Star.map 𝔽 (α := α) (β := β)
  }

instance : Applicative (Star 𝔽) :=
  { pure := λ {α} ↦ Star.mk α ∘ pure
  , seq := λ {α β} ↦ λ sx sy ↦ 
    Quotient.map₂' 
      (λ Fx Fy ↦ Fx <*> Fy)
      (by
        simp [Setoid.r, F.equiv]
        intros Ff₀ Ff₁ hf Fa₀ Fa₁ ha
        apply 𝔽.inter' hf ha
        intros n h₀ h₁
        simp [Seq.seq]
        rw [h₀, h₁]
      )
      sx (sy ())
  }

theorem Star.map_def {α β} (f : α → β) (s : F α) : f <$> (Star.mk (𝔽 := 𝔽) α s) = Star.mk β (F.map f s) := rfl

instance : LawfulFunctor (Star 𝔽) where
  map_const := rfl
  id_map := by
    intro α a
    induction a using Star.ind with
    | _ s => rfl
  comp_map := by
    intro α β γ g h a
    induction a using Star.ind with
    | _ s => rfl

theorem Star.seq_def {α β} (sf : F (α → β)) (sa : F α) : (Star.mk (𝔽 := 𝔽) _ sf) <*> Star.mk _ sa = 
  Star.mk _ (sf <*> sa) := rfl

instance : LawfulApplicative (Star 𝔽) where
  pure_seq := by
    intro α β a b
    induction b using Star.ind with
    | _ s => rfl
  map_pure := by
    intro α β g a
    simp [pure]
    rw [Star.map_def]
    rfl
  seq_pure := by
    intro α β a b
    induction a using Star.ind with
    | _ s => rfl
  seq_assoc := by
    intro α β γ a b c
    induction a using Star.ind with
    | _ s => 
      induction b using Star.ind with
      | _ t => 
        induction c using Star.ind with
        | _ u => rfl
  seqLeft_eq := by
    intro α β a b
    induction a using Star.ind with
    | _ s => rfl
  seqRight_eq := by
    intro α β a b
    induction a using Star.ind with
    | _ s => rfl

instance [Add α] : Add (Star 𝔽 α) where
  add := λ x y ↦ (· + ·) <$> x <*> y

instance [Mul α] : Mul (Star 𝔽 α) where
  mul := λ x y ↦ (· * ·) <$> x <*> y

instance [Neg α] : Neg (Star 𝔽 α) where
  neg := λ x ↦ (- ·) <$> x

instance [Pow α β] : Pow (Star 𝔽 α) (Star 𝔽 β) where
  pow := λ x y ↦ (· ^ ·) <$> x <*> y

theorem Star.add_def [Add α] : ∀ x y : Star 𝔽 α, x + y = (· + ·) <$> x <*> y := by
  intros x y
  simp [HAdd.hAdd, Add.add]

theorem Star.add_def' [Add α] : ∀ x y : F α, 
  Star.mk (𝔽 := 𝔽) α x + Star.mk α y = Star.mk α (λ n ↦ x n + y n):= by
  intros x y
  simp [Star.add_def, Seq.seq, Star.mk]
  have : ∀ z, Quotient.mk'' z = Quotient.mk (F.Setoid 𝔽 α) z := λ _ ↦ rfl
  simp_rw [← this, Quotient.map₂'_mk'', Functor.map, map, Quotient.map'_mk'', F.map, Quotient.map₂'_mk'']
  simp [Quotient.map'_mk'']

theorem Star.mul_def [Mul α] : ∀ x y : Star 𝔽 α, x * y = (· * ·) <$> x <*> y := by
  intros x y
  simp [HMul.hMul, Mul.mul]

theorem Star.mul_def' [Mul α] : ∀ x y : F α, 
  Star.mk (𝔽 := 𝔽) α x * Star.mk α y = Star.mk α (λ n ↦ x n * y n):= by
  intros x y
  simp [Star.mul_def, Seq.seq, Star.mk]
  have : ∀ z, Quotient.mk'' z = Quotient.mk (F.Setoid 𝔽 α) z := λ _ ↦ rfl
  simp_rw [← this, Quotient.map₂'_mk'', Functor.map, map, Quotient.map'_mk'', F.map, Quotient.map₂'_mk'']
  simp [Quotient.map'_mk'']

theorem Star.pow_def [Pow α β] : ∀ x : Star 𝔽 α, ∀ y : Star 𝔽 β, 
  x ^ y = ((λ a b ↦ a ^ b) <$> x <*> y) := by
  intros x y
  simp [HPow.hPow, Pow.pow]

theorem Star.pow_def' [Pow α α] : ∀ x : F α, ∀ y : F α, 
  Star.mk (𝔽 := 𝔽) α x ^ Star.mk (𝔽 := 𝔽) α y = Star.mk α (λ m ↦ x m ^ y m) := by
  intros x y
  simp [Star.pow_def, Seq.seq, Star.mk]
  have : ∀ z, Quotient.mk'' z = Quotient.mk (F.Setoid 𝔽 α) z := λ _ ↦ rfl
  simp_rw [← this, Quotient.map₂'_mk'', Functor.map, map, Quotient.map'_mk'', F.map, Quotient.map₂'_mk'']
  simp [Quotient.map'_mk'']
  
theorem Star.neg_def [Neg α] : ∀ x : Star 𝔽 α, -x = (- ·) <$> x := by
  intros x
  simp [Neg.neg]

theorem Star.neg_def' [Neg α] : ∀ x : F α, -(Star.mk (𝔽 := 𝔽) α x) = Star.mk α (λ n ↦ -x n) := by
  intros x
  simp [Star.neg_def, Star.mk]
  have : ∀ z, Quotient.mk'' z = Quotient.mk (F.Setoid 𝔽 α) z := λ _ ↦ rfl
  simp_rw [← this, Functor.map, map, Quotient.map'_mk'', F.map]

instance [One α] : One (Star 𝔽 α) where
  one := Star.mk α (λ _ ↦ 1)

instance [Zero α] : Zero (Star 𝔽 α) where
  zero := Star.mk α (λ _ ↦ 0)

theorem Star.one_def [One α] : (1 : Star 𝔽 α) = Star.mk α (λ _ ↦ 1) := rfl
theorem Star.zero_def [Zero α] : (0 : Star 𝔽 α) = Star.mk α (λ _ ↦ 0) := rfl

inductive RingExp : ℕ → Type where
  | zero : ∀ {n}, RingExp n
  | one  : ∀ {n}, RingExp n
  | var  : ∀ {n}, Fin n → RingExp n
  | add  : ∀ {n}, RingExp n → RingExp n → RingExp n
  | mul  : ∀ {n}, RingExp n → RingExp n → RingExp n
  | neg  : ∀ {n}, RingExp n → RingExp n
  | pow  : ∀ {n}, RingExp n → RingExp n → RingExp n

section RingExp

instance {n} : Add (RingExp n)  where
  add := RingExp.add

instance {n} : Mul (RingExp n)  where
  mul := RingExp.mul

instance {n} : Neg (RingExp n) where
  neg := RingExp.neg

instance {n} : Pow (RingExp n) (RingExp n) where
  pow := RingExp.pow

structure RingEq (n : ℕ) where
  lhs : RingExp n
  rhs : RingExp n

class RawRing (α : Type u) extends Add α, Mul α, Neg α, One α, Zero α, Pow α α where

instance [Add α] [Mul α] [Neg α] [One α] [Zero α] [Pow α α] : RawRing α where

def RingExp.eval {n : ℕ} (vars : Fin n → α) [RawRing α] : RingExp n → α
  | zero => 0
  | one => 1
  | var i => vars i
  | add x y => x.eval vars + y.eval vars
  | mul x y => x.eval vars * y.eval vars
  | neg x => - x.eval vars
  | pow x y => x.eval vars ^ y.eval vars 

def RingEq.eval {n : ℕ} (vars : Fin n → α) [RawRing α] : RingEq n → Prop
  | ⟨lhs, rhs⟩ => lhs.eval vars = rhs.eval vars

open RingExp

def Fin.toPair : ∀ {n : ℕ}, (Fin (n + 1) → α) → (α × (Fin n → α))
  | 0, f => ⟨f 0, Fin.elim0⟩
  | _ +1, f => ⟨f 0, λ i => f (i.succ)⟩

def Fin.fromPair : ∀ {n : ℕ}, α → (Fin n → α) → (Fin (n + 1) → α)
  | 0, a, _, _ => a
  | n +1, a, f, i => match i with
    | ⟨0, _⟩ => a
    | ⟨j+1, succ_j_lt_succ_succ_n⟩ =>
      have h : j < n + 1 := by simp at *; assumption 
      f ⟨j, h⟩

def Applicative.pull [Applicative A] (a : Fin n → A α) : A (Fin n → α) := by
  induction n with
  | zero => exact pure (λ f ↦ Fin.elim0 f)
  | succ m m_ih => 
    let rest : A (Fin m → α) := m_ih (λ i => a i.succ)
    let first : A α := a 0
    exact Fin.fromPair <$> first <*> rest 

theorem Star.map_mk : ∀ (f : α → β) (x : ℕ → α), 
  f <$> Star.mk (𝔽 := 𝔽) α x = Star.mk β (λ n ↦ f (x n)) := by
  intros f x
  simp [Star.mk, Functor.map, map, F.map]
  have mk''_at_α : ∀ z, Quotient.mk'' z = Quotient.mk (F.Setoid 𝔽 α) z := λ _ ↦ rfl
  have mk''_at_β : ∀ z, Quotient.mk'' z = Quotient.mk (F.Setoid 𝔽 β) z := λ _ ↦ rfl
  simp_rw [← mk''_at_α, ← mk''_at_β, Functor.map, map, Quotient.map'_mk'']
  
theorem RingExp.evalStar [RawRing α] : 
  ∀ {n} (r : RingExp n) 
  (vars : Fin n → Star 𝔽 α), 
  r.eval vars = r.eval <$> Applicative.pull vars
| 0, zero, vars => rfl
| 0, one, vars => rfl
| 0, var i, vars => i.elim0
| 0, add x y, vars => by
  simp [RingExp.eval, Star.map_def]
  rw [RingExp.evalStar, RingExp.evalStar]
  rfl
| 0, mul x y, vars => by
  simp [RingExp.eval, Star.map_def]
  rw [RingExp.evalStar, RingExp.evalStar]
  rfl
| 0, neg x, vars => by
  simp [RingExp.eval, Star.map_def]
  rw [RingExp.evalStar]
  rfl
| 0, pow x y, vars => by
  simp [RingExp.eval, Star.map_def]
  rw [RingExp.evalStar, RingExp.evalStar]
  rfl

| n+1, zero, vars => rfl
| n+1, one, vars => rfl
| n+1, var i, vars => by
  simp [RingExp.eval, Star.map_def, Applicative.pull]
  simp [RingExp.evalStar]
| n+1, add x y, vars => by
  simp [RingExp.eval, Functor.map, map, Applicative.pull]
  rw [Star.zero_def, Star.one_def]
  simp [RingExp.evalStar]
| n+1, mul x y, vars => by
  simp [RingExp.eval, Functor.map, map, Applicative.pull]
  rw [Star.zero_def, Star.one_def]
  simp [RingExp.evalStar]
| n+1, neg x, vars => by
  simp [RingExp.eval, Functor.map, map, Applicative.pull]
  rw [Star.zero_def, Star.one_def]
  simp [RingExp.evalStar]
| n+1, pow x y, vars => by
  simp [RingExp.eval, Functor.map, map, Applicative.pull]
  rw [Star.zero_def, Star.one_def]
  simp [RingExp.evalStar]


theorem Star.transfer [Add α] [Mul α] [Neg α] [One α] [Zero α] [Pow α α] 
  : ∀ {n : ℕ} (r : RingEq n)
  , (∀ vars : Fin n → α, r.eval vars) 
  → (∀ vars : Fin n → Star 𝔽 α, r.eval vars)
| n, ⟨lhs, rhs⟩, h, vars => by
  simp [RingEq.eval] at *
  induction lhs with 
  | zero => 
    simp [eval] at *
    rw [Star.zero_def]
    


  