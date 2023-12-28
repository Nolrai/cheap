import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Rat.Order
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.Order.Archimedean
import Mathlib.Init.Set
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Cofinite
import Mathlib.Order.Monotone.Basic
import std
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Eval
import Mathlib.Data.Polynomial.Degree.Definitions
import Mathlib.Data.Finmap
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Fin

open Filter
open Frequently

section

variable [LinearOrderedSemiring α] [LinearOrderedSemiring β] (f : α → β)

def Oscillating : Prop := (∃ᶠ n in atTop, f n > 0) ∧ (∃ᶠ n in atTop, f n < 0)

theorem Oscillating.getPos {f : α → β} (p : Oscillating f) : ∀ n, ∃ x, n < x ∧ 0 < f x :=
  frequently_atTop'.mp p.1

theorem Oscillating.getNeg {f : α → β} (p : Oscillating f) : ∀ n, ∃ x, n < x ∧ f x < 0 :=
  frequently_atTop'.mp p.2


def isZigZag : List α → Bool
  | [] => true
  | [x] => f x < 0 ∨ 0 < f x
  | (x :: y :: xs ) =>
    f x * f y < 0 ∧ y < x ∧ isZigZag (y :: xs)

@[simp]
theorem isZigZag.nil : ↑(isZigZag f []) := rfl
@[simp]
theorem isZigZag.singleton : isZigZag f [x] = (f x < 0 ∨ 0 < f x) := by
  rw [isZigZag]
  apply decide_eq_true_eq
@[simp]
theorem isZigZag.reduce : isZigZag f (x::y::xs) = (f x * f y < 0 ∧ y < x && isZigZag f (y :: xs)) := by
  simp [isZigZag, decide_eq_true_eq, And.comm]

def isZigZag_pos_or_neg
  : ∀ {l : List α} {x : α}, isZigZag f (x :: l) → f x < 0 ∨ 0 < f x
  | [], x => by
    rw [isZigZag, decide_eq_true_eq]
    apply id
  | (x :: xs), y => by
    have tri := lt_trichotomy (f y) 0
    rw [or_comm, or_assoc] at tri
    rw [isZigZag, decide_eq_true_eq]
    intros h
    have ⟨fy_fx_neg, _, _⟩ := h; clear h
    match tri with
    | Or.inr tri => exact Or.comm.mp tri
    | Or.inl tri => simp [tri] at fy_fx_neg

theorem oscillating_have_arbitrary_zig_zags
  (isOsc : Oscillating f) : ∀ n, ∃ l, l.length = n ∧ isZigZag f l := by
  intros n
  cases n
  case zero => exists []
  case succ n =>
    induction n
    case zero =>
      have ⟨x, x_big, fx_pos⟩ := isOsc.getPos 0
      use [x]
      simp
      apply ne_of_gt fx_pos
    case succ n n_ih =>
      have ⟨l, l_length, l_zigZag⟩ := n_ih
      match l with
      | [] => simp at l_length
      | (x :: xs) =>
        have isPosOrNeg := isZigZag_pos_or_neg f l_zigZag
        cases isPosOrNeg with
        | inl fx_neg =>
          have ⟨y, y_big, fy_pos⟩ := isOsc.getPos x
          use (y :: x :: xs)
          simp at *
          have : f y * f x < 0 := mul_neg_of_pos_of_neg fy_pos fx_neg
          tauto
        | inr fx_pos =>
          have ⟨y, y_big, fy_neg⟩ := isOsc.getNeg x
          use (y :: x :: xs)
          simp at *
          have : f y * f x < 0 := mul_neg_of_neg_of_pos fy_neg fx_pos
          tauto

end

section

prefix:100 " &" => (Σ _, ·)

def WithBot.succ (n : WithBot ℕ) : ℕ := n.recBotCoe (C := λ _ ↦ ℕ) 0 Nat.succ

def lastIs (p : α → Prop) : ∀ {n}, (Fin n → α) → Prop
  | 0, _ => True
  | n+1, f => p (f n)

section

variable {f : Fin 0 → α}

@[simp]
theorem lastIs.zero : lastIs p f := True.intro

@[simp]
theorem lastIs.zero_iff : lastIs p f ↔ True := refl _

end

section

variable {n} {f : Fin (n + 1) → α}

@[simp]
theorem lastIs.succ (h : p (f n)) : lastIs p f := h

@[simp]
theorem lastIs.from_succ (h : lastIs p f) : p (f n) := h

@[simp]
theorem lastIs.succ_iff : lastIs p f ↔ p (f n) := refl _

end

instance [DecidablePred p] : ∀ {n}, DecidablePred (lastIs p (n := n))
  | 0, _ => isTrue lastIs.zero
  | (n+1), f =>
    if h : p (f n)
    then isTrue (lastIs.succ h)
    else isFalse λ hyp ↦ h hyp

structure Polynomial' (R : Type*) [AddMonoid R] where
  degree' : ℕ
  coeff' : Fin degree' → R
  ofDegree : lastIs (· ≠ 0 : R → Prop) toCoef

scoped[Polynomial'] notation:9000 R "[Z]" => Polynomial' R

open Polynomial'

def Polynomial'.degree [AddMonoid R] (p : R[Z]) : WithBot ℕ :=
  match p.degree' with
  | 0 => ⊥
  | (n+1) => ↑n

section trim_and_untrim

variable [Zero R] [DecidablePred (· ≠ (0 : R))]

-- remove trailing zeros
def trim :
  ∀ {n}, (Fin n → R) → Σ m, Fin m → R
  | 0, f => ⟨0, f⟩
  | (n+1), f =>
    if lastIs (· ≠ 0) f
    then ⟨n+1, f⟩
    else trim (n := n) (λ i ↦ f ↑i)

@[simp]
theorem trim.zero (f : Fin 0 → R) : trim f = ⟨0, f⟩ := rfl

@[simp]
theorem trim.succ_case_nonzero (f : Fin (n+1) → R) : f n ≠ 0 → trim f = ⟨n+1, f⟩ := by
  intros h
  rw [trim]
  split
  · rfl
  case inr h' =>
    exfalso
    apply h

@[simp]
theorem trim.succ_case_zero (f : Fin (n+1) → R) : f n = 0 → trim f = trim (n := n) (λ i ↦ f ↑i)

variable {n} (f : Fin n → R)

def trim.size_le [DecidablePred (· ≠ (0 : R))] : (trim f).1 ≤ n := by
  induction n
  case zero => simp_rw [trim]
  case succ n n_ih =>
    rw [trim]
    by_cases lastIs (· ≠ 0) f
    · simp_rw [if_pos h]; rfl
    · simp_rw [if_neg h]
      apply le_trans (n_ih _) (Nat.le_succ n)

def trim.isTopNonzero [DecidablePred (· ≠ (0 : R))] : lastIs (· ≠ 0) (trim f).2 := by
  induction n
  case zero => simp [trim, lastIs]

-- if its past the end just return zero
def untrim (i : ℕ) : R :=
  if h : i < n
  then f ⟨i, h⟩
  else 0

def untrim' (k : ℕ) : Fin k → R :=
  λ ⟨i, _⟩ => untrim f i

abbrev under_untrim (a : Fin n → R) (b : Fin m → R) := untrim a = untrim b

def untrim_setoid : Setoid (Σ n, Fin n → R) where
  r a b := under_untrim a.2 b.2
  iseqv :=
    { refl := λ x ↦ rfl
    , symm := λ xy => xy.symm
    , trans := λ xy yz => by rw [under_untrim, xy, yz]
    }

def Finsup' := Quotient (untrim_setoid (R := R))

def Markovs : Prop := ∀ (f : ℕ → Bool), ∃ i, f i = false ∨ ∀ i, f i = true

theorem Polynomial'_equiv_untrim_quotient (m : Markovs) [AddMonoid R] : R[Z] ≃ Finsup' (R := R) where


end trim_and_untrim

def Polynomial'.coeff [AddMonoid R] (p : R[Z]) : ℕ → R :=
  untrim p.coeff'

open BigOperators

def Polynomial'.sumF [AddMonoid R] [AddCommMonoid R'] (f : R → ℕ → R') (p : R[Z]) : R' :=
  ∑ i, f (p.coeff' i) ↑i

def Polynomial'.eval [Semiring R] (p : R[Z]) (x : R) : R := p.sumF (λ c power ↦ c * x ^ power)

def Polynomial'.add [AddMonoid R] (a b : R[Z]) : R[Z] :=
  let c' : Fin (max a.degree' b.degree') → R := λ i ↦ a.coeff i + b.coeff i
