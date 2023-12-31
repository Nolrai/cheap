import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Rat.Order
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Interval
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.Order.Archimedean
import Mathlib.Init.Set
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Cofinite
import Mathlib.Order.Monotone.Basic
import std
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Basic

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

section untrim

variable {R : Type u} [Zero R]

def untrim {R : Type u} [Zero R] (f : Fin n → R) : ℕ → R :=
  λ i => if h : i < n then f ⟨i, h⟩ else 0

@[simp]
theorem untrim_zero {i : ℕ} (h : ¬ i < n) (f : Fin n → R) : untrim f i = 0 := by
  rw [untrim, dif_neg h]

@[simp]
theorem untrim_id {i : ℕ} (h : i < n) {f : Fin n → R} : untrim f i = f ⟨i, h⟩ := by
  simp [untrim, dif_pos h]

@[simp]
theorem untrim_comp (f : Fin n → R) (g : R → R') [Zero R'] (g_zero: g 0 = 0) : untrim (g ∘ f) = g ∘ untrim f := by
  funext i
  by_cases i < n
  · simp [untrim_id h]
  · simp [untrim_zero h, g_zero]

def untrim_setoid : Setoid (Σ n, Fin n → R) where
  r a b := untrim a.2 = untrim b.2
  iseqv := {
    refl := λ a ↦ rfl
    symm := λ ab ↦ ab.symm
    trans := λ ab bc ↦ by rw [ab, bc]
  }

end untrim

def Finsuppℕ (R : Type u) [Zero R] : Type u := Quotient (untrim_setoid (R := R))

def Segment.map {α β : Type u} (f : α → β ) : (Σ n, Fin n → α) → Σ n, Fin n → β
  | ⟨n, v⟩ => ⟨n, f ∘ v⟩

variable (R) [Zero R]

def Finsuppℕ.map {R R'} [Zero R] [Zero R'] (f : R → R') (s : Finsuppℕ R) (f_zero : f 0 = 0) : Finsuppℕ R' := by
  apply Quotient.map'
    (s₁ := untrim_setoid (R := R))
    (s₂ := untrim_setoid (R := R'))
    (f := Segment.map f)
  case a => exact s
  case h =>
    intros x₁ x₂
    have ⟨n₁, v₁⟩ := x₁; clear x₁
    have ⟨n₂, v₂⟩ := x₂; clear x₂
    simp [untrim_setoid, Segment.map]
    intros input_equal
    rw [untrim_comp (g := f) (f := v₁) f_zero, untrim_comp (g := f) (f := v₂) f_zero, input_equal]

def Fin.fold (f : R → α → α) (z : α) (x : Fin n → R) : α := Id.run <| do
  let mut acc : α := z
  for i in (id : Fin n → Fin n) do
    acc := f (x i) acc
  return acc

