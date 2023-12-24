import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Rat.Order
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

open Filter

section

def simply_ordered
  {α β : Type*} [LinearOrderedRing α] [LinearOrderedRing β]
  (f : α → β) :
  Prop := ∀ c, ¬ ((∃ᶠ n in atTop, f n > c) ∧ (∃ᶠ n in atTop, f n < c))

open Polynomial

theorem Polynomial.ind_aux
  [Semiring R]
  (p : R[X])
  {n : ℕ}
  : p.degree = ↑n →
  ∃ p' c, p'.degree < p.degree ∧ p = C c + p' * X := sorry

def exists_equal : ∀ n : α, ∃ m, n = m := λ n => ⟨n, rfl⟩

def With_bot.strong_induction [Preorder α] (motive : WithBot ℕ → Prop)
  (hyp : ∀ n, (∀ m, m < n → motive m) → motive n )
  : ∀ n, motive n := by
  have motive_bot : motive ⊥ := by
    apply hyp
    intros m m_lt
    exfalso
    apply not_lt_bot m_lt
  intros n
  cases n using WithBot.recBotCoe with
  | bot => exact motive_bot
  | coe n =>
    induction n using Nat.strong_induction_on with
    | h n ih =>
    apply hyp n
    intros m m_lt
    cases m using WithBot.recBotCoe with
    | bot => exact motive_bot
    | coe m =>
      apply ih
      rw [← WithBot.coe_lt_coe]
      exact m_lt

theorem Polynomial.ind
  [inst : OrderedSemiring R]
  (motive : R[X] → Prop)
  (zero_case : motive 0)
  (add_const : ∀ a p, motive p → motive (p + C a))
  (mul_X : ∀ p, motive p → motive (p * X))
  : ∀ (p : R[X]), motive p := by
    intro p
    have ⟨n, is_degree⟩ : ∃ n, p.degree = n := exists_equal p.degree
    revert p
    induction n using With_bot.strong_induction with
    | hyp n hyp =>
      intros p degree_p_eq
      cases n using WithBot.recBotCoe with
      | bot =>
        rw [degree_eq_bot, degree_p_eq] at *
        apply zero_case
      | coe n =>
        have ⟨p', c, lower_degree, eq_p⟩  := p.ind_aux degree_p_eq
        rw [add_comm] at eq_p
        rw [eq_p]
        rw [degree_p_eq] at *; clear degree_p_eq
        apply add_const
        apply mul_X
        apply hyp (degree p') lower_degree
        rfl
    apply inst.toPreorder

theorem Polynomial.eventually_ordered_zero
  [inst : LinearOrderedRing R]
  (p : R[X])
  : simply_ordered p.eval := by
  induction p using Polynomial.ind
  case zero_case =>
    intros reference hyp
    have ⟨pos, neg⟩ := hyp; clear hyp
    simp at *
    apply lt_irrefl (0 : R)
    apply lt_trans neg pos

  case add_const c p ih =>
    intros reference
    intros h
    have ⟨pos, neg⟩ := h; clear h
    apply ih (reference - c)
    simp at *
    constructor
    case left =>
      apply Frequently.mono pos
      intros x reference_lt_eval_p_plus_c
      rw [← add_zero (eval x p), ← add_left_neg (-c), sub_eq_add_neg, neg_neg, ← add_assoc]
      apply add_lt_add_right
      assumption
    case right =>
      apply Frequently.mono neg
      intros x reference_lt_eval_p_plus_c
      rw [← add_zero (eval x p), ← add_left_neg (-c), sub_eq_add_neg, neg_neg, ← add_assoc]
      apply add_lt_add_right
      assumption

  case mul_X p ih =>
    intros reference h
    have ⟨pos, neg⟩ := h; clear h
    simp at *
    
