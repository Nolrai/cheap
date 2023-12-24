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

def With_bot.strong_induction' (motive : WithBot ℕ → Prop)
  (motive_bot : motive ⊥)
  (motive_coe : ∀ n : ℕ, (∀ m, m < ↑n → motive m) → motive ↑n )
  : ∀ n, motive n := by
  intros n
  cases n using WithBot.recBotCoe with
  | bot => exact motive_bot
  | coe n =>
    induction n using Nat.strong_induction_on with
    | h n ih =>
    apply motive_coe n
    intros m m_lt
    cases m using WithBot.recBotCoe with
    | bot => exact motive_bot
    | coe m =>
      apply ih
      rw [← WithBot.coe_lt_coe]
      exact m_lt

def With_bot.strong_induction (motive : WithBot ℕ → Prop)
  (hyp : ∀ n, (∀ m, m < n → motive m) → motive n )
  : ∀ n, motive n := by
    have motive_bot : motive ⊥ := by
      apply hyp
      intros m m_lt
      exfalso
      apply not_lt_bot m_lt
    apply With_bot.strong_induction' motive motive_bot (λ n hyp₂ ↦ hyp n hyp₂)

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

#print Polynomial.X

def productOfLinear [Semiring R] (m : Multiset R) := Finsupp.single (1 : R) (0 : R)



theorem Polynomial.StrongFundamentalTheoremOfAlgebra
