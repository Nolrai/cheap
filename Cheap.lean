import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Rat.Order
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.Order.Archimedean
import Mathlib.Init.Set
import Mathlib.Order.Zorn
import std
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Cofinite
import Mathlib.Order.Filter.Ultrafilter
import Mathlib.Order.Filter.Germ
import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.Data.Fin.Basic

open Filter

abbrev Star (α : Type u) := Germ ((hyperfilter ℕ) : Filter ℕ) α

abbrev Star.limit : (ℕ → α) → Star α := Germ.ofFun

open Star

theorem Star.ind {α : Type u}
  {p : Star α → Prop} (h : ∀ f : ℕ → α, p (limit f)) (s : Star α)
  : p s :=
  by
  induction s using Germ.inductionOn
  case h f =>
    apply h

def Star.map'
  (f : ((ℕ → α) → (ℕ → β)))
  (hyp : ∀ a b, ∀ᶠ (i : ℕ) in ↑(Filter.hyperfilter ℕ), a i = b i → f a i = f b i)
  : Star α → Star β
  := Germ.map' f (λ a b a_eqv_b ↦ Eventually.mp a_eqv_b (hyp a b))

def Star.lift
  {α β : Type u}
  (f : ((ℕ → α) → β))
  (hyp : ∀ a b : ℕ → α, (∀ᶠ (x : ℕ) in ↑(Filter.hyperfilter ℕ), (a x) = (b x)) → f a = f b)
  : Star α → β := Quotient.lift f hyp

def Star.seq {α β : Type u} (mf : Star (α → β)) (mx : Unit → Star α) : Star β := by
  apply Quotient.map₂' (λ f a i ↦ f i (a i)) _ mf (mx () )
  intros mf₁ mf₂ mf_equiv mx₁ mx₂ mx_equiv
  simp
  filter_upwards [mx_equiv, mf_equiv]
  intros i mx_eq mf_eq
  clear * - mx_eq mf_eq
  rw [mx_eq, mf_eq]

abbrev Star.map {α β : Type u} (F : α → β) : Star α → Star β := Germ.map F

instance : Applicative Star where
  map := Star.map
  pure a := Star.limit (λ _ ↦ a)
  seq := Star.seq
  seqLeft x _ := x
  seqRight _ y := y ()

@[simp]
theorem Star.segLeft_eq_left (x : Star α) (y : Star β) : x <* y = x := rfl

@[simp]
theorem Star.segRight_eq_right (x : Star α) (y : Star β) : x *> y = y:= rfl

@[simp]
theorem Star.seq_mk_mk (x : ℕ → α → β) (y : ℕ → α) : Star.limit x <*> Star.limit y = Star.limit (λ i ↦ x i (y i)) :=
  rfl

@[simp]
theorem Star.map_mk {α β : Type u} (f : ℕ → α) (F : α → β) :
  F <$> (Star.limit f) = Star.limit (F ∘ f) := rfl

@[simp]
theorem Star.pure_def {α : Type u} (x : α) : pure x = Star.limit (λ _ ↦ x) := rfl

instance : LawfulApplicative Star where
  map_const := rfl
  id_map := λ x ↦ Germ.inductionOn x
    (λ f ↦ by
      rw [Star.map_mk]
      simp
    )
  map_pure := λ f x ↦ by
    rw [Star.pure_def, Star.pure_def, Star.map_mk]
    simp [Function.comp]
  seqLeft_eq := λ x y ↦ by
    simp_rw [Star.segLeft_eq_left, Function.const]
    induction x using Star.ind
    case h f =>
      rw [Star.map_mk]
      induction y using Star.ind
      case h g =>
        rw [Star.seq_mk_mk]
        simp

  seqRight_eq := λ x y ↦ by
    simp_rw [Star.segRight_eq_right, Function.const]
    induction x using Star.ind
    case h f =>
      rw [Star.map_mk]
      induction y using Star.ind
      case h g =>
        rw [Star.seq_mk_mk]
        simp

  pure_seq := λ g x ↦ by
    rw [pure_def]
    induction x using Star.ind
    case h f =>
      rw [seq_mk_mk, map_mk]
      congr

  seq_pure := λ g x ↦ by
    induction g using Star.ind
    case h f =>
    rw [pure_def, seq_mk_mk, map_mk]
    congr

  seq_assoc := λ x g h ↦ by
    induction g using Star.ind
    case h g =>
    induction h using Star.ind
    case h h =>
    induction x using Star.ind
    case h x =>
    simp_rw [map_mk, Function.comp, seq_mk_mk]

inductive AddMul where
  | Add
  | Mul

abbrev fromBool (b : Bool) : Type :=
  if b then Unit else Empty

open FirstOrder
open Language

def GroupLanguage : Language :=
  Language.mk (fromBool ∘ (· < 3)) (λ _ ↦ Empty)

def OrderLanguage : Language :=
  Language.mk (λ _ ↦ Empty) (fromBool ∘ (· = 2))

def OrderedFieldLanguage : Language :=
  (GroupLanguage.sum GroupLanguage).sum OrderLanguage

open Functions

def assoc {L : Language} (f : L.Functions 2) : L.Sentence :=
  ∀' ∀' ∀'((f.apply₂ (f.apply₂ &0 &1) &2 =' f.apply₂ &0 (f.apply₂ &1 &2)))

def left_id {L : Language} (f : L.Functions 2) (e : L.Constants) : L.Sentence :=
  ∀' (f.apply₂ e.term &0 =' &0)

def right_id {L : Language} (f : L.Functions 2) (e : L.Constants) : L.Sentence :=
  ∀' (f.apply₂ &0 e.term =' &0)

def MonoidTheory {L : Language} (opp : L.Functions 2) (id : L.Constants) : L.Theory :=
  {assoc opp, left_id opp id, right_id opp id}

def
