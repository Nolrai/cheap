
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Germ
import Mathlib.Order.Filter.AtTopBot

open Filter

structure Star (α : Type u) where
  filter : Filter ℕ
  germ : filter.Germ α

def Germ.sinkFilter {l₁ l₂ : Filter base} (filter_le : l₂ ≤ l₁) : Germ l₁ α → Germ l₂ α := by
  intros x
  apply Germ.compTendsto x (g := id)
  simp_rw [Filter.le_def, tendsto_def, Set.preimage_id_eq, id] at *
  assumption

/-
fields missing: 'seqLeft', 'seqRight'
-/
instance : Applicative Star where
  map f x := ⟨x.filter, x.germ.map f⟩
  mapConst x y := ⟨y.filter, Germ.const x⟩
  pure a := ⟨Filter.atTop, Germ.const a⟩
  seq := λ {α β} sf' sx'' =>
    let sx' := sx'' ()
    let l := sf'.filter ⊓ sx'.filter
    let sf : l.Germ (α → β) := Germ.sinkFilter (α := α → β) (inf_le_left : l ≤ sf'.filter)  sf'.germ
    let sx := Germ.sinkFilter (α := α) (inf_le_right : l ≤ sx'.filter)  sx'.germ
    { filter := l
    , germ := sf.map₂ (· $ ·) sx
    }
  seqLeft := λ {α _} left right => {
    filter := left.filter ⊓ (right ()).filter
    germ := Germ.sinkFilter (α := α) inf_le_left left.germ
  }
  seqRight := λ {_ β} left right' =>
    let right := right' ()
    { filter := left.filter ⊓ right.filter
    , germ := Germ.sinkFilter (α := β) inf_le_right right.germ
    }

@[simp]
theorem Star.map_filter (f : α → β) (x : Star α) : (f <$> x).filter = x.filter := rfl

theorem Star.seqLeft_eq (x : Star α) (y : Star β) : (SeqLeft.seqLeft x fun x => y) = Seq.seq (Function.const β <$> x) fun x => y
  := by
    have ⟨xf, xg⟩ := x; clear x
    have ⟨yf, yg⟩ := y; clear y
    simp [SeqLeft.seqLeft]
    simp [Seq.seq]
    induction xg using Germ.inductionOn
    induction yg using Germ.inductionOn
    rw [Germ.map₂, Quotient.map₂']

instance : LawfulApplicative Star where
  map_const := by
    intros α β
    funext a x
    have ⟨f, g⟩ := x
    induction g using Germ.inductionOn with
    | h f =>
      simp [Functor.mapConst, Functor.map]
      rfl
  id_map {α} x := by simp [Functor.map]
  seqLeft_eq := Star.seqLeft_eq
