
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Germ
import Mathlib.Order.Filter.Cofinite
import Mathlib.Order.Filter.AtTopBot

open Filter

structure F (α β : Type u) : Type u where
  filter : Filter α
  le_cofinite : filter ≤ cofinite
  toFun : α → β

instance : Functor (F env) where
  map := λ f fx ↦ {fx with toFun := f ∘ fx.toFun}
  mapConst := λ a fx ↦ {fx with toFun := λ _ ↦ a}

instance : LawfulFunctor (F γ) where
  id_map := λ _ ↦ rfl
  comp_map := λ _ _ _ ↦ rfl
  map_const := rfl

instance : Applicative (F ℕ) where
  pure := λ x ↦ {
    filter := cofinite
    le_cofinite := le_rfl
    toFun := λ _ ↦ x
    }
  seq := λ mf mx ↦ {
    filter := mf.filter ⊓ (mx ()).filter
    le_cofinite := le_trans inf_le_left mf.le_cofinite
    toFun := λ i ↦ mf.toFun i ((mx ()).toFun i)
    }
  seqLeft := λ ma mb ↦ {
    filter := ma.filter ⊓ (mb ()).filter
    le_cofinite := le_trans inf_le_left ma.le_cofinite
    toFun := ma.toFun
    }
  seqRight := λ ma mb ↦ {
    filter := ma.filter ⊓ (mb ()).filter
    le_cofinite := le_trans inf_le_left ma.le_cofinite
    toFun := (mb ()).toFun
    }

instance : LawfulApplicative (F ℕ) where
  seqLeft_eq := λ ma mb ↦ rfl
  seqRight_eq := λ ma mb ↦ rfl
  map_pure := λ g x ↦ rfl
  pure_seq := λ g ⟨l, l_le, f⟩ ↦ by
    simp [Seq.seq, Pure.pure, Functor.map]
    apply And.intro l_le
    funext
    simp
  seq_pure := λ ⟨l, l_le, f⟩ x ↦ by
    simp [Seq.seq, Pure.pure, Functor.map]
    apply And.intro l_le
    funext
    simp
  seq_assoc := λ x ⟨l₁, l₁_le, f₁⟩ ⟨l₂, l₂_le, f₂⟩ ↦ by
    simp [Seq.seq, Pure.pure, Functor.map]
    rw [← inf_assoc]

inductive F.r : F α β → F α β → Prop where
  | intro (filter : Filter α) {a b : F α β} (le_a : filter ≤ a.filter) (le_b : filter ≤ b.filter) (eeq : a.toFun =ᶠ[filter] b.toFun) : F.r a b

instance F.Setoid : Setoid (F α β) where
  r := F.r
  iseqv := {
    refl := λ a ↦ F.r.intro a.filter (le_refl _) (le_refl _) (EventuallyEq.refl _ _)
    symm := λ ⟨l, l_le_a, l_le_b, eeq⟩ ↦ F.r.intro l l_le_b l_le_a eeq.symm
    trans := λ ab' bc' ↦
      have ⟨l₁, le_a, _, ab⟩ := ab'
      have ⟨l₂, _, le_c, bc⟩ := bc'
      ⟨ l₁ ⊓ l₂
      , le_trans inf_le_left le_a, le_trans inf_le_right le_c
      , EventuallyEq.trans (ab.filter_mono inf_le_left) (bc.filter_mono inf_le_right)
      ⟩
  }

def Star α := Quotient (F.Setoid (α := ℕ) (β := α))

abbrev Star.mk (r : F ℕ α) : Star α := Quotient.mk _ r

theorem Star.ind (motive : Star α → Prop) (hyp : ∀ r : F ℕ α, motive (Star.mk r)) : ∀ s, motive s := Quotient.ind hyp
theorem Star.ind₂ (motive : Star α → Star β → Prop) (hyp : ∀ (ra : F ℕ α) (rb : F ℕ β), motive (Star.mk ra) (Star.mk rb)) :
  ∀ sa sb, motive sa sb := Quotient.ind₂ hyp
theorem Star.ind₃
  (motive : Star α → Star β → Star γ → Prop)
  (hyp : ∀ (ra : F ℕ α) (rb : F ℕ β) (rc : F ℕ γ), motive (Star.mk ra) (Star.mk rb) (Star.mk rc))
  : ∀ sa sb sc, motive sa sb sc := by
  intros sa
  apply Star.ind₂
  revert sa
  apply Star.ind
  apply hyp

def Star.map (f : α → β) : Star α → Star β := Quotient.map (f <$> ·) $ by
  intros x₁ x₂ x_eqv
  have ⟨l₁, _, x₁⟩ := x₁
  have ⟨l₂, _, x₂⟩ := x₂
  have ⟨l, l_le_l₁, l_le_l₂, eqv⟩ := x_eqv
  simp [Functor.map]
  use l
  simp_rw [] at *
  apply Eventually.mono eqv
  intros i i_h
  simp [i_h]

def Star.mapConst (b : β) : Star α → Star β := Quotient.map (Functor.mapConst b) $ by
  intros x₁ x₂ x_eqv
  have ⟨l, l_le_l₁, l_le_l₂, _⟩ := x_eqv
  simp [Functor.mapConst]
  use l

instance : Functor Star where
  map := Star.map
  mapConst := Star.mapConst

theorem Star.map_mk (f : α → β) r : f <$> Star.mk r = Star.mk (f <$> r) := by
  have : f <$> mk r = Star.map f (mk r) := rfl
  rw [this, Star.map, Quotient.map_mk]

instance : LawfulFunctor Star where
  map_const := rfl
  id_map x := by
    induction x using Star.ind
    case hyp x =>
    rw [Star.map_mk]
    rw [id_map]
  comp_map f g x := by
    induction x using Star.ind
    simp [Star.map_mk, comp_map]

def Star.seq (mf : Star (α → β)) (mx : Unit → Star α) : Star β := by
  apply Quotient.map₂ (· <*> ·) _ mf (mx ())
  intros mf₁ mf₂ mf_eqv mx₁ mx₂ mx_eqv
  have ⟨lx₁, _, x₁⟩ := mx₁
  have ⟨lx₂, _, x₂⟩ := mx₂
  have ⟨lx, lx_le_lx₁, lx_le_lx₂, x_eqv⟩ := mx_eqv
  have ⟨lf₁, _, mf₁⟩ := mf₁
  have ⟨lf₂, _, mf₂⟩ := mf₂
  have ⟨lf, lf_le_lf₁, lf_le_lf₂, f_eqv⟩ := mf_eqv
  use lf ⊓ lx
  case le_a =>
    clear * - lf_le_lf₁ lx_le_lx₁
    simp [Seq.seq] at *
    constructor
    · exact le_trans (b := lf) inf_le_left lf_le_lf₁
    · apply le_trans (b := lx) inf_le_right lx_le_lx₁
  case le_b =>
    clear * - lf_le_lf₂ lx_le_lx₂
    simp [Seq.seq] at *
    constructor
    · exact le_trans (b := lf) inf_le_left lf_le_lf₂
    · exact le_trans (b := lx) inf_le_right lx_le_lx₂
  case eeq =>
    clear * - x_eqv f_eqv
    simp_rw [Seq.seq] at *
    apply Eventually.mp (x_eqv.filter_mono inf_le_right)
    apply Eventually.mp (f_eqv.filter_mono inf_le_left)
    apply eventually_of_forall
    intros i feq xeq
    simp [feq, xeq]

theorem Star.seq_mk' (rf : F ℕ (α → β)) (rx : Unit → F ℕ α) :
  (Star.mk rf).seq (Star.mk ∘ rx) = Star.mk (Seq.seq rf rx) := by simp [Star.seq]

instance : Applicative Star where
  pure x := Star.mk (pure x)
  seq := Star.seq

theorem Star.pure_mk : pure x = Star.mk (pure x) := rfl

theorem Star.seq_mk (rf : F ℕ (α → β)) (rx : F ℕ α) :
  Star.mk rf <*> Star.mk rx = Star.mk (rf <*> rx) := rfl

instance : LawfulApplicative Star where
  map_pure := λ _ _ ↦ rfl
  seq_pure := λ f x ↦ by
    induction f using Star.ind
    case hyp f => simp [Star.pure_mk, Star.seq_mk, Star.map_mk]
  pure_seq := λ g x ↦ by
    induction x using Star.ind
    case hyp r =>
      rw [Star.pure_mk, Star.seq_mk, Star.map_mk, pure_seq]
  seq_assoc := λ f g h ↦ by
    induction f using Star.ind
    case hyp f =>
    induction g using Star.ind
    case hyp g =>
    induction h using Star.ind
    case hyp h =>
      simp [Star.seq_mk, Star.map_mk, LawfulApplicative.seq_assoc (f := F _)]
  seqLeft_eq := λ _ _ => rfl
  seqRight_eq := λ _ _ => rfl

abbrev Star.map₂ (op : α → β → γ) (a : Star α) (b : Star β) : Star γ := op <$> a <*> b

theorem Star.map₂_mk (op : α → β → γ) (a) (b) : (Star.mk a).map₂ op (Star.mk b) = Star.mk (op <$> a <*> b) := rfl

open Star

instance [Mul α] : Mul (Star α) where
  mul a b := a.map₂ Mul.mul b

theorem Star.mul_def [Mul α] (a b : Star α) : a * b = a.map₂ Mul.mul b := rfl

instance [Semigroup α] : Semigroup (Star α) where
  mul_assoc a b c := by
