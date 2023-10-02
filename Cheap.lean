import Mathlib

def D₁ R [Ring R] := {x : R // x * x = 0}

instance [Ring R] : Coe (D₁ R) R where
  coe := λ x => x.val

def toLine [Ring R] : (R × R) → D₁ R → R
  | ⟨intercept, slope⟩, ε => intercept + ε.val * slope

class KockLawvere (R) extends Ring R, Nontrivial R where
  equiv : (D₁ R → R) ≃ R × R
  equiv_eval : ↑equiv.symm = toLine

namespace KockLawvere

def slope [kl : KockLawvere R] : (D₁ R → R) → R
  | g => (kl.equiv.toFun g).2

theorem slope_of_line [KockLawvere R] : slope (toLine ((x : R), y)) = y := by
  rw [slope, ← equiv_eval]
  simp

theorem slope_unique [kl : KockLawvere R] (intercept slope₁ slope₂ : R) : 
  toLine (intercept, slope₁) = toLine (intercept, slope₂) → slope₁ = slope₂ := by
      intros hyp
      have : (intercept, slope₁) = (intercept, slope₂)
      · apply kl.equiv.symm.injective
        rw [equiv_eval]
        exact hyp 
      cases this
      · rfl

theorem KockLawvere_cancel {R} [kl : KockLawvere R] {b₁ b₂ : R} :
  (∀ d : D₁ R, d.val * b₁ = d.val * b₂) → b₁ = b₂ := by
  intro hyp
  apply slope_unique 0
  simp [toLine]
  funext x
  apply hyp

-- might not be the right term
-- A "crisp" subset is just one that respects ≈
structure Crisp (R) [Ring R] where
  toSet : Set R
  crisp : ∀ (x : toSet) (d : D₁ R), (x : R) + d ∈ toSet

theorem Crisp.injective_toSet [Ring R] : Function.Injective (Crisp.toSet : Crisp R → Set R) 
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

instance [Ring R] : SetLike (Crisp R) R where
  coe := Crisp.toSet
  coe_injective' := Crisp.injective_toSet    

def first_dir [KockLawvere R] {C : Crisp R} : (C → R) → C → R 
  | f, x => slope (λ ε ↦ f ⟨x + ε, C.crisp x ε ⟩)

def nth_dir [KockLawvere R] {C : Crisp R} : ℕ → (C → R) → C → R
  | 0, f => f
  | n+1, f => first_dir (nth_dir n f)

theorem d_not_singleton [kl : KockLawvere R] : ¬ (∀ x : R, x * x = 0 → x = 0) := by
  intro hyp
  have : toLine (0, (1 : R)) = toLine (0, (0 : R)) := by
    funext y
    have ⟨y, y_nilpotent⟩ := y
    rw [toLine, toLine]
    simp
    apply hyp _ y_nilpotent
  apply (zero_ne_one : (0 : R) ≠ 1)
  apply Eq.trans (b := slope (toLine ((0 : R), 0))) 
  · rw [slope_of_line]
  · rw [← this, slope_of_line]

instance asPartialOrder [Preorder R] : Setoid R where
  r (a b : R) := a ≤ b ∧ b ≤ a
  iseqv := 
    ⟨ λ a => ⟨refl a, refl a⟩
    , λ ⟨a_le_b, b_le_a⟩ => ⟨b_le_a, a_le_b⟩
    , λ ⟨x_le_y, y_le_x⟩ ⟨y_le_z, z_le_y⟩ =>
      ⟨x_le_y.trans y_le_z, z_le_y.trans y_le_x⟩
    ⟩

class OrderedKockLawvere (R) extends KockLawvere R, Preorder R, ZeroLEOneClass R where
  add_monotonic (x y z : R) : x ≤ y → x + z ≤ y + z
  mul_nonneg_monotonic (x y t : R) : x ≤ y → 0 ≤ t → x * t ≤ y * t
  zero_lt_one : (0 : R) < 1
  nilpotent_fuzzy (ε : D₁ R) : 0 ≈ ε.val
  narrow : ∀ {a b : R}, ¬ a ≤ b → b ≤ a

open OrderedKockLawvere

theorem le_add_nilpotent [OrderedKockLawvere R] 
  (x y : R) (d : D₁ R) : x ≤ y ↔ (x ≤ y + d) := by
  constructor
  · intro hyp
    apply Preorder.le_trans (b := x + d)
    · rw [add_comm, ← zero_add x, ← add_assoc, add_zero]
      apply add_monotonic
      apply (nilpotent_fuzzy d).1
    · apply add_monotonic _ _ _ hyp
  · intro hyp
    apply Preorder.le_trans (b := y + d)
    · apply hyp
    · rw [add_comm, ← zero_add y, ← add_assoc, add_zero, add_comm, add_comm]
      apply add_monotonic
      apply (nilpotent_fuzzy d).2

theorem add_nilpotent_le [OrderedKockLawvere R] 
  (x y : R) (d : D₁ R) : x ≤ y ↔ (x + d ≤ y) := by
  constructor
  · intro hyp
    apply Preorder.le_trans (b := y + d)
    · apply add_monotonic _ _ _ hyp
    · rw [add_comm, ← zero_add y, ← add_assoc, add_zero, add_comm, add_comm]
      apply add_monotonic
      apply (nilpotent_fuzzy d).2
  · intro hyp
    apply Preorder.le_trans (b := x + d)
    · rw [add_comm, ← zero_add x, ← add_assoc, add_zero, add_comm, add_comm]
      apply add_monotonic
      apply (nilpotent_fuzzy d).1
    · apply hyp

def mkCrisp [OrderedKockLawvere R] (a b : R) : Crisp R where
  toSet x := a ≤ x ∧ x ≤ b
  crisp := by
    intros x d
    have ⟨x, a_le_x, x_le_b⟩ := x
    simp [Set.mem_def]
    apply And.intro
    · apply (le_add_nilpotent a x d).1 a_le_x
    · apply (add_nilpotent_le x b d).1 x_le_b

def I R [OrderedKockLawvere R] := mkCrisp (0 : R) 1

class IntegratableSpace (R) extends OrderedKockLawvere R where
  integrate : (I R → R) → (I R → R)
  integrate_start : ∀ f, integrate f ⟨zero, refl _, zero_le_one⟩ = 0
  is_antiderivative : ∀ f, first_dir (integrate f) = f

