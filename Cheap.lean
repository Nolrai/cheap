import Mathlib

namespace NSA

def Applicative.lift2 [Applicative F] (f : α → β → γ) (x : F α) (y : F β) : F γ := f <$> x <*> y

open Applicative

instance liftMul [Applicative F] [Mul X] : Mul (F X) where
  mul := lift2 (· * ·)

theorem liftMul.def [Applicative F] [Mul X] :
  ∀ x y : F X, x * y = (· * ·) <$> x <*> y := λ _ _ => rfl

instance liftAdd [Applicative F] [Add X] : Add (F X) where
  add := lift2 (· + ·)

theorem liftAdd.def [Applicative F] [Add X] :
  ∀ x y : F X, x + y = (· + ·) <$> x <*> y := λ _ _ => rfl

instance liftNeg [Applicative F] [Neg X] : Neg (F X) where
  neg := Functor.map (-·)

theorem liftNeg.def [Applicative F] [Neg X] :
  ∀ x : F X, -x = (-·) <$> x := λ _ => rfl

instance liftSub [Applicative F] [Sub X] : Sub (F X) where
  sub := lift2 (· - ·)

theorem liftSub.def [Applicative F] [Sub X] :
  ∀ x y : F X, x - y = (· - ·) <$> x <*> y := λ _ _ => rfl

open Function

instance liftSemiring [Semiring X] : Semiring (ReaderM Env X) where
  zero := pure 0
  one := pure 1

  add := lift2 (· + ·)
  add_zero := by
    intros a
    simp [liftAdd.def]
    funext env
    simp [Seq.seq, Functor.map, Pure.pure]
    simp [OfNat.ofNat, ReaderT.pure]
    have : (Zero.zero : X) = 0 := by rfl
    rw [this, add_zero]
    
  zero_add := by
    intros a
    simp [liftAdd.def]
    funext env
    simp [Seq.seq, Functor.map, Pure.pure]
    simp [OfNat.ofNat, ReaderT.pure]
    have : (Zero.zero : X) = 0 := by rfl
    rw [this, zero_add]
  
  add_assoc := by
    intros a b c
    simp [liftAdd.def]
    funext env
    simp [Seq.seq, Functor.map, Pure.pure]
    simp [OfNat.ofNat, ReaderT.pure]

  add_comm := by sorry

  mul := lift2 (· * ·)
  mul_one := by sorry
  one_mul := by sorry
  zero_mul := by sorry
  mul_zero := by sorry
  mul_assoc := by sorry

  left_distrib := by sorry
  right_distrib := by sorry

structure analysis (F : Type → Type) extends Applicative F where
  X : Type
  [is_ring : Ring X]
  derivative : (F X → F X) → F X → F X
  integral : (F X → F X) → F X → F X
  derivative_integral : ∀ f, derivative (integral f) = f
  anti_derivatives_differ_by_constant : ∀ f g : F X → F X, derivative f = derivative g → ∃ c, ∀ x : F X, f x = g x + c 
