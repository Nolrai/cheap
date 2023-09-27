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

instance [h : Semiring X] : Semiring (Id X) := h

section LiftSemiring where

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
    apply add_assoc

  add_comm := by
    intros a b
    simp [liftAdd.def]
    funext env
    simp [Seq.seq, Functor.map, Pure.pure]
    simp [OfNat.ofNat, ReaderT.pure]
    apply add_comm

  mul := lift2 (· * ·)
  mul_one := by
    intros a
    simp [liftAdd.def]
    funext env
    simp [Seq.seq, Functor.map, Pure.pure]
    simp [OfNat.ofNat, ReaderT.pure]
    apply mul_one

  one_mul := by
    intros a
    simp [liftAdd.def]
    funext env
    simp [Seq.seq, Functor.map, Pure.pure]
    simp [OfNat.ofNat, ReaderT.pure]
    apply one_mul

  zero_mul := by
    intros a
    simp [liftAdd.def]
    funext env
    simp [Seq.seq, Functor.map, Pure.pure]
    simp [OfNat.ofNat, ReaderT.pure]
    apply zero_mul

  mul_zero := by sorry
  mul_assoc := by sorry

  left_distrib := by sorry
  right_distrib := by sorry
