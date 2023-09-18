import Mathlib

namespace NSA

class Filter (U : Type → Type) extends Applicative U where
  filter : U Prop → Prop

open Filter

infix:60 "∧'" => λ p q => (· ∧ ·) <$> p <*> q
infix:60 "∨'" => λ p q => (· ∨ ·) <$> p <*> q
def not' {U : Type → Type} [Filter U] (p : U Prop) : U Prop := (¬ ·) <$> p

class LawfulFilter (U : Type → Type) extends Filter U where
  to_LawfulApplicative : LawfulApplicative U
  filter_pure : ∀ (p : Prop), filter (pure p : U Prop) = p
  filter_intersection : ∀ (p q : U Prop), filter (p ∧' q) = filter p ∧ filter q
  filter_all : (s : X → Prop) → (∀ (x : X), s x) → ∀ u : U X, filter (s <$> u)

class UltraFilter (U : Type → Type ) extends Filter U where
  ultra : ∀ p, filter p ∨ filter (not' p)

class LawfulUltraFilter (U : Type → Type) extends LawfulFilter U, UltraFilter U where
 -- empty

class NSA (U : Type → Type) extends Filter U where
  idealization : ∀ (r : X → Y → Prop), 
    (∀ s : Finset X, ∃ y, ∀ x ∈ s, filter (r x <$> y)) ↔ ∃ y, ∀ x, filter (r <$> pure x <*> y) 
