{-# OPTIONS --prop #-}

module SProp where
open import Level using (Level; 0ℓ; _⊔_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Irrelevant

private variable
  ℓ ℓ' : Level
  X Y : Set ℓ
  P Q : Prop ℓ

record ⊤ : Prop where
  constructor tt

data ⊥ : Prop where

infix 30 ¬_

¬_ : Prop ℓ → Prop ℓ
¬ P = P → ⊥

data _∨_ (P : Prop ℓ) (Q : Prop ℓ') : Prop (ℓ ⊔ ℓ') where
  inl : P → P ∨ Q
  inr : Q → P ∨ Q

data Squash (X : Set ℓ) : Prop ℓ where
  squash : X → Squash X

squashElim : (X → P) → Squash X → P
squashElim f (squash x) = f x

record LiftT (X : Prop ℓ) : Set ℓ where
  constructor lift
  field lower : X

sPropIsProp : (P : Prop ℓ) → Irrelevant (LiftT P)
sPropIsProp P x y = refl

-- One might expect all hProps are strict propositions
-- which would mean there would be a function
-- squashPropOut : isProp X → Squash X → X
-- with computation rule
-- squashPropOut p (squash x) = x
-- however, this is not possible without equality reflection, which implies UIP
-- To see this, for x : X consider the type singl x := Σ[ y ∈ X ] x ≡ y
-- This type is contractible, but if it was in sProp, we would have,
-- for any y such that p : x ≡ y, (x , refl) = (y , p)
-- But this would mean that x = y definitionally
-- hence such a computation rule for squashPropOut would imply UIP
-- One could postulate squashPropOut without its computation rule but then
-- that would lead to stuck terms.

-- However, one can eliminate Squash X to ¬¬stable types:
squash→¬¬ : Squash X → ¬ (X → ⊥)
squash→¬¬ x f = squashElim f x

Stable : Set ℓ → Set ℓ
Stable X = ¬ (X → ⊥) → X

squashElimStable : Stable X → Squash X → X
squashElimStable f x = f (squash→¬¬ x)

-- So one might wonder if sProp is actually just the set of stable propositions.
-- Although this is not provable in Agda, it is consistent as it holds in Eff.

postulate ¬¬elim : ¬ ¬ P → P

-- Postulating ¬¬elim doesn't break computation because P is definitionally proof-irrelevant


mirabilis : ((P → ⊥) → P) → P
mirabilis f = ¬¬elim λ ¬p → ¬p (f ¬p)

lem : P ∨ ¬ P
lem = mirabilis λ f → inr λ p → f (inl p)

caseLEM : (P : Prop ℓ) → (P → Q) → (¬ P → Q) → Q
caseLEM P f g with lem {P = P}
... | inl x = f x
... | inr x = {!!}

exfalso : ⊥ → P
exfalso ()

pierce : (Q : Prop ℓ) → ((P → Q) → P) → P
pierce Q f = mirabilis λ ¬p → f λ p → exfalso (¬p p)

gdp : (P → Q) ∨ (Q → P)
gdp {P} {Q} = {!!}
