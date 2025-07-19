{-# OPTIONS --cubical --hidden-argument-puns #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Relation.Nullary

module WeakResizing where

private variable
  ℓ : Level

{-# NO_UNIVERSE_CHECK #-}
record Ω ℓ : Type ℓ where
  constructor el
  field
    ∣_∣ : Type ℓ
    tr : isProp ∣_∣
open Ω public

Ω₀ = Ω ℓ-zero

-- Impredicative truncation
∥_∥ : Type ℓ → Type ℓ
∥_∥ {ℓ} X = (P : Ω ℓ) → (X → ∣ P ∣) → ∣ P ∣

isProp∥_∥ : (X : Type ℓ) → isProp ∥ X ∥
isProp∥ X ∥ = isPropΠ2 λ P _ → P .tr

isInhab : Type ℓ → Ω ℓ
∣ isInhab X ∣ = ∥ X ∥
isInhab X .tr = isProp∥ X ∥

-- Powersets
ℙ : Type ℓ → Type ℓ
ℙ {ℓ} X = X → Ω ℓ

-- Unfortunately, even this is enough to cause the type-checker to loop
private module Girard (allProps : {X : Type} → isProp X) where
  el! : Type → Ω₀
  el! A = el A allProps

  data V : Type where
    set : (A : Ω₀) → (∣ A ∣ → V) → V

  _∈_ : V → V → Type
  x ∈ set A f = Σ[ i ∈ ∣ A ∣ ] f i ≡ x

  foundation : ∀ x → ¬ x ∈ x
  foundation (set A f) x∈x@(i , p) = foundation (f i) (subst (f i ∈_) (sym p) (i , refl))

  V' : V
  V' = set (el! V) λ x → x

  V∈V : V' ∈ V'
  V∈V = V' , refl

  -- Typechecker loops when trying to normalize this term
  UhOh : ⊥
  UhOh = foundation V' V∈V
