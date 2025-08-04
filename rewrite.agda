{-# OPTIONS --cubical --rewriting #-}

module Rewrite where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Equality.Base using () renaming (_≡_ to Eq)
open import Cubical.Data.Equality.Conversion using (pathToEq)
open import Agda.Builtin.Equality.Rewrite
open import Cubical.HITs.S1 as S¹
open import Cubical.HITs.Interval as Interval
open import Cubical.Data.Empty

private variable
  ℓ : Level
  X : Type ℓ

left≡right : Eq zero one
left≡right = pathToEq seg

{-# REWRITE left≡right #-}

Interval→S1 : Interval → S¹
Interval→S1 = Interval.elim _ base base loop

S1→Interval : S¹ → Interval
S1→Interval base = zero
S1→Interval (loop i) = seg i

S1→Interval→S1 : ∀ x → Interval→S1 (S1→Interval x) ≡ x
S1→Interval→S1 base = refl
S1→Interval→S1 (loop i) = refl

isContrS¹ : isContr S¹
isContrS¹ = isContrRetract S1→Interval Interval→S1 S1→Interval→S1 isContrInterval
