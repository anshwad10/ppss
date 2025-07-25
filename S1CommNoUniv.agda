{-# OPTIONS --cubical #-}

module S1CommNoUniv where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.HITs.S1.Base

shift-loop : (x : S¹) → x ≡ x
shift-loop base = loop
shift-loop (loop i) = invSides-filler loop (sym loop) (~ i)

loop-swap : ∀ x (p : base ≡ x) → Square loop (shift-loop x) p p
loop-swap = J> refl

shift : (x : S¹) → base ≡ base → x ≡ x
shift base p = p
shift (loop i) p j = loop-swap base p j i

cool-comm : ∀ (q : base ≡ base) x (p : base ≡ x) → Square q (shift x q) p p
cool-comm q = J> refl

comm : (p q : base ≡ base) → p ∙ q ≡ q ∙ p
comm p q = Square→compPath (cool-comm q base p)
