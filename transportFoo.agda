{-# OPTIONS --cubical #-}

module transportFoo where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Vec
open import Cubical.Data.Unit

_ : (A : Type) (x y z : A) → Vec A 3
_ = λ A x y z → transport refl (x ∷ y ∷ z ∷ []) -- Normalize it!
