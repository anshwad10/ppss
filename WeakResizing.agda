{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module WeakResizing where

{-# NO_UNIVERSE_CHECK #-}
record Ω ℓ : Type ℓ where
  constructor el
  field
    ∣_∣    : Type ℓ
    .tr : isProp ∣_∣
open Ω public

