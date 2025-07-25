{-# OPTIONS --cubical #-}

module MarkovsPrinciple where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.Nat as ℕ
open import Cubical.Relation.Nullary

{-# TERMINATING #-}
markov : (f : ℕ → Bool) → (¬ (∀ n → f n ≡ false)) → Σ[ n ∈ ℕ ] f n ≡ true
markov f f≢cf = helper (f 0) refl
  module markov where
    sucCase : Σ[ n ∈ ℕ ] f (suc n) ≡ true → Σ[ n ∈ ℕ ] f n ≡ true
    sucCase (n , p) = suc n , p

    helper : ∀ b → f 0 ≡ b → Σ[ n ∈ ℕ ] f n ≡ true
    helper false p0 = sucCase $ markov (f ∘ suc) λ ps → f≢cf (ℕ.elim p0 (const ∘ ps))
    helper true = 0 ,_
