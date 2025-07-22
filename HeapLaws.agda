{-# OPTIONS --cubical --hidden-argument-puns #-}

module HeapLaws where

open import Cubical.Foundations.Prelude

private variable
  ℓ : Level
  A : Type ℓ
  x y : A
  p q r s t : x ≡ y

heapInvL : p ∙∙ sym p ∙∙ q ≡ q
heapInvL {p} {q} i j = hcomp (λ k → λ where
    (i = i1) → q (j ∧ k)
    (j = i0) → p (~ k ∧ ~ i)
    (j = i1) → q k
  ) (p (~ i ∧ ~ j))

heapInvR : p ∙∙ sym q ∙∙ q ≡ p
heapInvR = cong sym heapInvL

heapAssoc : ((p ∙∙ q ∙∙ r) ∙∙ s ∙∙ t) ≡ (p ∙∙ q ∙∙ (r ∙∙ s ∙∙ t))
heapAssoc {p} {q} {r} {s} {t} = λ i → sq₁ i ∙∙ sq₂ i ∙∙ sq₃ i module heapAssoc where

  sq₁ : Square (p ∙∙ q ∙∙ r) p refl (sym r ∙ sym q)
  sq₁ i j = hcomp (λ k → λ where
      (i = i1) → p (j ∨ ~ k)
      (j = i0) → p (~ k)
      (j = i1) → compPath-filler' (sym r) (sym q) k i
    ) (q (~ i ∧ j))

  sq₂ : Square s q (sym r ∙ sym q) (sym s ∙' sym r)
  sq₂ i j = hcomp (λ k → λ where
      (i = i0) → s (j ∧ k)
      (i = i1) → q (j ∨ ~ k)
    ) (r (~ i))

  sq₃ : Square t (r ∙∙ s ∙∙ t) (sym s ∙' sym r) refl
  sq₃ i j = hcomp (λ k → λ where
      (i = i0) → t (j ∧ k)
      (j = i0) → compPath-filler' r s k (~ i)
      (j = i1) → t k
    ) (s (~ i ∨ j))
