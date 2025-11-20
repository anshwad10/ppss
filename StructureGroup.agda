{-# OPTIONS --cubical --guardedness #-}

{-- Defining the structure group of a heap so I can prove J wrong --}

module StructureGroup where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.GroupPath
open import Cubical.HITs.PropositionalTruncation

private variable
  ℓ ℓ' : Level

record Heap ℓ : Type (ℓ-suc ℓ) where
  field
    H : Type ℓ
    H-is-set : isSet H
    [_,_,_] : H → H → H → H
    assoc : ∀ a b c d e → [ a , b , [ c , d , e ] ] ≡ [ [ a , b , c ] , d , e ]
    assoc' : ∀ a b c d e → [ a , [ d , c , b ] , e ] ≡ [ a , b , [ c , d , e ] ]
    idl : ∀ a b → [ a , a , b ] ≡ b
    idr : ∀ a b → [ a , b , b ] ≡ a
    inhab : ∥ H ∥₁

  StructureGroup : Group ℓ
  StructureGroup = toldYaSo inhab module StructureGroup where
    open GroupStr

    fromPoint : H → Group ℓ
    fromPoint e .fst = H
    fromPoint e .snd .1g = e
    fromPoint e .snd ._·_ a b = [ a , e , b ]
    fromPoint e .snd .inv a = [ e , a , e ]
    fromPoint e .snd .isGroup = makeIsGroup H-is-set
      (λ x y z → assoc x e y e z)
      (λ x → idr x e) -- is that a maybeJosiah reference
      (λ x → idl e x)
      (λ x → assoc x e e x e ∙∙ cong [_, x , e ] (idr x e) ∙∙ idl x e)
      (λ x → sym (assoc e x e e x) ∙∙ cong [ e , x ,_] (idl e x) ∙∙ idr e x)

    φ : ∀ e e' → GroupHom (fromPoint e) (fromPoint e')
    φ e e' .fst x = [ e' , e , x ]
    φ e e' .snd = makeIsGroupHom λ x y → 
      [ e' , e , [ x , e , y ] ]               ≡⟨ assoc e' e x e y ⟩
      [ [ e' , e , x ] , e , y ]               ≡⟨ cong [ [ e' , e , x ] ,_, y ] (sym (idr e e')) ⟩
      [ [ e' , e , x ] , [ e , e' , e' ] , y ] ≡⟨ assoc' [ e' , e , x ] e' e' e y ⟩
      [ [ e' , e , x ] , e' , [ e' , e , y ] ] ∎

    φ-coh : ∀ e e' e'' x → φ e' e'' .fst (φ e e' .fst x) ≡ φ e e'' .fst x
    φ-coh e e' e'' x = 
      [ e'' , e' , [ e' , e , x ] ] ≡⟨ sym (assoc' e'' e' e' e x) ⟩
      [ e'' , [ e , e' , e' ] , x ] ≡⟨ cong [ e'' ,_, x ] (idr e e') ⟩
      [ e'' , e , x ]               ∎

    φ-eqv : ∀ e e' → isEquiv (φ e e' .fst)
    φ-eqv e e' = isoToIsEquiv (iso (φ e e' .fst) (φ e' e .fst) (lemma e e') (lemma e' e)) where
    
      lemma : ∀ e e' x → φ e e' .fst (φ e' e .fst x) ≡ x
      lemma e e' x = φ-coh e' e e' x ∙ idl e' x

    toldYaSo : ∥ H ∥₁ → Group ℓ
    toldYaSo = PropTrunc→Group fromPoint (λ e e' → (φ e e' .fst , φ-eqv e e') , φ e e' .snd) φ-coh
