{-# OPTIONS --cubical --safe #-}

module SuspMaybe where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Pointed
open import Cubical.Data.Unit.Base
open import Cubical.Data.Maybe.Base
open import Cubical.Data.Sum.Base
open import Cubical.HITs.Susp.Base
open import Cubical.HITs.Bouquet.Base
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Wedge.Base

private variable
  ℓ ℓ' : Level
  A B : Type ℓ

Bouquet→SuspMaybe : Bouquet A → Susp (Maybe A)
Bouquet→SuspMaybe base = north
Bouquet→SuspMaybe (loop x i) = (merid (just x) ∙ merid nothing ⁻¹) i

SuspMaybe→Bouquet : Susp (Maybe A) → Bouquet A
SuspMaybe→Bouquet north = base
SuspMaybe→Bouquet south = base
SuspMaybe→Bouquet (merid nothing i) = base
SuspMaybe→Bouquet (merid (just x) i) = loop x i

Bouquet→SuspMaybe→Bouquet : (x : Bouquet A) → SuspMaybe→Bouquet (Bouquet→SuspMaybe x) ≡ x
Bouquet→SuspMaybe→Bouquet base = refl
Bouquet→SuspMaybe→Bouquet (loop x i) j =
  (cong-∙ SuspMaybe→Bouquet (merid (just x)) (merid nothing ⁻¹) ∙ sym (rUnit (loop x))) j i
  
SuspMaybe→Bouquet→SuspMaybe : (x : Susp (Maybe A)) → Bouquet→SuspMaybe (SuspMaybe→Bouquet x) ≡ x
SuspMaybe→Bouquet→SuspMaybe north = refl
SuspMaybe→Bouquet→SuspMaybe south = merid nothing
SuspMaybe→Bouquet→SuspMaybe (merid nothing i) j = merid nothing (i ∧ j)
SuspMaybe→Bouquet→SuspMaybe (merid (just x) i) j = compPath-filler (merid (just x)) (merid nothing ⁻¹) (~ j) i

Bouquet⊎→Wedge : Bouquet (A ⊎ B) → Bouquet∙ A ⋁ Bouquet∙ B
Bouquet⊎→Wedge base = inl base
Bouquet⊎→Wedge (loop (inl x) i) = inl (loop x i)
Bouquet⊎→Wedge (loop (inr x) i) = (push tt ∙∙ cong Pushout.inr (loop x) ∙∙ sym (push tt)) i

Wedge→Bouquet⊎ : Bouquet∙ A ⋁ Bouquet∙ B → Bouquet (A ⊎ B)
Wedge→Bouquet⊎ (inl base) = base
Wedge→Bouquet⊎ (inl (loop x i)) = loop (inl x) i
Wedge→Bouquet⊎ (inr base) = base
Wedge→Bouquet⊎ (inr (loop x i)) = loop (inr x) i
Wedge→Bouquet⊎ (push tt i) = base

open Iso

BouquetIsoSuspMaybe : Iso (Bouquet A) (Susp (Maybe A))
BouquetIsoSuspMaybe .fun = Bouquet→SuspMaybe
BouquetIsoSuspMaybe .inv = SuspMaybe→Bouquet
BouquetIsoSuspMaybe .rightInv = SuspMaybe→Bouquet→SuspMaybe
BouquetIsoSuspMaybe .leftInv = Bouquet→SuspMaybe→Bouquet

Bouquet≃SuspMaybe : Bouquet A ≃ Susp (Maybe A)
Bouquet≃SuspMaybe = isoToEquiv BouquetIsoSuspMaybe

Bouquet⊎IsoWedge : Iso (Bouquet (A ⊎ B)) (Bouquet∙ A ⋁ Bouquet∙ B)
Bouquet⊎IsoWedge .fun = Bouquet⊎→Wedge
Bouquet⊎IsoWedge .inv = Wedge→Bouquet⊎
Bouquet⊎IsoWedge .rightInv (inl base) = refl
Bouquet⊎IsoWedge .rightInv (inl (loop x i)) = refl
Bouquet⊎IsoWedge .rightInv (inr base) = push tt
Bouquet⊎IsoWedge .rightInv (inr (loop x i)) j = doubleCompPath-filler (push tt) (cong Pushout.inr (loop x)) (sym (push tt)) (~ j) i
Bouquet⊎IsoWedge .rightInv (push tt i) j = push tt (i ∧ j)
Bouquet⊎IsoWedge .leftInv base = refl
Bouquet⊎IsoWedge .leftInv (loop (inl x) i) = refl
Bouquet⊎IsoWedge .leftInv (loop (inr x) i) j =
  (cong-∙∙ Wedge→Bouquet⊎ (push tt) (cong Pushout.inr (loop x)) (sym (push tt)) ∙ sym (rUnit (loop (inr x)))) j i

Bouquet⨄≃Wedge : Bouquet (A ⊎ B) ≃ (Bouquet∙ A ⋁ Bouquet∙ B)
Bouquet⨄≃Wedge = isoToEquiv Bouquet⊎IsoWedge
