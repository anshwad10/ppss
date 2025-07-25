{-# OPTIONS --cubical --safe #-}

module SuspMaybe where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Data.Maybe
open import Cubical.HITs.Susp.Base
open import Cubical.HITs.Bouquet.Base

private variable
  ℓ : Level
  A : Type ℓ

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

open Iso

BouquetIsoSuspMaybe : Iso (Bouquet A) (Susp (Maybe A))
BouquetIsoSuspMaybe .fun = Bouquet→SuspMaybe
BouquetIsoSuspMaybe .inv = SuspMaybe→Bouquet
BouquetIsoSuspMaybe .rightInv = SuspMaybe→Bouquet→SuspMaybe
BouquetIsoSuspMaybe .leftInv = Bouquet→SuspMaybe→Bouquet

Bouquet≃SuspMaybe : Bouquet A ≃ Susp (Maybe A)
Bouquet≃SuspMaybe = isoToEquiv BouquetIsoSuspMaybe


