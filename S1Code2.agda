{-# OPTIONS --cubical #-}

module S1Code2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)
open import Cubical.Data.Int

data S¹ : Type where
  base : S¹
  loop : base ≡ base

private variable
  ℓ : Level

elim : {P : S¹ → Type ℓ}
     → (Pbase : P base)
     → (Ploop : PathP (λ i → P (loop i)) Pbase Pbase)
     → ∀ x → P x
elim Pbase Ploop base = Pbase
elim Pbase Ploop (loop i) = Ploop i

elimProp : {P : S¹ → Type ℓ}
         → (Pbase : P base)
         → (Pprop : ∀ x → isProp (P x))
         → ∀ x → P x
elimProp Pbase Pprop = elim Pbase (isProp→PathP (λ i → Pprop (loop i)) _ _)

elimSet₂ : {P : S¹ → S¹ → Type ℓ}
         → (Pbase : P base base)
         → (Ploop₁ : PathP (λ i → P base (loop i)) Pbase Pbase)
         → (Ploop₂ : PathP (λ i → P (loop i) base) Pbase Pbase)
         → (Pset : ∀ x → isSet (P base x))
         → ∀ x y → P x y
elimSet₂ Pbase Ploop₁ Ploop₂ Pset = elim (elim Pbase Ploop₁) (funExt (elimProp Ploop₂ λ _ → isOfHLevelPathP' 1 (Pset _) _ _))

elimProp₂ : {P : S¹ → S¹ → Type ℓ}
          → (Pbase : P base base)
          → (Pprop : ∀ x y → isProp (P x y))
          → ∀ x y → P x y
elimProp₂ Pbase Pprop = elimProp (elimProp Pbase (Pprop base)) λ _ → isPropΠ λ _ → Pprop _ _

rec : {P : Type ℓ}
    → (Pbase : P)
    → (Ploop : Pbase ≡ Pbase)
    → S¹ → P
rec = elim

Code : S¹ → S¹ → Type
Code base base = ℤ
Code base (loop i) = sucPathℤ i
Code (loop i) base = sucPathℤ (~ i)
Code (loop i) (loop j) = invSides-filler sucPathℤ (sym sucPathℤ) i j

isSetCode : ∀ x y → isSet (Code x y)
isSetCode = elimProp₂ isSetℤ λ _ _ → isPropIsSet

CodeDiagonal : ∀ x → ℤ ≡ Code x x
CodeDiagonal base = refl
CodeDiagonal (loop i) j = compPathRefl {x = ℤ} j i

reflCode : ∀ x → Code x x
reflCode x = transport (CodeDiagonal x) 0

encode : ∀ x y → x ≡ y → Code x y
encode x = J> reflCode x

encodeRefl : ∀ x → encode x x refl ≡ reflCode x
encodeRefl x = transportRefl _

infix 40 loop^_
loop^_ : ℤ → base ≡ base
loop^ pos zero = refl
loop^ pos (suc n) = loop^ pos n ∙ loop 
loop^ negsuc zero = sym loop
loop^ negsuc (suc n) = loop^ negsuc n ∙ sym loop

encodeLoop^ : ∀ n → encode base base (loop^ n) ≡ n
encodeLoop^ (pos zero) = refl
encodeLoop^ (pos (suc n)) = cong sucℤ (encodeLoop^ (pos n))
encodeLoop^ (negsuc zero) = refl
encodeLoop^ (negsuc (suc n)) = cong predℤ (encodeLoop^ (negsuc n))

loop^suc : ∀ n → loop^ sucℤ n ≡ loop ∙ loop^ n
loop^suc (pos zero) = Square→compPath refl
loop^suc (pos (suc n)) = congL _∙_ (loop^suc (pos n)) ∙ sym (assoc loop (loop^ pos n) loop)
loop^suc (negsuc zero) = sym (rCancel loop)
loop^suc (negsuc (suc zero)) = PathP→compPathR (invSides-filler _ _)
loop^suc (negsuc (suc (suc n))) = congL _∙_ (loop^suc (negsuc (suc n))) ∙ sym (assoc _ _ _)

decode : ∀ x y → Code x y → x ≡ y
decode = elimSet₂ loop^_ (cong decodeBase loop) (symP (ua→ sq₂)) λ x → isSet→ (isSetBase≡ x) module decode where

  sq₁ : ∀ n → Square (loop^ n) (loop^ sucℤ n) refl loop
  sq₁ (pos n) = compPath-filler (loop^ pos n) loop
  sq₁ (negsuc zero) = λ i j → loop (i ∨ ~ j)
  sq₁ (negsuc (suc n)) = symP (compPath-filler (loop^ negsuc n) (sym loop))

  sq₂ : ∀ n → Square (loop^ n) (loop^ sucℤ n) (sym loop) refl
  sq₂ n = subst (λ p → Square (loop^ n) p (sym loop) refl) (sym (loop^suc n)) (compPath-filler' loop (loop^ n))

  decodeBase : ∀ x → Code base x → base ≡ x
  decodeBase = elim loop^_ (ua→ sq₁)

  decodeEncodeBase : ∀ x p → decodeBase x (encode base x p) ≡ p
  decodeEncodeBase = J> refl

  isSetBase≡ : ∀ x → isSet (base ≡ x)
  isSetBase≡ x = isSetRetract (encode base x) (decodeBase x) (decodeEncodeBase x) (isSetCode base x)

isGroupoidS¹ : isGroupoid S¹
isGroupoidS¹ = elimProp isSetBase≡ λ _ → isPropΠ λ _ → isPropIsSet where open decode

decodeRefl : ∀ x → decode x x (reflCode x) ≡ refl
decodeRefl = elimProp refl λ _ → isGroupoidS¹ _ _ _ _

decodeEncode : ∀ x y p → decode x y (encode x y p) ≡ p
decodeEncode = elimProp decodeEncodeBase λ _ → isPropΠ2 λ _ _ → isGroupoidS¹ _ _ _ _ where open decode

encodeDecode : ∀ x y n → encode x y (decode x y n) ≡ n
encodeDecode = elimProp₂ encodeLoop^ λ x y → isPropΠ λ _ → isSetCode x y _ _

CodeIsoPath : ∀ x y → Iso (x ≡ y) (Code x y)
CodeIsoPath x y .Iso.fun = encode x y
CodeIsoPath x y .Iso.inv = decode x y
CodeIsoPath x y .Iso.rightInv = encodeDecode x y
CodeIsoPath x y .Iso.leftInv = decodeEncode x y

Code≃Path : ∀ x y → (x ≡ y) ≃ Code x y
Code≃Path x y = isoToEquiv (CodeIsoPath x y)

Code≡Path : ∀ x y → (x ≡ y) ≡ Code x y
Code≡Path x y = ua (Code≃Path x y)

ΩS¹≡ℤ : (x : S¹) → (x ≡ x) ≡ ℤ
ΩS¹≡ℤ x i = Glue (CodeDiagonal x (~ i)) λ where
  (i = i0) → _ , Code≃Path x x
  (i = i1) → _ , idEquiv ℤ
