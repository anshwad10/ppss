{-# OPTIONS --cubical --guardedness --safe --hidden-argument-puns #-}

-- Written by Nuclear Catapult

open import Agda.Primitive
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma

variable
 ℓ ℓ' : Level
 A B : Type ℓ

record Category (ob : Type ℓ)(ℓ' : Level) : Type (ℓ-max ℓ (lsuc ℓ')) where
  field
    Hom : ob → ob → Type ℓ'
    Id   : ∀ x → Hom x x
    _⋆_  : ∀ {x y z} (f : Hom x y) (g : Hom y z) → Hom x z
    ⋆IdL : ∀ {x y} (f : Hom x y) → f ≡ Id x ⋆ f
    ⋆IdR : ∀ {x y} (f : Hom x y) → f ≡ f ⋆ Id y
    ⋆Assoc : ∀ {x y z w} (f : Hom x y) (g : Hom y z) (h : Hom z w)
           → f ⋆ (g ⋆ h) ≡ (f ⋆ g) ⋆ h

record ∞-Category{ob : Type ℓ}(Cat : Category ob ℓ') : Type (ℓ ⊔ (lsuc ℓ')) where
  coinductive
  open Category Cat
  field
   Cat⁑ : (a b : ob) → Category (Hom a b) ℓ'
  Hom₂ : {a b : ob} → Hom a b → Hom a b → Type ℓ'
  Hom₂ {a}{b} = Category.Hom (Cat⁑ a b)
  Id₂ : {a b : ob} → (f : Hom a b) → Hom₂ f f
  Id₂ {a}{b} = Category.Id (Cat⁑ a b)
  -- Vertical composition
  _⁑_ : {a b : ob}{f g h : Hom a b} → Hom₂ f g → Hom₂ g h → Hom₂ f h
  _⁑_ {a} {b} = Category._⋆_ (Cat⁑ a b)
  field
   -- Horizontal composition
   _⋆⋆_ : ∀{c d e}{J K : Hom e c}{F G : Hom c d} → Hom₂ J K → Hom₂ F G → Hom₂ (J ⋆ F) (K ⋆ G)
   ⋆⋆IdL : {a b : ob}{F G : Hom a b}(X : Hom₂ F G) →
      PathP (λ i → Hom₂ (⋆IdL F i) (⋆IdL G i))
            X
            (Id₂ (Id a) ⋆⋆ X)
   ⋆⋆IdR : {a b : ob}{F G : Hom a b}(X : Hom₂ F G) →
      PathP (λ i → Hom₂ (⋆IdR F i) (⋆IdR G i))
            X
            (X ⋆⋆ Id₂ (Id b))
   ⋆⋆Assoc : ∀{a b c d}{F G : Hom a b}{H I : Hom b c}{J K : Hom c d}
                 → (X : Hom₂ F G)
                 → (Y : Hom₂ H I)
                 → (Z : Hom₂ J K)
                 → PathP (λ i → Hom₂ (⋆Assoc F H J i) (⋆Assoc G I K i))
                         (X ⋆⋆ (Y ⋆⋆ Z))
                         ((X ⋆⋆ Y) ⋆⋆ Z)
  ΣHom : ob → ob → Type ℓ'
  ΣHom x y = Σ[ (p , q) ∈ (Hom x y × Hom x y)] Hom₂ p q
  ΣId : (x : ob) → ΣHom x x
  ΣId = λ x → (Id x , Id x) , Id₂ (Id x)
  _Σ⋆_ : {x y z : ob} → ΣHom x y → ΣHom y z → ΣHom x z
  _Σ⋆_ = λ((p , q) , p→q) → λ((r , s) , r→s) → ((p ⋆ r) , (q ⋆ s)) , (p→q ⋆⋆ r→s)
  ΣIdL : {x y : ob} → (X : ΣHom x y) → X ≡ ΣId x Σ⋆ X
  ΣIdL ((p , q) , p→q) i = (⋆IdL p i , ⋆IdL q i) , ⋆⋆IdL p→q i
  ΣIdR : {x y : ob} → (X : ΣHom x y) → X ≡ X Σ⋆ ΣId y
  ΣIdR ((p , q) , p→q) i = (⋆IdR p i , ⋆IdR q i) , ⋆⋆IdR p→q i
  Σ⋆Assoc : ∀{a b c d} → (X : ΣHom a b)(Y : ΣHom b c)(Z : ΣHom c d)
          → X Σ⋆ (Y Σ⋆ Z) ≡ (X Σ⋆ Y) Σ⋆ Z
  Σ⋆Assoc ((p , q) , p→q) ((r , s) , r→s) ((t , u) , t→u) i = (⋆Assoc p r t i , ⋆Assoc q s u i)
                                                            , ⋆⋆Assoc p→q r→s t→u i
  ΣCategory : Category ob ℓ'
  ΣCategory = record
               { Hom = ΣHom
               ; Id = ΣId
               ; _⋆_ = _Σ⋆_
               ; ⋆IdL = ΣIdL
               ; ⋆IdR = ΣIdR
               ; ⋆Assoc = Σ⋆Assoc
               }
  field
     interchange : ∀{a b c} → {p q r : Hom a b}{s t u : Hom b c}
                 → (δ : Hom₂ r q)(β :  Hom₂ u t)(γ : Hom₂ q p) (α : Hom₂ t s)
                 → (δ ⋆⋆ β) ⁑ (γ ⋆⋆ α) ≡ (δ ⁑ γ) ⋆⋆ (β ⁑ α)
     ΣCoInd : ∞-Category ΣCategory
     ⁑CoInd : (a b : ob) → ∞-Category (Cat⁑ a b)

PathCat : (X : Type ℓ) → Category X ℓ
PathCat X .Category.Hom = _≡_
PathCat X .Category.Id x = refl
PathCat X .Category._⋆_ = _∙_
PathCat X .Category.⋆IdL = lUnit
PathCat X .Category.⋆IdR = rUnit
PathCat X .Category.⋆Assoc = assoc

Path∞Cat : (X : Type ℓ) → ∞-Category (PathCat X)
Path∞Cat X .∞-Category.Cat⁑ a b = PathCat (a ≡ b)
Path∞Cat X .∞-Category._⋆⋆_ p q = cong₂ _∙_ p q
Path∞Cat X .∞-Category.⋆⋆IdL p i j = lUnit (p j) i
Path∞Cat X .∞-Category.⋆⋆IdR p i j = rUnit (p j) i
Path∞Cat X .∞-Category.⋆⋆Assoc p q r i j = assoc (p j) (q j) (r j) i
Path∞Cat X .∞-Category.interchange δ β γ α = {!!}
Path∞Cat X .∞-Category.ΣCoInd = {!!}
Path∞Cat X .∞-Category.⁑CoInd a b = Path∞Cat (a ≡ b)

TypeCat : ∀ ℓ → Category (Type ℓ) ℓ
TypeCat ℓ .Category.Hom X Y = X → Y
TypeCat ℓ .Category.Id X x = x
TypeCat ℓ .Category._⋆_ f g x = g (f x)
TypeCat ℓ .Category.⋆IdL f = refl
TypeCat ℓ .Category.⋆IdR f = refl
TypeCat ℓ .Category.⋆Assoc f g h = refl

-- Type∞Cat : ∀ ℓ → ∞-Category (TypeCat ℓ)
-- Type∞Cat ℓ .∞-Category.Cat⁑ = {!!}
-- Type∞Cat ℓ .∞-Category._⋆⋆_ = {!!}
-- Type∞Cat ℓ .∞-Category.⋆⋆IdL = {!!}
-- Type∞Cat ℓ .∞-Category.⋆⋆IdR = {!!}
-- Type∞Cat ℓ .∞-Category.⋆⋆Assoc = {!!}
-- Type∞Cat ℓ .∞-Category.interchange = {!!}
-- Type∞Cat ℓ .∞-Category.ΣCoInd = {!!}
-- Type∞Cat ℓ .∞-Category.⁑CoInd = {!!}
