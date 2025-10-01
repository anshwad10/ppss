{-# OPTIONS --without-K #-}

module FOL where

open import Level using (Level; 0ℓ; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat.Properties
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Vec hiding ([_])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import Data.Empty.Polymorphic renaming (⊥ to Empty)
open import Data.Unit.Polymorphic renaming (⊤ to Unit)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Fin.Patterns
open import Relation.Nullary.Decidable.Core using (True; toWitness)
open import Function.Base
open import Data.Bool using (Bool; true; false; T)
                      renaming (_∧_ to _and_; _∨_ to _or_)
open import Data.Vec.Recursive as RecVec using (_^_)
import Data.Unit

private
  variable
    ℓ : Level
    n m : ℕ

pattern [_] x = x ∷ []

record Signature (ℓ : Level) : Set (lsuc ℓ) where
  field
    Function : ℕ → Set ℓ
    Relation : ℕ → Set ℓ

module Types (S : Signature ℓ) where

  open Data.Nat hiding (_^_)
  open Data.Nat.Properties
  open Signature S

  data Term (n : ℕ) : Set ℓ where
    var : Fin n → Term n -- We represent variables using De Bruijn indices
    fun : ∀ {a} → Function a → Vec (Term n) a → Term n

  module _ {P : Set ℓ} (fvar : Fin n → P)
           (ffun : ∀ {a} → Function a → Vec (Term n) a → Vec P a → P) where
           
    term-rec : Term n → P
    map-term-rec : ∀ {a} → Vec (Term n) a → Vec P a

    term-rec (var i) = fvar i
    term-rec (fun g v) = ffun g v (map-term-rec v)

    map-term-rec [] = []
    map-term-rec (x ∷ v) = term-rec x ∷ map-term-rec v

  data Formula (n : ℕ) : Set ℓ where
    rel : ∀ {a} → Relation a → Vec (Term n) a → Formula n
    ⊤ : Formula n
    ⊥ : Formula n
    _⇒_ : Formula n → Formula n → Formula n
    _∧_ : Formula n → Formula n → Formula n
    _∨_ : Formula n → Formula n → Formula n
    ∃⟨_⟩ : Formula (suc n) → Formula n
    ∀⟨_⟩ : Formula (suc n) → Formula n
    _==_ : Term n → Term n → Formula n

  ¬_ : Formula n → Formula n
  ¬ φ = φ ⇒ ⊥

  _⇔_ : Formula n → Formula n → Formula n
  φ ⇔ ψ = φ ⇒ ψ ∧ ψ ⇒ φ

  infix 10 _==_
  infixr 2 _⇒_
  infix 3 _⇔_
  infix 5 ¬_
  infixr 4 _∧_
  infixr 4 _∨_
  infix 0 ∃-syntax
  infix 0 ∀-syntax
  infix 0 make-term-syntax
  infix 0 make-formula-syntax

  Sentence : Set ℓ
  Sentence = Formula 0

  Constant : Set ℓ
  Constant = Term 0

  funformula→formulasuc : ((∀ {k} → Term (suc k)) → Formula (suc n)) → Formula (suc n)
  funformula→formulasuc {n} φ = φ (λ {k} → var (Fin.fromℕ< (lemma k n))) where
  
    lemma : ∀ k n → suc (k ∸ n) ≤ (suc k)
    lemma k zero = ≤-refl
    lemma zero (suc n) = ≤-refl
    lemma (suc k) (suc n) = s≤s (≤-trans (n≤1+n _) (lemma k n))

  ∃-syntax : ((∀ {k} → Term (suc k)) → Formula (suc n)) → Formula n
  ∃-syntax {n} φ = ∃⟨ funformula→formulasuc φ ⟩

  syntax ∃-syntax (λ x → φ) = ∃[ x ] φ

  ∀-syntax : ((∀ {k} → Term (suc k)) → Formula (suc n)) → Formula n
  ∀-syntax {n} φ = ∀⟨ funformula→formulasuc φ ⟩

  syntax ∀-syntax (λ x → φ) = ∀[ x ] φ 

  private

    list-vars : Vec (∀ {k} → ⦃ True (n ≤? k) ⦄ → Term k) n
    list-vars = tabulate λ i ⦃ wit ⦄ →
      var (Fin.opposite (Fin.inject≤ i (toWitness wit)))

  make-term : (Vec (∀ {k} → ⦃ True (n ≤? k) ⦄ → Term k) n → Term n)
            → Term n
  make-term f = f list-vars

  make-formula : (Vec (∀ {k} → ⦃ True (n ≤? k) ⦄ → Term k) n → Formula n)
               → Formula n
  make-formula f = f list-vars

  make-term-syntax : ∀ n → ((∀ {k} → ⦃ True (n ≤? k) ⦄ → Term k) ^ n → Term n)
                   → Term n
  make-term-syntax n f = make-term (f ∘ RecVec.fromVec)

  syntax make-term-syntax n (λ v → t) = term-in n free-vars v ꞉ t -- \:4 in emacs

  make-formula-syntax : ∀ n
                      → ((∀ {k} → ⦃ True (n ≤? k) ⦄ → Term k) ^ n → Formula n)
                      → Formula n
  make-formula-syntax n f = make-formula (f ∘ RecVec.fromVec)

  syntax make-formula-syntax n (λ v → φ) = formula-in n free-vars v ꞉ φ

  -- It works as expected

  module _ (P : ∀ {n} → Term n → Formula n) where private

    test₁ : _≡_ {A = Sentence} (∃[ x ] ∃[ y ] x == y) (∃⟨ ∃⟨ var 1F == var 0F ⟩ ⟩)
    test₁ = refl

    test₂ : _≡_ {A = Sentence}
            (∃[ x ] P x ∧ (∀[ y ] P y ⇒ x == y))
            (∃⟨ P (var 0F) ∧ ∀⟨ P (var 0F) ⇒ var 1F == var 0F ⟩ ⟩)
    test₂ = refl

    test₃ : _≡_ {A = Formula 2} (
              formula-in 2 free-vars (x , y) ꞉ x == y
            ) (var 1F == var 0F)
    test₃ = refl

  ∃-closure : Formula n → Sentence
  ∃-closure {zero} φ = φ
  ∃-closure {suc n} φ = ∃-closure {n} ∃⟨ φ ⟩

  ∀-closure : Formula n → Sentence
  ∀-closure {zero} φ = φ
  ∀-closure {suc n} φ = ∀-closure {n} ∀⟨ φ ⟩

  private

    mapFin : (Fin n → Fin m) → Fin (suc n) → Fin (suc m)
    mapFin f 0F = 0F
    mapFin f (suc i) = suc (f i)

  permute-vars-term : (Fin n → Fin m) → Term n → Term m
  permute-vars-term f = term-rec (λ i → var (f i)) (λ f _ v → fun f v)

  permute-vars-formula : (Fin n → Fin m) → Formula n → Formula m
  permute-vars-formula f (rel r v) = rel r (map (permute-vars-term f) v)
  permute-vars-formula f ⊤ = ⊤
  permute-vars-formula f ⊥ = ⊥
  permute-vars-formula f (φ ⇒ ψ) = permute-vars-formula f φ ⇒ permute-vars-formula f ψ
  permute-vars-formula f (φ ∧ ψ) = permute-vars-formula f φ ∧ permute-vars-formula f ψ
  permute-vars-formula f (φ ∨ ψ) = permute-vars-formula f φ ∨ permute-vars-formula f ψ
  permute-vars-formula f ∃⟨ φ ⟩ = ∃⟨ permute-vars-formula (mapFin f) φ ⟩
  permute-vars-formula f ∀⟨ φ ⟩ = ∀⟨ permute-vars-formula (mapFin f) φ ⟩
  permute-vars-formula f (x == y) = permute-vars-term f x == permute-vars-term f y

  module _ (P : Relation 2) where private

    apP : Term n → Term n → Formula n
    apP x y = rel P (x ∷ [ y ])

    test₁ : permute-vars-formula Fin.opposite (
              formula-in 2 free-vars (x , y) ꞉
                apP x y ∧ (∀[ z ] apP x z ⇒ y == z)
            ) ≡ (
              formula-in 2 free-vars (y , x) ꞉
                apP x y ∧ (∀[ z ] apP x z ⇒ y == z)
            )
    test₁ = refl

  inject-term : Term n → Term (m + n)
  inject-term = permute-vars-term (_ Fin.↑ʳ_)

  inject-formula : Formula n → Formula (m + n)
  inject-formula = permute-vars-formula (_ Fin.↑ʳ_)

  subst-term : Term n → Vec (Term m) n → Term m
  subst-term t μ = term-rec (lookup μ) (λ f _ v → fun f v) t

  subst-formula : Formula n → Vec (Term m) n → Formula m
  subst-formula (rel r v) μ = rel r (map (λ t → subst-term t μ) v)
  subst-formula ⊤ μ = ⊤
  subst-formula ⊥ μ = ⊥
  subst-formula (φ ⇒ ψ) μ = subst-formula φ μ ⇒ subst-formula ψ μ
  subst-formula (φ ∧ ψ) μ = subst-formula φ μ ∧ subst-formula ψ μ
  subst-formula (φ ∨ ψ) μ = subst-formula φ μ ∨ subst-formula ψ μ
  subst-formula ∃⟨ φ ⟩ μ = ∃⟨ subst-formula φ (var 0F ∷ map inject-term μ) ⟩
  subst-formula ∀⟨ φ ⟩ μ = ∀⟨ subst-formula φ (var 0F ∷ map inject-term μ) ⟩
  subst-formula (x == y) μ = subst-term x μ == subst-term y μ

  isAtomicᵇ : Formula n → Bool
  isAtomicᵇ (rel r v) = true
  isAtomicᵇ ⊤ = true
  isAtomicᵇ ⊥ = true
  isAtomicᵇ (φ ⇒ ψ) = isAtomicᵇ φ and isAtomicᵇ ψ
  isAtomicᵇ (φ ∧ ψ) = isAtomicᵇ φ and isAtomicᵇ ψ
  isAtomicᵇ (φ ∨ ψ) = isAtomicᵇ φ and isAtomicᵇ ψ
  isAtomicᵇ ∃⟨ φ ⟩ = false
  isAtomicᵇ ∀⟨ φ ⟩ = false
  isAtomicᵇ (x == y) = true

  record Structure : Set (lsuc ℓ) where
    field
      Domain : Set ℓ
      apfun : Function n → Vec Domain n → Domain
      aprel : Relation n → Vec Domain n → Set ℓ

  module Interpretation (S : Structure) where

    open Structure S

    interpret-term : Vec Domain n → Term n → Domain
    interpret-term μ = term-rec (lookup μ) λ f _ v → apfun f v

    interpret-formula : Vec Domain n → Formula n → Set ℓ
    interpret-formula μ (rel r v) = aprel r (map (interpret-term μ) v)
    interpret-formula μ ⊤ = Unit
    interpret-formula μ ⊥ = Empty
    interpret-formula μ (φ ⇒ ψ) = interpret-formula μ φ → interpret-formula μ ψ
    interpret-formula μ (φ ∧ ψ) = interpret-formula μ φ × interpret-formula μ ψ
    interpret-formula μ (φ ∨ ψ) = interpret-formula μ φ ⊎ interpret-formula μ ψ
    interpret-formula μ ∃⟨ φ ⟩ = Σ[ x ∈ Domain ] interpret-formula (x ∷ μ) φ
    interpret-formula μ ∀⟨ φ ⟩ = (x : Domain) → interpret-formula (x ∷ μ) φ
    interpret-formula μ (x == y) = interpret-term μ x ≡ interpret-term μ y

    evaluate : Constant → Domain
    evaluate = interpret-term []

    proof : Sentence → Set ℓ
    proof = interpret-formula []

record Theory (ℓ : Level) : Set (lsuc ℓ) where
  field
    sig : Signature ℓ

  open Signature sig public
  open Types sig

  field
    AxiomSet : Set ℓ
    axiom : AxiomSet → Sentence

record Model (T : Theory ℓ) : Set (lsuc ℓ) where
  open Theory T
  open Types sig
  
  field 
    struct : Structure

  open Structure struct public
  open Interpretation struct

  field
    axioms-proof : ∀ i → proof (axiom i)

module Examples where

  open Theory
  open Signature

  module OrderedAbGroup where
  
    OrderedAbGroupSig : Signature 0ℓ
    OrderedAbGroupSig .Function 0 = Unit
    OrderedAbGroupSig .Function 1 = Unit
    OrderedAbGroupSig .Function 2 = Unit
    OrderedAbGroupSig .Function _ = Empty
    OrderedAbGroupSig .Relation 2 = Unit
    OrderedAbGroupSig .Relation _ = Empty

    open Types OrderedAbGroupSig

    private
      e : Term n
      e = fun tt []

      -_ : Term n → Term n
      - x = fun tt [ x ]

      _+_ : Term n → Term n → Term n
      x + y = fun tt (x ∷ [ y ])

      _≤_ : Term n → Term n → Formula n
      x ≤ y = rel tt (x ∷ [ y ])

    OrderedAbGroupAxioms : Fin 8 → Sentence
    OrderedAbGroupAxioms 0F = -- Associativity
      ∀[ x ] ∀[ y ] ∀[ z ] ((x + y) + z) == (x + (y + z))
    OrderedAbGroupAxioms 1F = -- Identity
      ∀[ x ] (x + e) == x
    OrderedAbGroupAxioms 2F = -- Inverse
      ∀[ x ] (x + (- x)) == e
    OrderedAbGroupAxioms 3F = -- Commutativity
      ∀[ x ] ∀[ y ] (x + y) == (y + x)
    OrderedAbGroupAxioms 4F = -- Reflexivity
      ∀[ x ] x ≤ x
    OrderedAbGroupAxioms 5F = -- Antisymmetry
      ∀[ x ] ∀[ y ] (x ≤ y) ⇒ (y ≤ x) ⇒ (x == y)
    OrderedAbGroupAxioms 6F = -- Transitivity
      ∀[ x ] ∀[ y ] ∀[ z ] (x ≤ y) ⇒ (y ≤ z) ⇒ (x ≤ z)
    OrderedAbGroupAxioms 7F = -- Translation-invariance
      ∀[ x ] ∀[ y ] ∀[ z ] (x ≤ y) ⇒ ((x + z) ≤ (y + z))

    OrderedAbGroup : Theory 0ℓ
    OrderedAbGroup .sig = OrderedAbGroupSig
    OrderedAbGroup .AxiomSet = Fin 8
    OrderedAbGroup .axiom = OrderedAbGroupAxioms

  module Peano where

    PeanoSig : Signature 0ℓ
    PeanoSig .Function 0 = Unit
    PeanoSig .Function 1 = Unit
    PeanoSig .Function 2 = Fin 2
    PeanoSig .Function _ = Empty
    PeanoSig .Relation n = Empty

    open Types PeanoSig

    private    
      z : Term n
      z = fun tt []

      s : Term n → Term n
      s x = fun tt [ x ]

      _+_ : Term n → Term n → Term n
      x + y = fun 0F (x ∷ [ y ])

      _·_ : Term n → Term n → Term n
      x · y = fun 1F (x ∷ [ y ])

      _≤_ : Term n → Term n → Formula n
      x ≤ y = ∃[ k ] (inject-term x + k) == (inject-term y)

    Peano : Theory 0ℓ
    Peano .sig = PeanoSig
    Peano .AxiomSet = Fin 6 ⊎ Formula 1
    Peano .axiom (inj₁ 0F) = ∀[ x ] ¬ s x == z
    Peano .axiom (inj₁ 1F) = ∀[ x ] ∀[ y ] s x == s y ⇒ x == y
    Peano .axiom (inj₁ 2F) = ∀[ x ] x + z == x
    Peano .axiom (inj₁ 3F) = ∀[ x ] ∀[ y ] x + s y == s (x + y)
    Peano .axiom (inj₁ 4F) = ∀[ x ] x · z == z
    Peano .axiom (inj₁ 5F) = ∀[ x ] ∀[ y ] x · s y == (x · y) + x
    Peano .axiom (inj₂ φ) = subst-formula φ [ z ]
                          ⇒ (∀[ x ] subst-formula φ [ x ] ⇒ subst-formula φ [ s x ])
                          ⇒ (∀[ x ] subst-formula φ [ x ])

  module OrderedAbGroupInt where

    open OrderedAbGroup

    open Model
    open Types (OrderedAbGroup .sig)
    open Structure

    open import Data.Integer
    open import Data.Integer.Properties

    OrderedAbGroupInt : Model OrderedAbGroup
    OrderedAbGroupInt .struct .Domain = ℤ
    OrderedAbGroupInt .struct .apfun {0} _ [] = +0
    OrderedAbGroupInt .struct .apfun {1} _ [ x ] = - x
    OrderedAbGroupInt .struct .apfun {2} _ (x ∷ [ y ]) = x + y
    OrderedAbGroupInt .struct .aprel {2} _ (x ∷ [ y ]) = x ≤ y
    OrderedAbGroupInt .axioms-proof 0F = +-assoc
    OrderedAbGroupInt .axioms-proof 1F = +-identityʳ
    OrderedAbGroupInt .axioms-proof 2F = +-inverseʳ
    OrderedAbGroupInt .axioms-proof 3F = +-comm
    OrderedAbGroupInt .axioms-proof 4F x = ≤-refl
    OrderedAbGroupInt .axioms-proof 5F x y = ≤-antisym
    OrderedAbGroupInt .axioms-proof 6F x y z = ≤-trans
    OrderedAbGroupInt .axioms-proof 7F x y z = +-monoˡ-≤ z

  module PeanoNat where

    open Peano

    open Model
    open Types (Peano .sig)
    open Structure

    open Data.Nat
    open Data.Nat.Properties

    Peanoℕ : Model Peano
    Peanoℕ .struct .Domain = ℕ
    Peanoℕ .struct .apfun {0} tt [] = 0
    Peanoℕ .struct .apfun {1} tt [ x ] = suc x
    Peanoℕ .struct .apfun {2} 0F (x ∷ [ y ]) = x + y
    Peanoℕ .struct .apfun {2} 1F (x ∷ [ y ]) = x * y
    Peanoℕ .axioms-proof (inj₁ 0F) x = Level.lift ∘ 1+n≢0
    Peanoℕ .axioms-proof (inj₁ 1F) x y = suc-injective
    Peanoℕ .axioms-proof (inj₁ 2F) = +-identityʳ
    Peanoℕ .axioms-proof (inj₁ 3F) = +-suc
    Peanoℕ .axioms-proof (inj₁ 4F) = *-zeroʳ
    Peanoℕ .axioms-proof (inj₁ 5F) x y = trans (*-suc x y) (+-comm x _)
    Peanoℕ .axioms-proof (inj₂ ϕ) = proof where postulate proof : _
