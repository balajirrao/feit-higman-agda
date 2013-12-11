module IncidenceGeometry (O : Set) (_#_ : O → O → Set) where
  open import Data.Nat
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
  open import Data.Product
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  postulate
    #-refl : ∀ {e} → e # e
    #-sym : ∀ {e f} → e # f → f # e

  data chain : O → O → Set
  --hd : ∀ {n} → chain n → O
  
  data chain where
    chain-inc : {e f : O} (_ : e # f) → chain e f -- Simple chain, formed by incidence
    chain-ext : ∀ {e₀ e₁ e₂} (_ : chain e₀ e₁) (_ : e₁ # e₂) → chain e₀ e₂ -- chain extension 
  
  data _∈_ : {e f : O} → O → chain e f → Set where
    head : ∀ {e f} (c : chain e f) → e ∈ c
    last : ∀ {e f} (c : chain e f) → f ∈ c
    ext : ∀ {e₀ e₁ e₂} (c : chain e₀ e₁) (p : e₁ # e₂) → e₂ ∈ (chain-ext {e₀} {e₁} {e₂} c p)
    
  len : {e f : O} → chain e f → ℕ
  len (chain-inc _) = suc zero
  len (chain-ext c _) = suc (len c)
  
  last-but-one : ∀ {e f} (c : chain e f) → O
  last-but-one (chain-inc {e} {f} x) = e
  last-but-one (chain-ext {e₀} {e₁} {e₂} c x) = e₁

  data irred : {e f : O} → chain e f → Set where
    irred-inc : ∀ {e f} → (e ≡ f → ⊥) → (e#f : e # f) → irred (chain-inc e#f)
    irred-ext : ∀ {e₀ e₁ e₂} → (c : chain e₀ e₁) → irred c →
                  (e₁#e₂ : e₁ # e₂) → ((last-but-one c) # e₂ → ⊥) →
                  irred (chain-ext c e₁#e₂)

  -- Since we are dealing with finite objects here we assume that a shortest chain always exists
  postulate
    shortest-chain : (e f : O) → chain e f
    shortest-chain-is-shortest : ∀ {e f} → {c : chain e f} → (len (shortest-chain e f) ≤ len c)
  
