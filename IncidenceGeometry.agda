module IncidenceGeometry (O : Set) (_#_ : O → O → Set) where
  open import Data.Nat hiding (_<_)
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
  open import Data.Product
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Data.Maybe

  postulate
    #-refl : ∀ {e} → e # e
    #-sym : ∀ {e f} → e # f → f # e

  data chain : O → O → Set
  --hd : ∀ {n} → chain n → O
  
  data chain where
    chain-zero : ∀ {e f} (e#f : e # f) → chain e f -- Simple chain, formed by incidence
    chain-suc : ∀ {e₀ e₁ e₂} (c : chain e₀ e₁) (e₁#e₂ : e₁ # e₂) → chain e₀ e₂ -- chain extension 
  
  len : {e f : O} → chain e f → ℕ
  len (chain-zero _) = suc zero
  len (chain-suc c _) = suc (len c)

  join : ∀ {e₀ e₁ e₂} (c₁ : chain e₀ e₁) (c₂ : chain e₁ e₂) → chain e₀ e₂
  join c₁ (chain-zero e₁#e₂) = chain-suc c₁ e₁#e₂
  join c₁ (chain-suc c₂ e₁#e₂) = chain-suc (join c₁ c₂) e₁#e₂
  
  reverse : ∀ {e f} → chain e f → chain f e
  reverse (chain-zero {e} {f} e#f) = chain-zero (#-sym e#f)
  reverse (chain-suc {e₀} {e₁} {e₂} c e₁#e₂) = join (chain-zero (#-sym e₁#e₂)) (reverse c)
  
  infix 4 _≺_ _≻_

  data _≺_ : ∀ {e f : O} (x y : O) → {x#y : x # y} {c : chain e f} → Set where
    ≺-zero : ∀ {e f} → (e#f : e # f) → (e ≺ f) {e#f} {chain-zero e#f}
    ≺-suc : ∀ {e₀ e₁ e₂} (c : chain e₀ e₁) (e₁#e₂ : e₁ # e₂) → (e₁ ≺ e₂) {e₁#e₂} {chain-suc c e₁#e₂}
  
  _≻_ : ∀ {e f} (x y : O) {x#y : x # y} {c : chain e f} → Set
  _≻_ x y {x#y} {c} = (y ≺ x) {#-sym x#y} {reverse c}

  next-elem : ∀ {e f y} {c : chain e f} {x : O} {x#y : x # y} (x≺y : (x ≺ y) {x#y} {c}) → O
  next-elem {y = y} x≺y = y

  prev-elem : ∀ {e f x} {c : chain e f} {y : O} {x#y : x # y} (x≻y : (x ≻ y) {x#y} {c}) → O
  prev-elem {x = x} x≻y = x

  data irred : {e f : O} (c : chain e f) → Set where
    irred-zero : ∀ {e f} → (e≠f : e ≡ f → ⊥) → (e#f : e # f) → irred (chain-zero e#f) 
    irred-suc : ∀ {e₀ e₁ e₂ e₃ e₁#e₂} (c : chain e₀ e₂) (e₂#e₃ : e₂ # e₃)
                  (e₁≺e₂ : (e₁ ≺ e₂) {e₁#e₂} {c}) (¬e₁#e₃ : (e₁ # e₃) → ⊥) → irred (chain-suc c e₂#e₃)
    
  -- Since we are dealing with finite objects here we assume that a shortest chain always exists
  postulate
    shortest-chain : (e f : O) → chain e f
    shortest-chain-is-shortest : ∀ {e f} → {c : chain e f} → (len (shortest-chain e f) ≤ len c)
