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
    chain-ext : ∀ {e₀ e₁ e₂} (c : chain e₀ e₁) (e₁#e₂ : e₁ # e₂) → chain e₀ e₂ -- chain extension 
  
  data _∈_ : {e f : O} → O → chain e f → Set where
    ∈-head : ∀ {e f} (e#f : e # f) → e ∈ chain-inc e#f
    ∈-last : ∀ {e f} → (e#f : e # f) → f ∈ chain-inc e#f
    ∈-ext-tail : ∀ {e₀ e₁ e₂} (c : chain e₀ e₁) → (e₁#e₂ : e₁ # e₂) → e₂ ∈ (chain-ext c e₁#e₂) 
    ∈-ext-init : ∀ {e₀ e₁ e₂ x} (c : chain e₀ e₁) (e₁#e₂ : e₁ # e₂) → x ∈ c → x ∈ (chain-ext c e₁#e₂)
    
  len : {e f : O} → chain e f → ℕ
  len (chain-inc _) = suc zero
  len (chain-ext c _) = suc (len c)
  
  last-but-one : ∀ {e f} (c : chain e f) → O
  last-but-one (chain-inc {e} {f} x) = e
  last-but-one (chain-ext {e₀} {e₁} {e₂} c x) = e₁

  data irred : {e f : O} → chain e f → Set where
    irred-inc : ∀ {e f} → (e≠f : e ≡ f → ⊥) → (e#f : e # f) → irred (chain-inc e#f)
    irred-ext : ∀ {e₀ e₁ e₂} → (c : chain e₀ e₁) → irred c →
                  (e₁#e₂ : e₁ # e₂) → ((last-but-one c) # e₂ → ⊥) →
                  irred (chain-ext c e₁#e₂)

  next-elem : ∀ {e f x} → {c : chain e f} → x ∈ c → O
  next-elem {e} {f} {x} {chain-inc e#f} p = f
  next-elem {e} {.x} {x} {chain-ext c e₁#x} (∈-ext-tail .c .e₁#x) = x
  next-elem {e} {f} {x} {chain-ext c e₁#f} (∈-ext-init .c .e₁#f p) = next-elem p

  next-elem-∈ : ∀ {e f} → {x : O} → {c : chain e f} → (p : x ∈ c) → (next-elem p) ∈ c
  next-elem-∈ {e} {f} {x} {chain-inc e#f} p = ∈-last e#f
  next-elem-∈ {e} {.x} {x} {chain-ext c e₁#e₂} (∈-ext-tail .c .e₁#e₂) = ∈-ext-tail c e₁#e₂
  next-elem-∈ {e} {f} {x} {chain-ext c e₁#e₂} (∈-ext-init .c .e₁#e₂ p) = ∈-ext-init c e₁#e₂ (next-elem-∈ p)

  next-elem-# : ∀ {e f} → {x : O} → {c : chain e f} → (p : x ∈ c) → x # (next-elem p)
  next-elem-# {.x} {f} {x} {chain-inc x#f} (∈-head .x#f) = x#f
  next-elem-# {e} {.x} {x} {chain-inc e#f} (∈-last .e#f) = #-refl
  next-elem-# {e} {.x} {x} {chain-ext c e₁#e₂} (∈-ext-tail .c .e₁#e₂) = #-refl
  next-elem-# {e} {f} {x} {chain-ext c e₁#e₂} (∈-ext-init .c .e₁#e₂ p) = next-elem-# p

  -- Since we are dealing with finite objects here we assume that a shortest chain always exists
  postulate
    shortest-chain : (e f : O) → chain e f
    shortest-chain-is-shortest : ∀ {e f} → {c : chain e f} → (len (shortest-chain e f) ≤ len c)


