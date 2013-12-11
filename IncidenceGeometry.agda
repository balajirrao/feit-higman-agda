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
    chain-inc : {e f : O} → e # f → chain e f -- Simple chain, formed by incidence
    chain-ext : ∀ {e₀ e₁} (c : chain e₀ e₁) {e₂} (_ : e₁ # e₂) → chain e₀ e₂ -- chain extension 
  
  len : {e f : O} → chain e f → ℕ
  len (chain-inc _) = suc zero
  len (chain-ext c _) = suc (len c)
  
  head : {e f : O} → chain e f → O
  head {e} _ = e
  
  last : {e f : O} → chain e f → O
  last {_} {f} _ = f
  
  irred : {e f : O} → chain e f → Set
  irred (chain-inc {e} {f} _) = (e ≡ f → ⊥)
  irred (chain-ext {e₀} {e₂} c {e₃} _) with c
  ... | (chain-inc .{e₀} .{e₂} _) = e₀ # e₃ → ⊥
  ... | (chain-ext .{e₀} {e₁} _ .{e₂} _) = irred c × (e₁ # e₃ → ⊥)
  
  -- Since we are dealing with finite objects here we assume that a shortest chain always exists
  postulate
    shortest-chain : (e f : O) → chain e f
    shortest-chain-is-shortest : ∀ {e f} → {c : chain e f} → (len (shortest-chain e f) ≤ len c)
  
