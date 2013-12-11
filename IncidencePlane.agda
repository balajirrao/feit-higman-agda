module IncidencePlane where
  open import Data.Nat
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
  open import Data.Product
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Data.Sum using (_⊎_) renaming (inj₁ to injP; inj₂ to injL)
  
  postulate
    P : Set
    L : Set

  O : Set
  O = P ⊎ L
 
  postulate
    _#_ : O → O → Set
    point-#-sym : {e f : P} → (injP e) # (injP f) → e ≡ f
    line-#-sym : {e f : L} → (injL e) # (injL f) → e ≡ f

  open import IncidenceGeometry O _#_

  alternates : (e f : O) → Set
  alternates e f with e | f
  ... | (injP _) | (injP _) = ⊥
  ... | (injL _) | (injL _) = ⊥
  ... | (injL _) | (injP _) = ⊤
  ... | (injP _) | (injL _) = ⊤

  alternating-chain : ∀ {e f : O} (c : chain e f) → Set
  alternating-chain (chain-inc {e} {f} _) = alternates e f
  alternating-chain (chain-ext {e₀} {e₁} c {e₂} p )  = alternating-chain c × alternates e₁ e₂

  --irred-chain-alternates : ∀ {e f} (c : chain e f) {_ : irred c} → alternating-chain c
  --irred-chain-alternates c = {!!}
