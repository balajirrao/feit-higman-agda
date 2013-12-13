module IncidencePlane where
  open import Data.Bool using (Bool; true; false)
  open import Data.Nat
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Product
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
  open import Data.Sum using (_⊎_) renaming (inj₁ to injP; inj₂ to injL)
  open import Data.Maybe
  
  postulate
    P : Set
    L : Set

  O : Set
  O = P ⊎ L
 
  isP : O → Bool
  isP (injP x) = true
  isP (injL y) = false

  isL : O → Bool
  isL (injP x) = false
  isL (injL y) = true

  
  postulate
    _#_ : O → O → Set
    eq-#-P : {e f : P} → (injP e) # (injP f) → e ≡ f
    eq-#-L : {e f : L} → (injL e) # (injL f) → e ≡ f

  
  import IncidenceGeometry O _#_ as IG
  open IG

  irred-alt-P : ∀ {e f x y} {c : chain e f} (ic : irred c) (x#y : (injP x) # y) (x≺y : ((injP x) ≺ y) {x#y} {c} ) → (isL y ≡ true)
  irred-alt-P ic x#y x≺y with (next-elem x≺y)
  irred-alt-P {x = x} (irred-zero e≠f .x#y) x#y (≺-zero .x#y) | injP p = ⊥-elim (e≠f (cong injP (eq-#-P x#y)))
  irred-alt-P {e = e₀} .{injP e₃} {x = e₂} (irred-suc {e₁ = e₁} {e₁#e₂ = e₁#e₂} .c .e₂#e₃ e₁≺e₂ ¬e₁#e₃) e₂#e₃ (≺-suc c .e₂#e₃) | injP e₃ =
                       ⊥-elim (¬e₁#e₃ (subst (λ t → e₁ # t) (cong injP (eq-#-P e₂#e₃)) e₁#e₂))
  ... | (injL l) = refl

  
  irred-alt-L : ∀ {e f x y} {c : chain e f} (ic : irred c) (x#y : (injL x) # y) (x≺y : ((injL x) ≺ y) {x#y} {c} )  → (isP y ≡ true)
  irred-alt-L ic x#y x≺y with (next-elem x≺y)
  irred-alt-L {x = x} (irred-zero e≠f .x#y) x#y (≺-zero .x#y) | injL p = ⊥-elim (e≠f (cong injL (eq-#-L x#y)))
  irred-alt-L {e = e₀} .{injL e₃} {x = e₂} (irred-suc {e₁ = e₁} {e₁#e₂ = e₁#e₂} .c .e₂#e₃ e₁≺e₂ ¬e₁#e₃) e₂#e₃ (≺-suc c .e₂#e₃) | injL e₃ =
                       ⊥-elim (¬e₁#e₃ (subst (λ t → e₁ # t) (cong injL (eq-#-L e₂#e₃)) e₁#e₂))
  ... | (injP p) = refl
  
  
  
  module EvenOdd where

    open import Data.Nat

    data Even : ℕ → Set where
      evenZero : Even 0
      evenSuc : {n : ℕ} → Even n → Even (suc (suc n))
    
    data Odd : ℕ → Set where
      oddOne : Odd 1
      oddSuc : {n : ℕ} → Odd n → Odd (suc (suc n))

  open EvenOdd

  
