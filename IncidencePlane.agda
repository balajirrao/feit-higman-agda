
module IncidencePlane where
  open import Data.Bool using (Bool; true; false)
  open import Data.Nat
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Product
  open import
    Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; subst₂; sym; trans; _≢_)
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

  infix 3 _#_
  
  postulate
    _#_ : O → O → Set
    eq-#-P : {e f : P} → (injP e) # (injP f) → e ≡ f
    eq-#-L : {e f : L} → (injL e) # (injL f) → e ≡ f

  import IncidenceGeometry as IG
  open IG O _#_

  module EvenOdd where

    open import Data.Nat

    data Even : ℕ → Set
    data Odd : ℕ → Set 

    data Even where
      evenZero : Even 0
      oddEven : {n : ℕ} → Odd n → Even (suc n)
    
    data Odd where
      evenOdd : {n : ℕ} → Even n → Odd (suc n)

    evenSuc : ∀ {m} → Even m → Even (suc (suc m))
    evenSuc {zero} p = oddEven (evenOdd p)
    evenSuc {suc m} p = oddEven (evenOdd p)
  
    oddSuc : ∀ {m} → Odd m → Odd (suc (suc m))
    oddSuc {zero} p = evenOdd (oddEven p)
    oddSuc {suc m} p = evenOdd (oddEven p)
  
    oddOne : Odd 1
    oddOne = evenOdd evenZero

  open EvenOdd
 
  irred-PP-even : ∀ {p p'} → (c : chain (injP p) (injP p')) → irred c → Even (len c)
  irred-PL-odd : ∀ {p l} → (c : chain (injP p) (injL l)) → irred c → Odd (len c)

  irred-PP-even [] ic = evenZero
  irred-PP-even (c ∷ e#f) ic with (fst e#f)
  irred-PP-even ([] ∷ e#f) ic | injP x = ⊥-elim (ic (cong injP (eq-#-P e#f)))
  irred-PP-even (c ∷ e#f ∷ e#f₁) ic | injP x = ⊥-elim (proj₁ ic (subst (λ m → fst e#f # m) (cong injP (eq-#-P e#f₁)) e#f))
  irred-PP-even (c ∷ e#f) ic | injL y = oddEven (irred-PL-odd c (irred-init (c ∷ e#f) (λ ()) ic))

  irred-PL-odd ([] ∷ e#f) _ = oddOne
  irred-PL-odd (c ∷ e#f ∷ e#f₁) ic with (last c)
  irred-PL-odd (c ∷ e#f ∷ e#f₁) ic | injP x with (snd e#f)
  irred-PL-odd (c ∷ e#f ∷ e#f₁) ic | injP x₁ | injP x = ⊥-elim (proj₁ ic (subst (λ m → m # snd e#f₁) (cong injP (eq-#-P (#-sym e#f))) e#f₁))
  irred-PL-odd (c ∷ e#f ∷ e#f₁) ic | injP x | injL y = ⊥-elim (proj₁ ic (subst (λ m → fst e#f # m) (cong injL (eq-#-L e#f₁)) e#f))
  irred-PL-odd (c ∷ e#f ∷ e#f₁) ic | injL y = oddSuc (irred-PL-odd c (irred-init (c ∷ e#f) (λ ()) (proj₂ ic)))

  shortest-PP-even : ∀ {p p'} → (c : chain (injP p) (injP p')) → shortest c → Even (len c)
  shortest-PP-even c sc = irred-PP-even c (shortest-irred c sc)

  shortest-PL-odd : ∀ {p l} → (c : chain (injP p) (injL l)) → shortest c → Odd (len c)
  shortest-PL-odd c sc = irred-PL-odd c (shortest-irred c sc)
