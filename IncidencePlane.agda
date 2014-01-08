module IncidencePlane where
  open import Data.Bool using (Bool; true; false)
  open import Data.Nat
  open import Data.Unit using (⊤; tt)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Product
  open import
    Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; subst₂; sym; trans; _≢_)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Maybe

  open import Relation.Nullary.Core
 
  --private
  postulate
    P L : Set
    
  O : Set
  O = P ⊎ L
 
  isP : O → Bool
  isP (inj₁ x) = true
  isP (inj₂ y) = false

  isL : O → Bool
  isL (inj₁ x) = false
  isL (inj₂ y) = true

  infix 3 _#_
  
  postulate
    _#_ : O → O → Set
    eq-#-P : {e f : P} → .((inj₁ e) # (inj₁ f)) → e ≡ f
    eq-#-L : {e f : L} → .((inj₂ e) # (inj₂ f)) → e ≡ f

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

    eitherEvenOdd : ∀ x → Even x → Odd x → ⊥
    eitherEvenOdd zero e ()
    eitherEvenOdd (suc x) (oddEven p) (evenOdd q) = eitherEvenOdd x q p

    evenOddDec : ∀ m → (Even m) ⊎ (Odd m)
    evenOddDec zero = inj₁ evenZero
    evenOddDec (suc m) with (evenOddDec m)
    evenOddDec (suc m) | inj₁ x = inj₂ (evenOdd x)
    evenOddDec (suc m) | inj₂ y = inj₁ (oddEven y)

  open EvenOdd
 
  irred-PP-even : ∀ {p p'} → (c : chain (inj₁ p) (inj₁ p')) → irred c → Even (len c)
  irred-PL-odd : ∀ {p l} → (c : chain (inj₁ p) (inj₂ l)) → irred c → Odd (len c)

  irred-PP-even [ ._ ] _ = evenZero
  irred-PP-even {_} {p} ((c ∷ .(inj₁ p)) {q}) ic with (last c)
  ... | inj₁ x = ⊥-elim (irred-∷ c (inj₁ p) ic (cong inj₁ (eq-#-P q)))
  ... | inj₂ y = oddEven (irred-PL-odd c (irred-init (c ∷ inj₁ p) tt ic))

  irred-PL-odd {_} {l} ((c ∷ .(inj₂ l)) {q}) ic with (last c)
  ... | inj₁ _ = evenOdd (irred-PP-even c (irred-init (c ∷ inj₂ l) tt ic))
  ... | inj₂ y = ⊥-elim (irred-∷ c (inj₂ l) ic (cong inj₂ (eq-#-L q)))

  irred-LL-even : ∀ {l l'} → (c : chain (inj₂ l) (inj₂ l')) → irred c → Even (len c)
  irred-LL-even [ .(inj₂ _) ] x = evenZero
  irred-LL-even {_} {l'} ((c ∷ .(inj₂ l')) {q} ) ic with (last c)
  ... | inj₁ _ rewrite (len-rev c) = oddEven (irred-PL-odd (rev c) 
                                      (irred-rev c (irred-init (c ∷ inj₂ l')  tt ic)))
  ... | inj₂ _ = ⊥-elim (irred-∷ c (inj₂ l') ic (cong inj₂ (eq-#-L q)))
 
  shortest-PP-even : ∀ {p p'} → (c : chain (inj₁ p) (inj₁ p')) →
                       shortest c → Even (len c)
  shortest-PP-even c sc = irred-PP-even c (shortest-irred c sc)

  shortest-PL-odd : ∀ {p l} → (c : chain (inj₁ p) (inj₂ l)) →
                      shortest c → Odd (len c)
  shortest-PL-odd c sc = irred-PL-odd c (shortest-irred c sc)

  module GenPolygon (n : ℕ) where
    postulate
      A₁ : ∀ (e f : O) → ∃ {A = chain e f} (λ c → (len  c) ≤ n)
      A₂ : ∀ (e f : O) → (c₁ : chain e f) (c₂ : chain e f) → (len c₁ < n) → (len c₂ < n) → (c₁ ≡ c₂)
  
    open Data.Nat.≤-Reasoning
 
    len-shortest-≤n : ∀ {e f} → (c : chain e f) → shortest c → len c > n → ⊥
    len-shortest-≤n {e} {f} c sc l with proj₁ (A₁ e f) | proj₂(A₁ e f) 
    ... | c' | p  = sc c' (begin suc (len c') ≤⟨ s≤s p ⟩ (relTo l))

    nondegen : ∀ {e f} → Set
    nondegen {e} {f} = ∃ {A = chain e f} (λ c → shortest c × (len c) ≡ n)

    closed : ∀ {e f} (c : chain e f) → Set
    closed {.f} {f} IG.[ .f ] = ⊥
    closed {e} {f} (c IG.∷ .f) = f ≡ e

    closed-even : ∀ {e} → (c : chain e e) → irred c → Even (len c)
    closed-even {inj₁ _} c = irred-PP-even c
    closed-even {inj₂ _} c = irred-LL-even c    

    mid : ∀ {e f} → (c : chain e f) → Even (len c) → O
    mid [ e ] p = e
    mid ([ e ] ∷ f) (oddEven ())
    mid ([ e ] ∷ f ∷ g) p = f
    mid (((c ∷ f) {c#f}) ∷ g) (oddEven (evenOdd p)) = mid (init ((c ∷ f) {c#f}) tt) p
