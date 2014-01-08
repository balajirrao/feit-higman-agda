module Misc where
  open import Data.Nat
  open import Relation.Binary.PropositionalEquality
  open import Data.Empty
  open import Data.Sum
  
  module EvenOdd where
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

  open EvenOdd public

  m≤m : ∀ {m} → m ≤ m
  m≤m {zero} = z≤n
  m≤m {suc m} = s≤s m≤m

  +-suc : ∀ a b → suc a + b ≡ a + suc b
  +-suc zero b = refl
  +-suc (suc a) b = cong suc (+-suc a b)
  
  +-com : ∀ a b → a + b ≡ b + a
  +-com zero zero = refl
  +-com zero (suc b) rewrite +-com b 0 = refl
  +-com (suc a) b = trans (cong suc (+-com a b)) (+-suc b a)
  
