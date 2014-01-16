module Misc where
  open import Data.Nat
  open import Relation.Binary.PropositionalEquality
  open import Data.Empty
  open import Data.Sum
  
  open Data.Nat.≤-Reasoning

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

  n≤suc : ∀ {n} → n ≤ suc n
  n≤suc {zero} = z≤n
  n≤suc {suc n} = s≤s n≤suc
 
  div2 : ∀ {n} → Even n → ℕ
  div2 evenZero = 0
  div2  (oddEven (evenOdd {n} x)) = suc (div2 x)
  
  div2*2 : ∀ {n} → (p : Even n) → 2 * (div2 p) ≡ n
  div2*2  evenZero = refl
  div2*2 (oddEven (evenOdd {n} x))
               rewrite sym(+-suc (div2 x) (div2 x + 0)) =
                                       cong suc (cong suc (div2*2 x))

  div2≤ : ∀ {n} → (p : Even n) → (div2 p) ≤ n
  div2≤ evenZero = z≤n
  div2≤ (oddEven (evenOdd {n} x))
              = s≤s (begin div2 x ≤⟨ div2≤ x ⟩ relTo (n≤suc))
 
