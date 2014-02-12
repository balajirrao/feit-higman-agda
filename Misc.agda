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
      evenSuc : ∀ {m} → Even m → Even (suc (suc m))

      
    
    data Odd where
      oddOne : Odd 1
      oddSuc : ∀ {m} → Odd m → Odd (suc (suc m))
     
    evenOdd : {n : ℕ} → Even n → Odd (suc n)
    evenOdd evenZero = oddOne
    evenOdd (evenSuc p) = oddSuc (evenOdd p)

    oddEven : {n : ℕ} → Odd n → Even (suc n)
    oddEven oddOne = evenSuc evenZero
    oddEven (oddSuc p) = evenSuc (oddEven p)

    eitherEvenOdd : ∀ x → Even x → Odd x → ⊥
    eitherEvenOdd .0 evenZero ()
    eitherEvenOdd .(suc (suc m)) (evenSuc {m} p) (oddSuc q) = eitherEvenOdd m p q

    evenOddDec : ∀ m → (Even m) ⊎ (Odd m)
    evenOddDec zero = inj₁ evenZero
    evenOddDec (suc m) with (evenOddDec m)
    evenOddDec (suc m) | inj₁ x = inj₂ (evenOdd x)
    evenOddDec (suc m) | inj₂ y = inj₁ (oddEven y)

    odd≡ : ∀ {x y} → x ≡ y → Odd x → Odd y
    odd≡ refl p = p

    even≡ : ∀ {x y} → x ≡ y → Even x → Even y
    even≡ refl p = p

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
 
  suc-≤ : ∀ {x y} → suc x ≤ suc y → x ≤ y
  suc-≤ (s≤s p) = p

  n≤pred : ∀ {n} → pred n ≤ n
  n≤pred {zero} = z≤n
  n≤pred {suc n} = n≤suc

  ≤≡ : ∀ {x y z} → x ≡ y → z ≤ x → z ≤ y
  ≤≡ refl q = q
  
  ≡⇒≤ : ∀ {x y} → x ≡ y → x ≤ y
  ≡⇒≤ refl = m≤m

  div2 : ∀ {n} → Even n → ℕ
  div2 evenZero = zero
  div2 (evenSuc q) = suc (div2 q) 
 
  ≤≢⇒< : ∀ {x y} → x ≤ y → x ≢ y → x < y
  ≤≢⇒< {.0} {zero} z≤n q = ⊥-elim (q refl)
  ≤≢⇒< {.0} {suc y} z≤n q = s≤s z≤n
  ≤≢⇒< (s≤s p) q = s≤s (≤≢⇒< p (λ z → q (cong suc z)))

  ≤-≥⇒≡ : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y
  ≤-≥⇒≡ z≤n z≤n = refl
  ≤-≥⇒≡ (s≤s p) (s≤s q) = cong suc (≤-≥⇒≡ p q)

  <-≡-trans : ∀ {x y z} →  x ≡ y → y ≥ z → x ≥ z
  <-≡-trans refl q = q

  suc∘pred≡id : ∀ {x} → (x > 0) → (suc (pred x)) ≡ x
  suc∘pred≡id (s≤s g) = refl

  div2*2 : ∀ {n} (p : Even n) → (div2 p) * 2 ≡ n
  div2*2 evenZero = refl
  div2*2 (evenSuc {n} x) = cong (λ z → suc (suc z)) (div2*2 x)


  div2≤ : ∀ {n} → (p : Even n) → (div2 p) ≤ n
  div2≤ evenZero = z≤n
  div2≤ (evenSuc {n} x)
              = s≤s (begin div2 x ≤⟨ div2≤ x ⟩ relTo (n≤suc))

