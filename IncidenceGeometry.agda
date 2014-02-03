module IncidenceGeometry (O : Set) (_#_ : O → O → Set)
                         (#-refl : ∀ {e} → e # e)
                         (#-sym : ∀ {e f} → e # f → f # e) where
  open import Data.Nat
  open import Data.Unit using (⊤; tt)
  open import Data.Empty
  open import Data.Product
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; _≢_; subst; subst₂; sym; trans)
  open import Data.Maybe
  open import Data.Sum
  open import Data.Bool
  open import Relation.Binary
  open import Relation.Nullary.Core
  open import Misc

  infixr 5 _∷_   
  data chain : O → O → Set where
    [_] : (e : O) → chain e e
    _∷_ : ∀ {f g} (e : O) .{{e<>f : e ≡ f → ⊥}} .{{e#f : e # f}} (c : chain f g) → chain e g    

  len : ∀ {e f} (c : chain e f) → ℕ
  len [ _ ] = zero
  len (_ ∷ c) = suc (len c)

  data _∈_ : ∀ {e f} (x : O) (c : chain e f) → Set where
    ∈z : ∀ {e f} (c : chain e f) → e ∈ c
    ∈s : ∀ {e f x} (y : O) .{{y<>e : y ≡ e → ⊥}} (c : chain e f) .{{q : y # e}} (p : x ∈ c) → x ∈ (y ∷ c)

  nth : ∀ {e f n} (c : chain e f) (p : n ≤ (len c))  → O
  nth [ e ] z≤n = e
  nth (e ∷ _) z≤n = e
  nth (e#f ∷ c) (s≤s p) = nth c p
                                                                       
  data irred : ∀ {e f} (c : chain e f) → Set where
    iz : ∀ (e f g : O) .{{e<>f : e ≡ f → ⊥}} .{{f<>g : f ≡ g → ⊥}}
           .{{e#f : e # f}} .{{f#g : f # g}} (¬e#g : .(e # g) → ⊥) → irred (e ∷ f ∷ [ g ])
    is : ∀ {f g} (e : O) .{{e#f : e # f}} .{{e<>f : e ≡ f → ⊥}}
           (c : chain f g) (p : (len c) ≥ 1) (ic : irred c)
           (¬e#c : .(e # (nth c p)) → ⊥) → irred (e ∷ c) 

  nth-∈ : ∀ {e f n} (c : chain e f) (p : n ≤ (len c)) → (nth c p) ∈ c
  nth-∈ [ e ] z≤n = ∈z [ e ]
  nth-∈ (e ∷ c) z≤n = ∈z (e ∷ c)
  nth-∈ (e ∷ c) (s≤s p) = ∈s e c (nth-∈ c p)


  head : ∀ {e f} (c : chain e f) → O
  head {e} c = nth c z≤n

  last : ∀ {e f} (c : chain e f) → O
  last c = nth c m≤m

  tail : ∀ {e f} (c : chain e f) (p : (len c) ≥ 1) → chain (nth c p) f
  tail [ _ ] ()
  tail (e ∷ c) (s≤s p) with c
  tail {.e} {f} (e ∷ c) (s≤s z≤n) | [ .f ] = [ f ]
  tail (e ∷ c) (s≤s z≤n) | (g ∷ c') = c

  init : ∀ {e f} (c : chain e f) (p : (len c) ≥ 1) → chain e (nth {n = pred (len c)} c n≤pred)
  init [ _ ] ()
  init (e ∷ [ _ ]) (s≤s z≤n) = [ e ] 
  init (e#f ∷ e#f₁ ∷ c) (s≤s z≤n) = e#f ∷ init (e#f₁ ∷ c) (s≤s z≤n)

  infixl 5 _++_
  _++_ : ∀ {e f} (c : chain e f) (g : O) .{{f<>g : f ≡ g → ⊥}} .{{p : f # g}} → chain e g
  [ e ] ++ f = e ∷ [ f ] 
  (e#f ∷ c) ++ p = e#f ∷ (c ++ p)

{-
  rev : ∀ {e f} (c : chain e f) → chain f e
  rev [ e ] = [ e ]
  rev (e ∷ c) = {!rev c ++ e!}
-}
  -- Shortest chain --

  module ShortestPredicate where
    shortest : ∀ {e f} → (c : chain e f) → Set
    shortest {e} {f} c = (c' : chain e f) → ((len c) ≯ (len c'))

    -- Couple of obvious functions to deal with buggy pattern matching lambdas
    
    private F : ∀ {e f g} → (e ≡ f) → (c : chain f g) → chain e g
            F {e} refl c = c

    private G : ∀ {e f g} → (p : e ≡ f) (c : chain f g) → len (F p c) ≤ suc (len c)
            G refl c = n≤suc
  
    shortest-irred : ∀ {e f} (c : chain e f) (p : (len c) ≥ 2) → shortest c → irred c
    shortest-irred [ _ ] () sc
    shortest-irred (e ∷ [ _ ]) (s≤s ()) s
    shortest-irred (e ∷ f ∷ [ g ]) (s≤s (s≤s z≤n)) sc = iz e f g
                                   (λ e#g → sc (_∷_ e
                                     {{e<>f = λ e≡f → sc (F e≡f [ g ]) (s≤s (G e≡f [ g ]))}}
                                     {{e#f = e#g}} [ g ]) (s≤s (s≤s z≤n)))

    shortest-irred (e ∷ f ∷ g ∷ c) (s≤s (s≤s z≤n)) sc = is e (f ∷ g ∷ c) (s≤s z≤n)
                            (shortest-irred (f ∷ g ∷ c) (s≤s (s≤s z≤n))
                            (λ c' z → sc (e ∷ c') (s≤s z)))
                            (λ e#g → sc (_∷_ e
                               {{e<>f = λ e≡f → sc (F e≡f (g ∷ c)) (s≤s (G e≡f (g ∷ c)))}}
                               {{e#f = e#g}} (g ∷ c)) m≤m) 

  open ShortestPredicate public
{-

  mid : ∀ {e f n} (c : chain e f n) (p : Even n) → O
  mid c p = nth c (div2≤ p)

  take-left : ∀ {e f n m} (c : chain e f n) (p : m ≤ n) → chain e (nth c p) m
  take-left c z≤n = nil
  take-left (e#f ∷ c) (s≤s p) = e#f ∷ take-left c p

  take-right : ∀ {e f n m} (c : chain e f n) (p : m ≤ n) → chain (nth c p) f (n ∸ m) 
  take-right nil z≤n = nil
  take-right (e#f ∷ c) z≤n = e#f ∷ c
  take-right (e#f ∷ c) (s≤s p) = take-right c p

 
-}


