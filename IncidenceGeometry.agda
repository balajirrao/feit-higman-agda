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
  data chain : O → O → ℕ → Set where
    nil : ∀ {e} → chain e e zero
    _∷_ : ∀ {e f g n} (e#f : e # f) (c : chain f g n) → chain e g (suc n)

  data _∈_ : ∀ {e f n} (x : O) (c : chain e f n) → Set where
    ∈z : ∀ {e f n} (c : chain e f n) → e ∈ c
    ∈s : ∀ {e f n x y} (c : chain e f n) (q : y # e) (p : x ∈ c) → x ∈ (q ∷ c)
   
  nth : ∀ {e f m n} (c : chain e f n) (p : m ≤ n) → O
  nth {e} _ z≤n = e
  nth (_ ∷ c) (s≤s p) = nth c p
                                                                        
  data irred : ∀ {e f n} (c : chain e f n) → Set where
    iz : ∀ {e f g} (e#f : e # f) (f#g : f # g) (¬e#g : e # g → ⊥) → irred (e#f ∷ f#g ∷ nil)
    is : ∀ {e f g n} (e#f : e # f) (c : chain f g n) (p : n ≥ 1)
           (ic : irred c) (¬e#c : e # (nth c p) → ⊥) → irred (e#f ∷ c)
       
  nth-∈ : ∀ {e f n m} (c : chain e f n) (p : m ≤ n) → (nth c p) ∈ c
  nth-∈ c z≤n = ∈z c
  nth-∈ (e#f ∷ c) (s≤s p) = ∈s c e#f (nth-∈ c p)

  head : ∀ {e f n} (c : chain e f n) → O
  head {e} c = nth c z≤n

  last : ∀ {e f n} (c : chain e f n) → O
  last c = nth c m≤m

  tail : ∀ {e f n} (c : chain e f (suc n)) → chain (nth c (s≤s z≤n)) f n
  tail (_ ∷ c) = c

  init : ∀ {e f n} (c : chain e f (suc n)) → chain e (nth c n≤suc) n
  init (_ ∷ nil) = nil
  init (e#f ∷ f#g ∷ c) = e#f ∷ init (f#g ∷ c)

  infixl 5 _++_
  _++_ : ∀ {e f g n} (c : chain e f n) (p : f # g) → chain e g (suc n)
  nil ++ p = p ∷ nil
  (e#f ∷ c) ++ p = e#f ∷ (c ++ p)
  
  rev : ∀ {e f n} (c : chain e f n) → chain f e n
  rev nil = nil
  rev (e#f ∷ c) = rev c ++ (#-sym e#f) 

  -- Shortest chain --

  shortest : ∀ {e f n} → (c : chain e f n) → Set
  shortest {e} {f} {n} _ = ∀ {m} (c' : chain e f m) → (n ≯ m)

  shortest-irred : ∀ {e f n} (c : chain e f n) (p : n ≥ 2) → shortest c → irred c
  shortest-irred (e#f ∷ f#g ∷ nil) (s≤s (s≤s z≤n)) sc =
                      iz e#f f#g (λ e#g → sc (e#g ∷ nil) (s≤s (s≤s z≤n)))
  shortest-irred (e#f ∷ f#g ∷ g#h ∷ c) (s≤s (s≤s z≤n)) sc =
                      is e#f (f#g ∷ g#h ∷ c) (s≤s z≤n)
                      (shortest-irred (f#g ∷ g#h ∷ c) (s≤s (s≤s z≤n))
                      (λ {m} c' z → sc (e#f ∷ c') (s≤s z)))
                      (λ e#g → ⊥-elim (sc (e#g ∷ g#h ∷ c) m≤m))
