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
    nil : ∀ {e} → chain e e
    _∷_ : ∀ {e f g} .(e#f : e # f) (c : chain f g) → chain e g

  len : ∀ {e f} (c : chain e f) → ℕ
  len nil = zero
  len (_ ∷ c) = suc (len c)

  data _∈_ : ∀ {e f} (x : O) (c : chain e f) → Set where
    ∈z : ∀ {e f} (c : chain e f) → e ∈ c
    ∈s : ∀ {e f x y} (c : chain e f) .(q : y # e) (p : x ∈ c) → x ∈ (q ∷ c)

  nth : ∀ {e f n} (c : chain e f) (p : n ≤ (len c))  → O
  nth {e} nil z≤n = e
  nth {e} (_ ∷ _) z≤n = e
  nth (e#f ∷ c) (s≤s p) = nth c p

                                                                       
  data irred : ∀ {e f} (c : chain e f) → Set where
    iz : ∀ {e f g} .(e#f : e # f) .(f#g : f # g) (¬e#g : .(e # g) → ⊥) → irred (e#f ∷ f#g ∷ nil)
    is : ∀ {e f g} .(e#f : e # f) (c : chain f g) (p : (len c) ≥ 1) 
           (ic : irred c) (¬e#c : .(e # (nth c p)) → ⊥) → irred (e#f ∷ c)
  

  nth-∈ : ∀ {e f n} (c : chain e f) (p : n ≤ (len c)) → (nth c p) ∈ c
  nth-∈ nil z≤n = ∈z nil
  nth-∈ (e#f ∷ c) z≤n = ∈z (e#f ∷ c)
  nth-∈ (e#f ∷ c) (s≤s p) = ∈s c e#f (nth-∈ c p)


  head : ∀ {e f} (c : chain e f) → O
  head {e} c = nth c z≤n

  last : ∀ {e f} (c : chain e f) → O
  last c = nth c m≤m

  tail : ∀ {e f} (c : chain e f) (p : (len c) ≥ 1) → chain (nth c p) f
  tail nil ()
  tail (e#f ∷ c) (s≤s z≤n) with c
  ... | nil = c
  ... | _ ∷ _ = c


  init : ∀ {e f} (c : chain e f) (p : (len c) ≥ 1) → chain e (nth {n = pred (len c)} c n≤pred)
  init nil ()
  init (e#f ∷ nil) (s≤s z≤n) = nil
  init (e#f ∷ e#f₁ ∷ c) (s≤s z≤n) = e#f ∷ init (e#f₁ ∷ c) (s≤s z≤n)

  infixl 5 _++_
  _++_ : ∀ {e f g} (c : chain e f) .(p : f # g) → chain e g
  nil ++ p = p ∷ nil
  (e#f ∷ c) ++ p = e#f ∷ (c ++ p)

  rev : ∀ {e f} (c : chain e f) → chain f e
  rev nil = nil
  rev (e#f ∷ c) = rev c ++ (#-sym e#f) 

  -- Shortest chain --

  shortest : ∀ {e f} → (c : chain e f) → Set
  shortest {e} {f} c = (c' : chain e f) → ((len c) ≯ (len c'))

  shortest-irred : ∀ {e f} (c : chain e f) (p : (len c) ≥ 2) → shortest c → irred c
  shortest-irred nil () sc
  shortest-irred (e#f ∷ nil) (s≤s ()) sc
  shortest-irred (e#f ∷ f#g ∷ nil) (s≤s (s≤s z≤n)) sc = iz e#f f#g (λ e#g → sc (e#g ∷ nil) (s≤s (s≤s z≤n)))
  shortest-irred (e#f ∷ f#g ∷ g#h ∷ c) (s≤s (s≤s z≤n)) sc =
                            is e#f (f#g ∷ g#h ∷ c) (s≤s z≤n)
                            (shortest-irred (f#g ∷ g#h ∷ c) (s≤s (s≤s z≤n))
                              (λ c' z → sc (e#f ∷ c') (s≤s z)))
                            (λ e#g → sc (e#g ∷ g#h ∷ c) m≤m)

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
