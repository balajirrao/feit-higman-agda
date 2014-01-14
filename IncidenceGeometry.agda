module IncidenceGeometry (O : Set) (_#_ : O → O → Set) where
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

  postulate
    #-refl : ∀ {e} → e # e
    #-sym : ∀ {e f} → e # f → f # e

  infixl 5 _∷_  
  infixr 5 _∷_  
 
  data chain : O → O → ℕ → Set where
    [_] : (e : O) → chain e e zero
    _∷_ : ∀ {f g n} (e : O) (c : chain f g n) .{p : e # f} → chain e g (suc n)

  nth : ∀ {e f m n} (c : chain e f n) (p : m ≤ n) → O
  nth {e} _ z≤n = e
  nth (_ ∷ c) (s≤s p) = nth c p


  head : ∀ {e f n} (c : chain e f n) → O
  head {e} c = nth c z≤n

  last : ∀ {e f n} (c : chain e f n) → O
  last c = nth c m≤m

  tail : ∀ {e f n} (c : chain e f (suc n)) → chain (nth c (s≤s z≤n)) f n
  tail (_ ∷ c) = c


  init : ∀ {e f n} (c : chain e f (suc n)) → chain e (nth c n≤suc) n
  init {e} {f} (.e ∷ [ .f ]) = [ e ]
  init ((e ∷ (f ∷ c)) {p}) = (e ∷ init (f ∷ c)) {p}
