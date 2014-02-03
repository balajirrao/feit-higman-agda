open import Relation.Binary
open import Data.Nat
open import Data.Product
open import Data.Empty
open import Data.Fin using (Fin)

open import Relation.Binary.PropositionalEquality

open import Function.Bijection

import Level

module GenPolygon (P L : Set) (n : ℕ) where
  
  -- The Set O consists of two kinds of objects
  data O : Set where
    pt : P → O
    ln : L → O
  
  -- Axioms for incidence relation
  postulate 
    _#_ : Rel O Level.zero
    #sym : ∀ {e f} → e # f → f # e
    #refl : ∀ {e} → e # e

  -- Axioms for incidence plane. Two points (or lines) can be incident only when they are equal
  postulate
    A-pt#eq : ∀ {p p'} → ((pt p) # (pt p')) → (p ≡ p')
    A-ln#eq : ∀ {l l'} → ((ln l) # (ln l')) → (l ≡ l')

  infixr 5 _⟨_⟩∷_ 

  -- A p-chain is between two points. It can grow only by point-line pair
  data p-chain : P → P → Set where
   nil : ∀ {p} → p-chain p p
   _⟨_⟩∷_  : ∀ {p l p' p''} .(p#l : (pt p) # (ln l)) .(l#p' : (ln l) # (pt p')) (c : p-chain p' p'') → p-chain p p''

  import IncidenceGeometry as IG
  open IG O _#_ #refl #sym

  -- Convert a p-chain to a chain
  as-chain : ∀ {p p'} (pc : p-chain p p') → chain (pt p) (pt p')
  as-chain nil = nil
  as-chain (p#l ⟨ l#p' ⟩∷ pc) = p#l ∷ l#p' ∷ as-chain pc
  
  -- That a shortest chain exists between any two elements of O and they have length lambda e f
  postulate
    lambda : (e f : O) → ℕ
    lambda-shortest : ∀ {e f} (c : chain e f) → (len c ≡ (lambda e f)) → shortest c

  -- A₂ : There exists at most one irreducible chain of length less than n from e to f
  postulate
    A₂ : (e f : O) → Bijection (setoid (Σ (chain e f) (λ c → irred c × len c < n))) (setoid (Fin 1))
    
