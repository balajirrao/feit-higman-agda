open import Data.Nat
open import Data.Nat.Properties
--open Data.Nat.≤-Reasoning

open import Data.Fin using (Fin)

open import Data.Unit using (⊤; tt)
open import Data.Empty
open import Data.Product

open import Relation.Binary.PropositionalEquality as PropEq
open PropEq.≡-Reasoning 

open import Relation.Nullary.Core

open import Function.Equality hiding (setoid; cong; _∘_)
open import Function.Inverse hiding (sym)

open import Misc

open import GenPolygon

open import Data.Unit hiding (setoid)

module Lemma-2-2 where

  open import Lemma-2-1

  -- Choose f such that lambda e f = n. Then f must be in L
  step-0 : ∀ {e} → Odd (reveal _n) → L
  step-0 {e} p with proj₁ (GP (pt e)) | inspect proj₁ (GP (pt e))
  step-0 p | ln f | [ eq ] = f
  step-0 {e} p | pt f | [ eq ] = ⊥-elim (eitherEvenOdd (lambda (pt e) (pt f))
                                       (even≡ sc-len-lambda (pp-len-even (sc (pt e) (pt f))))
                                              (odd≡ (sym (trans
                                                    (PropEq.cong (λ x → lambda (pt e) x) (sym eq))
                                                      (proj₂ (GP (pt e))))) p) )

  rev' : ∀ {e f k} →  Σ (chain e f) (λ c → len c ≡ k) → Σ (chain f e) (λ c → len c ≡ k)
  rev' (c , len≡k) = (rev c) , trans (sym len-rev) len≡k

  rev'²-id : ∀ {e f k} → (c : Σ (chain e f) (λ c → len c ≡ k)) → rev' (rev' c) ≈ c
  rev'²-id c = rev²-id

  -- Next, we need an Inverse between chains from e to f to chains to f to e of the same length
  revI : ∀ {e f k} → Inverse (ChainsWithPropertySetoid {e} {f} (λ c → len c ≡ k)) (ChainsWithPropertySetoid {f} {e} (λ c → len c ≡ k))
  revI = record { to = record { _⟨$⟩_ = rev'; cong = cong rev }; 
                   from = record { _⟨$⟩_ = rev'; cong = cong rev };
                   inverse-of = record { left-inverse-of = rev'²-id; 
                                         right-inverse-of = rev'²-id } }
  
  lemma-2-2 : ∀ {e f} → (lambda (pt e) (ln f) ≡ n) → Inverse (setoid (L# e)) (setoid (P# f))
  lemma-2-2 p = lemma2-1a (trans lambda-sym p) ∘ revI ∘ record { 
                                                               to = Inverse.from (lemma2-1 p);
                                                               from = Inverse.to (lemma2-1 p);
                                                               inverse-of = record {
                                                                            left-inverse-of = Inverse.right-inverse-of (lemma2-1 p);
                                                                            right-inverse-of = Inverse.left-inverse-of (lemma2-1 p)
                                                                            }
                                                               }
