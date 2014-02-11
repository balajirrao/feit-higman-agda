open import Data.Nat
open import Data.Nat.Properties
open Data.Nat.≤-Reasoning

open import Data.Fin using (Fin)

open import Data.Unit using (⊤; tt)
open import Data.Empty
open import Data.Product

open import Relation.Binary.PropositionalEquality as PropEq
open import Relation.Nullary.Core

open import Function.Equality hiding (setoid)
open import Function.Bijection

open import Misc

open import GenPolygon

open import Data.Unit

module Lemma-2-2 where
  
  -- Choose f such that lambda e f = n. Then f must be in L
  step0 : ∀ {e} → Odd (reveal _n) → L
  step0 {e} p with proj₁ (GP (pt e)) | inspect proj₁ (GP (pt e))
  step0 p | ln f | [ eq ] = f
  step0 {e} p | pt f | [ eq ] = ⊥-elim (eitherEvenOdd (lambda (pt e) (pt f))
                                       (even≡ spc-len-lambda (pp-len-even (spc e (pt f))))
                                              (odd≡ (sym (trans
                                                    (PropEq.cong (λ x → lambda (pt e) x) (sym eq))
                                                      (proj₂ (GP (pt e))))) p) )


  lemma-2-2 : Odd (reveal _n) → s ≡ t
  lemma-2-2 p = {!!}
