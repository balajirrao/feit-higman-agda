open import Data.Nat
open import Data.Nat.Properties

open Data.Nat.≤-Reasoning

open import Data.Fin using (Fin)

open import Data.Unit using (⊤; tt)
open import Data.Empty
open import Data.Product

open import Relation.Binary.PropositionalEquality
--open PropEq.≡-Reasoning renaming (begin_ to ≡begin_; _≡⟨_⟩_ to _==⟨_⟩_; _∎ to _≡∎)

open import Relation.Nullary.Core

open import Function.Equality hiding (setoid; cong)
open import Function.Bijection

open import Misc

open import GenPolygon

open import Data.Unit.Core

module Lemma-2-1-new where

  -- A p-chain and an l-chain ending at the common point can *not* have equal lengths
  step0 : ∀ {e e₁ f} → (pc : p-chain e f) (lc : l-chain e₁ f) → (p-len pc) ≡ (l-len lc) → ⊥
  step0 {e} {e₁} {pt f} pc lc p = eitherEvenOdd
                                  (p-len pc) (pp-len-even pc)
                                  (odd≡ (sym p) (lp-len-odd lc))
  step0 {e} {e₁} {ln f} pc lc p = eitherEvenOdd
                                  (p-len pc)
                                  (even≡ (sym p) (ll-len-even lc))
                                  (pl-len-odd pc)
    
  -- An incident point-line pair can *not* have equal len-lambda distance to a common point
  step1 : ∀ {e e₁ f} → .((pt e) # (ln e₁)) → (lambda (pt e) f) ≡ (lambda (ln e₁) f) → ⊥
  step1 {e} {e₁} {f} p q rewrite (lcc-id (sc (ln e₁) f))
                 = step0 (spc e f) (slc e₁ f)  (trans spc-len-lambda
                                                      (trans q (sym slc-len-lambda)))

  -- Given 3 contiguous natural numbers a b c and that if
  -- ∙ x is not greater than c
  -- ∙ x is not less than a
  -- ∙ x is not equal to b
  -- ∙ x is not equal to c
  -- ⇒ Then conclude x is equal to a
  x≡pred : ∀ {b} (x : ℕ) (b≥1 : b ≥ 1) (x≮a : x ≮ (pred b)) (x≯c : x ≯ (suc b))
                              (x≢b : x ≢ b) (x≢c : x ≢ (suc b)) → x ≡ pred b
  x≡pred {zero} x () x≮a x≯c x≢b x≢c
  x≡pred {suc zero} x (s≤s z≤n) x≮a x≯c x≢b x≢c with compare x 0
  x≡pred {suc zero} .0 (s≤s z≤n) x≮a x≯c x≢b x≢c | equal .0 = refl
  x≡pred {suc zero} .1 (s≤s z≤n) x≮a x≯c x≢b x≢c | greater .0 zero = ⊥-elim (x≢b refl)
  x≡pred {suc zero} .2 (s≤s z≤n) x≮a x≯c x≢b x≢c | greater .0 (suc zero) = ⊥-elim (x≢c refl)
  x≡pred {suc zero} .(suc (suc (suc k))) (s≤s z≤n) x≮a x≯c x≢b x≢c | greater .0 (suc (suc k)) = ⊥-elim (x≯c (s≤s (s≤s (s≤s z≤n))))
  x≡pred {suc (suc b)} zero (s≤s z≤n) x≮a x≯c x≢b x≢c = ⊥-elim (x≮a (s≤s z≤n))
  x≡pred {suc (suc b)} (suc x) b≥1 x≮a x≯c x≢b x≢c = cong suc (x≡pred {suc b} x (s≤s z≤n)
                                                              (λ z → x≮a (s≤s z))
                                                              (λ z → x≯c (s≤s z))
                                                              (λ z → x≢b (cong suc z))
                                                              (λ z → x≢c (cong suc z))) 

