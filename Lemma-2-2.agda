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
                                       (even≡ spc-len-lambda (pp-len-even (spc e (pt f))))
                                              (odd≡ (sym (trans
                                                    (PropEq.cong (λ x → lambda (pt e) x) (sym eq))
                                                      (proj₂ (GP (pt e))))) p) )

  rev' : ∀ {e f k} →  Σ (chain e f) (λ c → len c ≡ k) → Σ (chain f e) (λ c → len c ≡ k)
  rev' (c , len≡k) = (rev c) , trans (sym len-rev) len≡k

  rev'-cong : ∀ {e f k} → {i j : Σ (chain e f) (λ c → len c ≡ k)} → i ≈ j → rev' i ≈ rev' j
  rev'-cong {e} {f} {k} {.proj₁ , proj₂} {proj₁ , proj₃} refl = refl  

  rev-++ : ∀ {e f g} {c : chain e f} .{f#g : f # g} .{f<>g : f ≢ g} → rev (c ++ g) ≡ _∷_ g {{e<>f = λ x → f<>g (sym x)}} {{e#f = #sym f#g}} (rev c) 
  rev-++ {.f} {f} {g} {[ .f ]} = refl
  rev-++ {e} {f} {g} {_∷_ {e₁} .e {{e<>e₁}} {{e#e₁}} c} {f#g} {f<>g} rewrite rev-++ {e₁} {f} {g} {c} {f#g} {f<>g} = refl                                                   

  rev²-id : ∀ {e f} {c : chain e f} → rev (rev c) ≡ c
  rev²-id {.f} {f} {[ .f ]} = refl
  rev²-id {e} {f} {_∷_ {e₁} .e {{e<>f}} {{e#f}} c} = trans (rev-++ {f} {e₁} {e} {rev c} {#sym e#f} {λ z → e<>f (sym z)}) (cong (_∷_ e) rev²-id)
 
  rev'²-id : ∀ {e f k} → (c : Σ (chain e f) (λ c → len c ≡ k)) → rev' (rev' c) ≈ c
  rev'²-id c = chains≡⇒≈ rev²-id

  -- Next, we need an Inverse between chains from e to f to chains to f to e of the same length
  revI : ∀ {e f k} → Inverse (ChainsWithProperty e f (λ c → len c ≡ k)) (ChainsWithProperty f e (λ c → len c ≡ k))
  revI = record { to = record { _⟨$⟩_ = rev'; cong = rev'-cong }; 
                   from = record { _⟨$⟩_ = rev'; cong = rev'-cong };
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
