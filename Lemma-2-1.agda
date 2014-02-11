open import Data.Nat
open import Data.Nat.Properties

open Data.Nat.≤-Reasoning

open import Data.Fin using (Fin)

open import Data.Unit using (⊤; tt)
open import Data.Empty
open import Data.Product

open import Relation.Binary.PropositionalEquality as PropEq
open PropEq.≡-Reasoning renaming (begin_ to ≡begin_; _≡⟨_⟩_ to _==⟨_⟩_; _∎ to _≡∎)

open import Relation.Nullary.Core

open import Function.Equality hiding (setoid)
open import Function.Bijection

open import Misc

open import GenPolygon

open import Data.Unit.Core

module Lemma-2-1 where

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
                 = step0 (spc e f) (slc e₁ f)  (trans spc-len-lambda (trans q (sym slc-len-lambda)))

  -- If e # e₁ then λ (e₁ , f) is atmost suc ( λ ( e, f))
  step2 : ∀ {e e₁ f} → (pt e) # (ln e₁) → (lambda (ln e₁) f) ≯ suc (lambda (pt e) f)
  step2 {e} {e₁} {f} e#e₁ p = lambda-shortest (pt e ∷ sc (ln e₁) f)
                              (⊥-elim (lambda-shortest
                                (_∷_ (ln e₁) {{e#f = #sym e#e₁}} (sc (pt e) f))
                              (begin
                              suc (suc (len (sc (pt e) f)))
                                ≡⟨ PropEq.cong suc (PropEq.cong suc sc-len-lambda) ⟩
                              suc (suc (lambda (pt e) f))
                                ≤⟨ p ⟩
                              (lambda (ln e₁) f) ∎
                              )))
                                
  -- If e # e₁ then λ (e₁ , f) is least pred ( λ ( e, f))
  step3 : ∀ {e e₁ f} → .((pt e) # (ln e₁)) → (lambda (pt e) f ≡ n) → (lambda (ln e₁) f) ≮ pred (lambda (pt e) f)
  step3 {e} {e₁} {f} e#e₁ ≡n p = lambda-shortest (_∷_ (ln e₁) {{e#f = #sym e#e₁}} (sc (pt e) f))
                                 (⊥-elim (lambda-shortest (pt e ∷ sc (ln e₁) f)
                                         (begin
                                           suc (suc (len (sc (ln e₁) f)))
                                               ≡⟨ PropEq.cong suc (PropEq.cong suc sc-len-lambda) ⟩
                                                 suc (suc (lambda (ln e₁) f))
                                                   ≤⟨ s≤s p ⟩
                                                 suc (pred (lambda (pt e) f))
                                                   ≡⟨ suc∘pred≡id
                                                      (begin
                                                        1
                                                          ≤⟨ s≤s z≤n ⟩
                                                        3
                                                          ≤⟨ n>2 ⟩
                                                        n
                                                          ≡⟨ sym ≡n ⟩
                                                        lambda (pt e) f ∎)
                                                      ⟩
                                                 lambda (pt e) f
                                                 ∎
                                               )))
    

  -- Therefore we conclude by A₁ that λ (e₁, f) must be equal to pred ( λ (e , f))
  step4 : ∀ {e e₁ f} → .((pt e) # (ln e₁)) → (lambda (pt e) f) ≡ n →  (lambda (ln e₁) f) ≡ pred (lambda (pt e) f)
  step4 {e} {e₁} {f} e#e₁ ≡n with (suc(lambda (ln e₁) f)) ≤? pred (lambda (pt e) f)
  step4 e#e₁ ≡n | yes p = ⊥-elim (step3 e#e₁ ≡n p)
  step4 {e} {e₁} {f} e#e₁ ≡n | no ¬p with suc (lambda (pt e) f) ≤? (lambda (ln e₁) f)
  step4 {e} {e₁} {f} e#e₁ ≡n | no ¬p | yes p = ⊥-elim (A₁'
                                               (begin
                                                 suc (reveal _n) 
                                                   ≡⟨ PropEq.cong suc (sym ≡n) ⟩
                                                 suc (lambda (pt e) f)
                                                   ≤⟨ p ⟩
                                                 (lambda (ln e₁) f ∎)))

  step4 {e} {e₁} {f} e#e₁ ≡n | no ¬p₁ | no ¬p with (lambda (pt e) f) ≟ (lambda (ln e₁) f)
  step4 e#e₁ ≡n | no ¬p₁ | no ¬p | yes p = ⊥-elim (step1 e#e₁ p)
  step4 e#e₁ ≡n | no ¬p₂ | no ¬p₁ | no ¬p = ≤-≥⇒≡ (
                                                  pred-mono(pred-mono(
                                                  (≤≢⇒< (≰⇒> ¬p₁))
                                                  (λ t₁ → ¬p (PropEq.cong pred (sym t₁)))
                                                  ))) (suc-≤ (≰⇒> ¬p₂))
 
  -- Fun from chains of length n from e to f to lines incident with e  
  step5 : ∀ {e f} → Σ (p-chain e f) (λ pc → p-len pc ≡ n)  → L# e
  step5 (c , p) with n | n>2
  step5 (c , p) | zero | ()
  step5 {e} ([ .e ] , ()) | suc a | s≤s b
  step5 {e} (_∷_ {l} .e {{e#f}} c , p) | suc a | s≤s b = l ⟦ e#f ⟧

  step5-inj : ∀ {e f} (c c' : Σ (p-chain e f) (λ pc → p-len pc ≡ n)) →
                step5 c ≡ step5 c' → pc-to-c (proj₁ c) ≡ pc-to-c (proj₁ c')
  step5-inj {e} {f} c c' p with n | n>2 | inspect reveal _n
  step5-inj {e} ([ .e ] , l) ([ .e ] , n) p | a | b | [ eq ] = refl
  step5-inj {e} ([ .e ] , refl) (_∷_ .e {{e#f}} c , ()) p | .0 | b | [ eq ]
  step5-inj {e} (_∷_ .e {{e#f}} c , ()) ([ .e ] , refl) p | .0 | b  | [ eq ]
  step5-inj {e} (_∷_ .e {{e#f}} c , l) (_∷_ .e {{e#f₁}} c₁ , refl) refl | ._ | s≤s b | [ eq ] =
                PropEq.cong (_∷_ (pt e)) (A₂ ((lc-to-c c) ,
                                             (begin
                                               suc (len (lc-to-c c))
                                                 ≡⟨ PropEq.cong suc (sym (llen-len c)) ⟩ 
                                               suc (l-len c)
                                                 ≡⟨ l ⟩
                                               suc (l-len c₁)
                                                 ≡⟨ sym eq ⟩
                                               n
                                                 ∎))
                                             ((lc-to-c c₁),
                                               (begin
                                                 suc (len (lc-to-c c₁))
                                                   ≡⟨ PropEq.cong suc (sym (llen-len c₁)) ⟩
                                                 suc (l-len c₁)
                                                   ≡⟨ sym eq ⟩
                                                 (n ∎))
                                             ))

  -- Since lambda e₁ f = n - 1, 
 -- step6 : 

  -- Forall f, given e # l, get a p-chain from e to f
  step6 : ∀ {e f} → L# e → (lambda (pt e) f ≡ n) →  Σ (p-chain e f) (λ pc → p-len pc ≡ n)
  step6 {e} {f} l#e p = (_∷_ e {{e#f = p#l l#e}} (slc (#l l#e) f) ,
                                                (≡begin
                                                   suc (l-len (c-to-lc (sc (ln (#l l#e)) f)))
                                                     ==⟨ PropEq.cong suc (llen-len (slc (#l l#e) f)) ⟩
                                                   suc (len (lc-to-c (c-to-lc (sc (ln (#l l#e)) f))))
                                                     ==⟨ PropEq.cong suc (PropEq.cong len (lcc-id (sc (ln (#l l#e)) f))) ⟩
                                                   suc (len (sc (ln (#l l#e)) f))
                                                     ==⟨ PropEq.cong suc sc-len-lambda ⟩
                                                   suc (lambda (ln (#l l#e)) f)
                                                     ==⟨ PropEq.cong suc (step4 (p#l l#e) p) ⟩ 
                                                   suc (pred (lambda (pt e) f))
                                                     ==⟨ suc∘pred≡id
                                                         (begin
                                                           1
                                                         ≤⟨ s≤s z≤n ⟩
                                                           3
                                                         ≤⟨ n>2 ⟩
                                                           n
                                                         ≡⟨ sym p ⟩ (lambda (pt e) f ∎)) ⟩
                                                     lambda (pt e) f ==⟨ p ⟩ n ≡∎))

  step7 : ∀ {e f} → L# e → (lambda (pt e) f ≡ n) → Σ (chain (pt e) f) (λ c → len c ≡ n)
  step7 {e} {f} l#e p = pc-to-c (proj₁ (step6 l#e p)) , trans (PropEq.cong suc (sym (llen-len (slc (#l l#e) f)))) (proj₂ (step6 l#e p))


  lemma2-1 : ∀ {e f} (p : (lambda (pt e) f) ≡ n) → Bijection (ChainsWithProperty (pt e) f (λ c → len c ≡ n)) (setoid (L# e))
  lemma2-1 {e} {f} p = record { to = record { _⟨$⟩_ = λ z → step5 (c-to-pc (proj₁ z) , {!!}); cong = {!!} };
                                              bijective = record { injective = {!!};
                                                                   surjective = record
                                                                                { from = record { _⟨$⟩_ = λ t₁ → step7 t₁ p; cong = {!!} };
                                                                                right-inverse-of = λ x → {!!} } } }


