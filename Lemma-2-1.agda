open import Data.Nat
open import Data.Nat.Properties

open Data.Nat.≤-Reasoning

open import Data.Fin using (Fin)

open import Data.Unit using (⊤; tt)
open import Data.Empty
open import Data.Product

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning renaming (begin_ to ≡begin_; _≡⟨_⟩_ to _==⟨_⟩_; _∎ to _≡∎)

open import Relation.Nullary.Core

open import Function.Equality hiding (setoid; cong)
open import Function.Inverse hiding (sym)

open import Misc

open import GenPolygon

open import Data.Unit.Core

import Level

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
    
  -- An incident point-line pair can *not* have equal shortest distances to a common point
  -- because of even-odd polarity
  step1 : ∀ {e e₁ f} → .((pt e) # (ln e₁)) → (lambda (pt e) f) ≡ (lambda (ln e₁) f) → ⊥
  step1 {e} {e₁} {f} p q rewrite (lcc-id (sc (ln e₁) f))
                 = step0 (spc e f) (slc e₁ f)  (trans spc-len-lambda
                                                      (trans q (sym slc-len-lambda)))
  
  lambda-unequal : ∀ {e e₁ f} → .{e#e₁ : e # e₁} .{e<>e₁ : e ≢ e₁} → (lambda e f) ≡ (lambda e₁ f) → ⊥
  lambda-unequal {pt x} {pt x₁} {f} {e₁#e} {e₁<>e} _ = A-pt#eq e₁#e e₁<>e 
  lambda-unequal {ln x} {ln x₁} {f} {e₁#e} {e₁<>e} _ = A-ln#eq e₁#e e₁<>e
  lambda-unequal {pt x} {ln x₁} {f} {e₁#e} {e₁<>e} λ≡ = step1 e₁#e λ≡
  lambda-unequal {ln x} {pt x₁} {f} {e₁#e} {e₁<>e} λ≡ = step1 (#sym e₁#e) (sym λ≡)

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

  n≥1 : n ≥ 1
  n≥1 = begin 1 ≤⟨ s≤s z≤n ⟩ 3 ≤⟨ n>2 ⟩ (n ∎)

  n≢0 : n ≡ 0 → ⊥
  n≢0 n≡0 = ⊥-elim (n≰2 (<-≡-trans (cong suc (cong suc (sym n≡0))) (≤-steps 2 m≤m)))
  

  lambda-pred : ∀ {e e₁ f} .{e#e₁ : e # e₁} .{e<>e₁ : e ≢ e₁} → lambda e f ≡ n → lambda e₁ f ≡ pred (lambda e f)
  lambda-pred {e} {e₁} {f} {e#e₁} {e<>e₁} p = x≡pred {lambda e f} (lambda e₁ f)
                                          (<-≡-trans p n≥1)
                                          (λ x → lambda-ub {e<>e₁ = λ z → e<>e₁ (sym z)} {e#e₁ = #sym e#e₁}
                                                 (begin
                                                   suc (suc (lambda e₁ f))
                                                     ≤⟨ s≤s x ⟩
                                                   suc (pred (lambda e f))
                                                     ≡⟨ suc∘pred≡id (<-≡-trans p n≥1) ⟩
                                                   (lambda e f ∎)))
                                          (λ x → lambda-lb {e<>e₁ = λ z → e<>e₁ (sym z)} {e#e₁ = #sym e#e₁}
                                                 (begin
                                                   1
                                                     ≤⟨ <-≡-trans p n≥1 ⟩
                                                   lambda e f
                                                     ≤⟨ ≤-steps 2 m≤m ⟩
                                                   suc (suc (lambda e f))
                                                     ≤⟨ x ⟩ lambda e₁ f ∎) (pred-mono x))
                                          (lambda-unequal {e#e₁ = #sym e#e₁} {e<>e₁ = λ z → e<>e₁ (sym z)})
                                          (λ x → A₁'
                                                 (begin
                                                   suc (reveal _n)
                                                     ≡⟨ cong suc (sym p) ⟩
                                                   suc (lambda e f)
                                                     ≡⟨ sym x ⟩
                                                   lambda e₁ f ∎))
 
  
 -- F and F-inverse build correspondence between chains of length n and lines incident with e
  F : ∀ {e f} {λ≡n : lambda (pt e) f ≡ n} → Σ (chain (pt e) f) (λ c → len c ≡ n) → L# e
  F {λ≡n = λ≡n} ([ ._ ] , len≡n) = ⊥-elim (n≢0 (sym len≡n))
  F (_∷_ {pt x} ._ {{e<>f}} {{e#f}} c , len≡n) = ⊥-elim (A-pt#eq e#f e<>f)
  F (_∷_ {ln f} ._ {{e<>f}} {{e#f}} c , len≡n) = f ⟦ e#f ⟧ 


  F-cong : ∀ {e f} {λ≡n : lambda (pt e) f ≡ n} → {c c' : Σ (chain (pt e) f) (λ c → len c ≡ n)}
                                                 → c ≈ c' → F {e} {f} {λ≡n} c ≡ F {e} {f} {λ≡n} c'
  F-cong {e} {.(pt e)} {λ≡n} {.([ pt e ]) , proj₂} {[ .(pt e) ] , proj₄} refl = refl
  F-cong {e} {f} {λ≡n} {.(pt e ∷ proj₃) , proj₂} {_∷_ {pt x} .(pt e) {{e<>f}} {{e#f}} proj₃ , proj₄} refl = refl
  F-cong {e} {f} {λ≡n} {.(pt e ∷ proj₃) , proj₂} {_∷_ {ln x} .(pt e) {{e<>f}} {{e#f}} proj₃ , proj₄} refl = refl


  F-inverse : ∀ {e f} {λ≡n : lambda (pt e) f ≡ n} → L# e → Σ (chain (pt e) f) (λ c → len c ≡ n)
  F-inverse {e} {f} {λ≡n} (e₁ ⟦ p#l ⟧) = _∷_ (pt e) {{λ ()}} (sc (ln e₁) f) , 
                                          (≡begin
                                            suc (len (sc (ln e₁) f))
                                              ==⟨ cong suc sc-len-lambda ⟩
                                            suc (lambda (ln e₁) f)
                                              ==⟨ cong suc (lambda-pred {e#e₁ = p#l} {e<>e₁ = λ()} λ≡n) ⟩
                                            suc (pred (lambda (pt e) f))
                                              ==⟨ suc∘pred≡id (<-≡-trans λ≡n n≥1) ⟩
                                            lambda (pt e) f
                                              ==⟨ λ≡n ⟩
                                            n ≡∎)
  
  F-inverse-cong : ∀ {e f} {λ≡n : lambda (pt e) f ≡ n} → {i j : L# e} → i ≡ j → F-inverse {e} {f} {λ≡n} i ≈ F-inverse {e} {f} {λ≡n} j
  F-inverse-cong {_} {_} {_} {.j} {j} refl = refl

  -- Proof that F is injective
  F-inj : ∀ {e f} {λ≡n : lambda (pt e) f ≡ n} → {c c' : Σ (chain (pt e) f) (λ c → len c ≡ n)} →
                      F {e} {f} {λ≡n} c ≡ F  {e} {f} {λ≡n} c' → c ≈ c'
  F-inj {e} {.(pt e)} {_} {([ .(pt e) ] , len≡n)} {([ .(pt e) ] , len≡n')} refl = ⊥-elim (n≢0 (sym len≡n'))
  F-inj {e} {.(pt e)} {_} {([ .(pt e) ] , len≡n)} {(_∷_ .(pt e) {{e<>f}} {{e#f}} c' , len≡n')} p = ⊥-elim (n≢0 (sym len≡n))
  F-inj {e} {.(pt e)} {_} {(_∷_ .(pt e) {{e<>f}} {{e#f}} c , len≡n)} {([ .(pt e) ] , len≡n')} p = ⊥-elim (n≢0 (sym len≡n'))
  F-inj {e} {f} {_} {(_∷_ {pt x} .(pt e) {{e<>f}} {{e#f}} c , len≡n)} {(_∷_ .(pt e) {{e<>f₁}} {{e#f₁}} c' , len≡n')} p = ⊥-elim (A-pt#eq e#f e<>f)
  F-inj {e} {f} {_} {(_∷_ {ln x} .(pt e) {{e<>f}} {{e#f}} c , len≡n)} {(_∷_ {pt x₁} .(pt e) {{e<>f₁}} {{e#f₁}} c' , len≡n')} p = ⊥-elim (A-pt#eq e#f₁ e<>f₁)
  F-inj {e} {f} {_} {(_∷_ {ln .x₁} .(pt e) {{e<>f}} {{e#f}} c , len≡n)} {(_∷_ {ln x₁} .(pt e) {{e<>f₁}} {{e#f₁}} c' , len≡n')} refl = --{!!}
                     chains≡⇒≈ (cong (λ x → _∷_ (pt e) {{e<>f = e<>f}} {{e#f = e#f}} x)
                          (A₂ (c , (≡⇒≤ len≡n)) (c' , (≡⇒≤ len≡n'))))
 

  F-left-inv : ∀ {e f} → (λ≡n : lambda (pt e) f ≡ n) (x : Σ (chain (pt e) f) (λ c → len c ≡ n)) → proj₁ (F-inverse {e} {f} {λ≡n} (F {e} {f} {λ≡n} x)) ≡ proj₁ (x)
  F-left-inv {e} p ([ .(pt e) ] , proj₂) = ⊥-elim (n≢0 (sym proj₂))
  F-left-inv {e} p (_∷_ {pt x} .(pt e) {{e<>f}} {{e#f}} proj₁ , proj₂) = ⊥-elim (A-pt#eq e#f e<>f)
  F-left-inv {e} {f} p (_∷_ {ln e₁} .(pt e) {{e<>f}} {{e#f}} proj₁ , proj₂) = cong (_∷_ (pt e))
             (A₂ ((sc (ln e₁) f) , (begin suc (len (sc (ln e₁) f)) ≡⟨ cong suc sc-len-lambda ⟩
                                            suc (lambda (ln e₁) f) ≡⟨ cong suc (lambda-pred {(pt e)} {(ln e₁)} {f} {e#f} {e<>f} p) ⟩
                                            suc (pred (lambda (pt e) f)) ≡⟨ suc∘pred≡id (<-≡-trans p n≥1) ⟩ lambda (pt e) f ≡⟨ p ⟩ (n ∎)))
             (proj₁ , ≡⇒≤ proj₂)) 

  lemma2-1 : ∀ {e f} → lambda (pt e) f ≡ n → Inverse (ChainsWithProperty (pt e) f (λ c → len c ≡ n)) (setoid (L# e))
  lemma2-1 {e} {f} λ≡n = record { to = record { _⟨$⟩_ = F {e} {f} {λ≡n}; cong = F-cong }; from = record {
                                              _⟨$⟩_ = F-inverse {e} {f} {λ≡n};
                                              cong = F-inverse-cong {e} {f} {λ≡n} };
                                              inverse-of = record { left-inverse-of = λ x → chains≡⇒≈ (F-left-inv λ≡n x); right-inverse-of = λ x → refl } }

  {-lemma2-1 {e} {f} λ≡n = record { to = record { _⟨$⟩_ = F {e} {f} {λ≡n}; cong = F-cong };
                                  bijective = record { injective = F-inj;
                                                       surjective = record { from = record
                                                                           { _⟨$⟩_ = F-inverse {e} {f} {λ≡n};
                                                                             cong = F-inverse-cong {e} {f} {λ≡n} };
                                                                           right-inverse-of = λ x → refl } } }-}

   
 -- F and F-inverse build correspondence between chains of length n and lines incident with e
  G : ∀ {e f} {λ≡n : lambda (ln e) f ≡ n} → Σ (chain (ln e) f) (λ c → len c ≡ n) → P# e
  G {λ≡n = λ≡n} ([ ._ ] , len≡n) = ⊥-elim (n≢0 (sym len≡n))
  G (_∷_ {ln x} ._ {{e<>f}} {{e#f}} c , len≡n) = ⊥-elim (A-ln#eq e#f e<>f)
  G (_∷_ {pt f} ._ {{e<>f}} {{e#f}} c , len≡n) = f ⟦ e#f ⟧


  G-cong : ∀ {e f} {λ≡n : lambda (ln e) f ≡ n} → {c c' : Σ (chain (ln e) f) (λ c → len c ≡ n)}
                                                 → c ≈ c' → G {e} {f} {λ≡n} c ≡ G {e} {f} {λ≡n} c'
  G-cong {e} {.(ln e)} {λ≡n} {.([ ln e ]) , proj₂} {[ .(ln e) ] , proj₄} refl = ⊥-elim (n≢0 (sym proj₄))
  G-cong {e} {f} {λ≡n} {.(ln e ∷ proj₃) , proj₂} {_∷_ {ln x} .(ln e) {{e<>f}} {{e#f}} proj₃ , proj₄} refl = ⊥-elim (A-ln#eq e#f e<>f)
  G-cong {e} {f} {λ≡n} {.(ln e ∷ proj₃) , proj₂} {_∷_ {pt x} .(ln e) {{e<>f}} {{e#f}} proj₃ , proj₄} refl = refl 



  G-inverse : ∀ {e f} {λ≡n : lambda (ln e) f ≡ n} → P# e → Σ (chain (ln e) f) (λ c → len c ≡ n)
  G-inverse {e} {f} {λ≡n} (e₁ ⟦ p#l ⟧) = _∷_ (ln e) {{λ ()}} (sc (pt e₁) f) , 
                                          (≡begin
                                            suc (len (sc (pt e₁) f))
                                              ==⟨ cong suc sc-len-lambda ⟩
                                            suc (lambda (pt e₁) f)
                                              ==⟨ cong suc (lambda-pred {e#e₁ = p#l} {e<>e₁ = λ ()} λ≡n) ⟩
                                            suc (pred (lambda (ln e) f))
                                              ==⟨ suc∘pred≡id (<-≡-trans λ≡n n≥1) ⟩
                                            lambda (ln e) f
                                              ==⟨ λ≡n ⟩
                                            n ≡∎)
  
  G-inverse-cong : ∀ {e f} {λ≡n : lambda (ln e) f ≡ n} → {i j : P# e} → i ≡ j → G-inverse {e} {f} {λ≡n} i ≈ G-inverse {e} {f} {λ≡n} j
  G-inverse-cong {_} {_} {_} {.j} {j} refl = refl


  -- Proof that F is injective
  G-inj : ∀ {e f} {λ≡n : lambda (ln e) f ≡ n} → {c c' : Σ (chain (ln e) f) (λ c → len c ≡ n)} →
                      G {e} {f} {λ≡n} c ≡ G {e} {f} {λ≡n} c' → c ≈ c'
  G-inj {e} {.(ln e)} {λ≡n} {[ .(ln e) ] , proj₂} {[ .(ln e) ] , proj₄} eq = refl
  G-inj {e} {.(ln e)} {λ≡n} {[ .(ln e) ] , proj₂} {_∷_ {pt x} .(ln e) {{e<>f}} {{e#f}} proj₃ , proj₄} eq = ⊥-elim (n≢0 (sym proj₂))
  G-inj {e} {.(ln e)} {λ≡n} {[ .(ln e) ] , proj₂} {_∷_ {ln x} .(ln e) {{e<>f}} {{e#f}} proj₃ , proj₄} eq = ⊥-elim (A-ln#eq e#f e<>f)
  G-inj {e} {.(ln e)} {λ≡n} {_∷_ .(ln e) {{e<>f}} {{e#f}} proj₁ , proj₂} {[ .(ln e) ] , proj₄} eq = ⊥-elim (n≢0 (sym proj₄))
  G-inj {e} {f} {λ≡n} {_∷_ {pt .x₁} .(ln e) {{e<>f}} {{e#f}} c , len≡n} {_∷_ {pt x₁} .(ln e) {{e<>f₁}} {{e#f₁}} c' , len≡n'} refl = 
                                                                                                                   chains≡⇒≈
                                                                                                                     (cong (λ x → _∷_ (ln e) {{e<>f = e<>f}} {{e#f = e#f}} x)
                                                                                                                                      (A₂ (c , ≡⇒≤ len≡n) (c' , ≡⇒≤ len≡n')))

  G-inj {e} {f} {λ≡n} {_∷_ {pt x} .(ln e) {{e<>f}} {{e#f}} proj₁ , proj₂} {_∷_ {ln x₁} .(ln e) {{e<>f₁}} {{e#f₁}} proj₃ , proj₄} eq = ⊥-elim (A-ln#eq e#f₁ e<>f₁)
  G-inj {e} {f} {λ≡n} {_∷_ {ln x} .(ln e) {{e<>f}} {{e#f}} proj₁ , proj₂} {_∷_ .(ln e) {{e<>f₁}} {{e#f₁}} proj₃ , proj₄} eq = ⊥-elim (A-ln#eq e#f e<>f)
 


 
  G-left-inv : ∀ {e f} → (λ≡n : lambda (ln e) f ≡ n) (x : Σ (chain (ln e) f) (λ c → len c ≡ n)) → proj₁ (G-inverse {e} {f} {λ≡n} (G {e} {f} {λ≡n} x)) ≡ proj₁ (x)
  G-left-inv {e} p ([ .(ln e) ] , proj₂) = ⊥-elim (n≢0 (sym proj₂))
  G-left-inv {e} p (_∷_ {ln x} .(ln e) {{e<>f}} {{e#f}} proj₁ , proj₂) = ⊥-elim (A-ln#eq e#f e<>f)
  G-left-inv {e} {f} p (_∷_ {pt e₁} .(ln e) {{e<>f}} {{e#f}} proj₁ , proj₂) = cong (_∷_ (ln e))
             (A₂ ((sc (pt e₁) f) , (begin suc (len (sc (pt e₁) f)) ≡⟨ cong suc sc-len-lambda ⟩
                                            suc (lambda (pt e₁) f) ≡⟨ cong suc (lambda-pred {(ln e)} {(pt e₁)} {f} {e#f} {e<>f} p) ⟩
                                            suc (pred (lambda (ln e) f)) ≡⟨ suc∘pred≡id (<-≡-trans p n≥1) ⟩ lambda (ln e) f ≡⟨ p ⟩ (n ∎)))
             (proj₁ , ≡⇒≤ proj₂)) 


  lemma2-1a : ∀ {e f} → lambda (ln e) f ≡ n → Inverse (ChainsWithProperty (ln e) f (λ c → len c ≡ n)) (setoid (P# e))
  lemma2-1a {e} {f} λ≡n = record { to = record { _⟨$⟩_ = G {e} {f} {λ≡n}; cong = G-cong }; from = record {
                                              _⟨$⟩_ = G-inverse {e} {f} {λ≡n};
                                              cong = G-inverse-cong {e} {f} {λ≡n} };
                                              inverse-of = record { left-inverse-of = λ x → chains≡⇒≈ (G-left-inv λ≡n x); right-inverse-of = λ x → refl } }

