open import Relation.Binary

open import Data.Nat
open import Data.Nat.Properties
--open Data.Nat.≤-Reasoning

open import Data.Fin using (Fin)

open import Data.Unit using (⊤; tt)
open import Data.Empty
open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Core

--open PropEq.≡-Reasoning 

open import Relation.Nullary.Core

open import Function.Equality hiding (setoid; cong; _∘_)
open import Function.Inverse hiding (sym)

open import Misc

open import GenPolygon

open import Data.Unit hiding (setoid; _≟_)

module Lemma-2-4 where
  
  -- Given that rho == r, M is the set of chains of length 2q
  M : ∀ {e f} → ℕ → ℕ → Set
  M {e} {f} r q = (rho e f) ≡ r × ChainsWithProperty {pt e} {pt f} (λ c → len c ≡ 2 * q)

  M-setoid : ∀ {e f} → ℕ → ℕ → Setoid _ _
  M-setoid {e} {f} r q = record { Carrier = M {e} {f} r q;
                                  _≈_ = λ x x₁ → proj₂ x ≈ proj₂ x₁;
                                  isEquivalence = record { refl = refl;
                                                           sym = sym;
                                                           trans = trans } }

  zero-len-chain-unique : ∀ {e} {c : chain (pt e) (pt e)} → len c ≡ 0 → c ≡ [ pt e ]
  zero-len-chain-unique {e} {[ .(pt e) ]} p = refl
  zero-len-chain-unique {e} {_∷_ .(pt e) {{e<>f}} {{e#f}} c} ()

  M₀₀ : ∀ {e f} → rho e f ≡ 0 → Inverse (M-setoid {e} {f} zero zero) (setoid ⊤)
  M₀₀ {e} {f} r≡0 rewrite rho-zero-eq r≡0 = record {
                                            to = record { _⟨$⟩_ = λ _ → tt; cong = λ _ → refl };
                                            from = record { _⟨$⟩_ = λ _ → rho-zero , ([ pt f ] , refl); cong = λ _ → refl };
                                            inverse-of = record {
                                                         left-inverse-of = λ x → sym (zero-len-chain-unique (proj₂ (proj₂ x)));
                                                         right-inverse-of = λ _ → refl } }

  M₀ᵣ : ∀ {e f} → (rho e f ≢ zero) → Inverse (M-setoid {e} {f} zero zero) (setoid ⊥)
  M₀ᵣ p = record { to = record { _⟨$⟩_ = λ x → p (proj₁ x); cong = λ {i} _ → ⊥-elim (p (proj₁ i)) };
                   from = record { _⟨$⟩_ = ⊥-elim; cong = λ {i} → ⊥-elim i };
                   inverse-of = record { left-inverse-of = λ x → ⊥-elim (p (proj₁ x));
                                         right-inverse-of = λ x → ⊥-elim x } }

