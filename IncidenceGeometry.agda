module IncidenceGeometry (O : Set) (_#_ : O → O → Set) where
  open import Data.Nat -- hiding (_<_)
  open import Data.Unit using (⊤)
  open import Data.Empty
  open import Data.Product
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; _≢_; subst; subst₂; sym)
  open import Data.Maybe
  open import Data.Sum
  open import Data.Bool
  open import Relation.Binary

  postulate
    #-refl : ∀ {e} → e # e
    #-sym : ∀ {e f} → e # f → f # e

  fst : ∀ {e f} → e # f → O
  fst {e} {_} _ = e

  snd : ∀ {e f} → e # f → O
  snd {_} {f} _ = f
  
  infixl 5 _∷_

  data chain : O → O → Set where
    [] : ∀ {e} → chain e e
    _∷_ : ∀ {e₀ e f} → (c : chain e₀ e) → (e#f : e # f) → chain e₀ f

  [_] : ∀ {e f} → (e#f : e # f) → chain e f
  [ e#f ] = [] ∷ e#f

  len : ∀ {e f} → chain e f → ℕ
  len [] = zero
  len (c ∷ f#g) = suc (len c)

  join : ∀ {e f g} → chain e f → chain f g → chain e g
  join c₁ [] = c₁
  join c₁ (c₂ ∷ f#g) = join c₁ c₂ ∷ f#g

  head : ∀ {e f} → chain e f → O
  head {e} {_} _ = e

  last : ∀ {e f} → chain e f → O
  last {_} {f} _ = f 

  last-but-one : ∀ {e f} (c : chain e f) → (ne : len c ≢ zero) → O
  last-but-one [] ne = ⊥-elim (ne refl) 
  last-but-one (c ∷ e#f) _ = last c

  init : ∀ {e f} (c : chain e f) → (ne : len c ≢ zero) → chain e (last-but-one c ne)
  init [] ne = ⊥-elim (ne refl)
  init (c ∷ e#f) _ = c

  infixl 3 _∈_
  
  _∈_ : ∀ {e f} → O → chain e f → Set
  x ∈ ([] {e}) = x ≡ e
  x ∈ c ∷ e#f = x ≡ snd e#f ⊎ x ∈ c
  
  isbefore : ∀ {e f x y} {c : chain e f} → x ∈ c → y ∈ c → Set
  isbefore {.f} {f} {x} {y} {[]} x₁ x₂ = ⊥
  isbefore {e} {f} {x} {y} {c ∷ e#f} (inj₁ x₁) (inj₁ x₂) = ⊥
  isbefore {e} {f} {x} {y} {c ∷ e#f} (inj₁ x₁) (inj₂ y₁) = ⊥
  isbefore {e} {f} {x} {y} {c ∷ e#f} (inj₂ y₁) (inj₁ x₁) = x ≡ (fst e#f)
  isbefore {e} {f} {x} {y} {c ∷ e#f} (inj₂ y₁) (inj₂ y₂) = isbefore y₁ y₂
  
  isbefore-# : ∀ {e f x y} → (c : chain e f) → (x∈c : x ∈ c) (y∈c : y ∈ c) → isbefore x∈c y∈c → x # y
  isbefore-# [] x∈c y∈c x₁ = subst₂ (λ m n → m # n) (sym x∈c) (sym y∈c) #-refl
  isbefore-# (c ∷ e#f) (inj₁ x₁) (inj₁ x₂) x₃ = ⊥-elim x₃
  isbefore-# (c ∷ e#f) (inj₁ x₁) (inj₂ y₁) x₂ = ⊥-elim x₂
  isbefore-# (c ∷ e#f) (inj₂ y₁) (inj₁ x₁) x₂ = subst₂ (λ m n → m # n) (sym x₂) (sym x₁) e#f
  isbefore-# (c ∷ e#f) (inj₂ y₁) (inj₂ y₂) x₁ = isbefore-# c y₁ y₂ x₁

  irred : ∀ {e f} → chain e f → Set
  irred [] = ⊤
  irred ([] ∷ e#f) = fst e#f ≢ snd e#f
  irred (c ∷ e#f ∷ f#g) = (fst e#f # snd f#g → ⊥) × irred (c ∷ e#f)

  irred-init : ∀ {e f} → (c : chain e f) → (ne : len c ≢ zero) → irred c → irred (init c ne)
  irred-init [] ne ic = ⊥-elim (ne refl)
  irred-init (c ∷ e#f) _ ic with c
  irred-init (c ∷ e#f) ne ic | [] = Data.Unit.tt
  irred-init (c ∷ e#f₁) ne ic | c' ∷ e#f = proj₂ ic
  --irred-init (c ∷ e#f ∷ e#f₁) ne ic = proj₂ ic

  --postulate
  --ƛ : O → O → ℕ
  --ƛ-smallest : ∀ {e f} {c : chain e f} → ((ƛ e f) ≤ (len c)) × (∀ {m} → (m ≤ (len c)) → m ≤ (ƛ e f))
  
  shortest : ∀ {e f} → (c : chain e f) → Set
  shortest {e} {f} c = (c' : chain e f) → (len c) ≯ (len c')
                                    
  sh-irred-helper : ∀ {e f} → e # f → ( (c' : chain e f) → suc (len c') ≤ 1 → ⊥) → e ≡ f → ⊥
  sh-irred-helper f₁ p refl = p [] (s≤s z≤n)

  m≤m : ∀ m → m ≤ m
  m≤m zero = z≤n
  m≤m (suc m) = s≤s (m≤m m)

  shortest-irred : ∀ {e f} → (c : chain e f) → shortest c → irred c
  shortest-irred [] s = Data.Unit.tt
  shortest-irred ([] ∷ e#f) s = sh-irred-helper e#f s
  shortest-irred (c ∷ e#f ∷ e#f₁) s = (λ e₂#f → s (c ∷ e₂#f) (m≤m (suc (suc (len c))))) , shortest-irred (c ∷ e#f) (λ c₁ z → s (c₁ ∷ e#f₁) (s≤s z)) 

  
