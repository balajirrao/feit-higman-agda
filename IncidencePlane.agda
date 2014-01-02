
module IncidencePlane where
  open import Data.Bool using (Bool; true; false)
  open import Data.Nat
  open import Data.Unit using (⊤; tt)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Product
  open import
    Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; subst₂; sym; trans; _≢_)
  open import Data.Sum using (_⊎_) renaming (inj₁ to injP; inj₂ to injL)
  open import Data.Maybe

  open import Relation.Nullary.Core
 
  --private
  postulate
    P L : Set
    
  O : Set
  O = P ⊎ L
 
  isP : O → Bool
  isP (injP x) = true
  isP (injL y) = false

  isL : O → Bool
  isL (injP x) = false
  isL (injL y) = true

  infix 3 _#_
  
  postulate
    _#_ : O → O → Set
    eq-#-P : {e f : P} → .((injP e) # (injP f)) → e ≡ f
    eq-#-L : {e f : L} → .((injL e) # (injL f)) → e ≡ f

  import IncidenceGeometry as IG
  open IG O _#_

  module EvenOdd where

    open import Data.Nat

    data Even : ℕ → Set
    data Odd : ℕ → Set 

    data Even where
      evenZero : Even 0
      oddEven : {n : ℕ} → Odd n → Even (suc n)
    
    data Odd where
      evenOdd : {n : ℕ} → Even n → Odd (suc n)

    evenSuc : ∀ {m} → Even m → Even (suc (suc m))
    evenSuc {zero} p = oddEven (evenOdd p)
    evenSuc {suc m} p = oddEven (evenOdd p)
  
    oddSuc : ∀ {m} → Odd m → Odd (suc (suc m))
    oddSuc {zero} p = evenOdd (oddEven p)
    oddSuc {suc m} p = evenOdd (oddEven p)
  
    oddOne : Odd 1
    oddOne = evenOdd evenZero

    aa : ∀ x → Even x → Odd x → ⊥
    aa zero e ()
    aa (suc x) (oddEven x₁) (evenOdd x₂) = aa x x₂ x₁

  open EvenOdd
 
  irred-PP-even : ∀ {p p'} → (c : chain (injP p) (injP p')) → irred c → Even (len c)
  irred-PL-odd : ∀ {p l} → (c : chain (injP p) (injL l)) → irred c → Odd (len c)

  irred-PP-even [ ._ ] _ = evenZero
  irred-PP-even (c ∷ ._) ic with (last c)
  irred-PP-even {p} {p'} ((c IG.∷ .(injP p')) {q}) ic | injP x = ⊥-elim (irred-∷ c (injP p') ic (cong injP (eq-#-P q)))
  irred-PP-even {p} {p'} (c IG.∷ .(injP p')) ic | injL y = oddEven (irred-PL-odd c (irred-init (c IG.∷ injP p') tt ic))

  irred-PL-odd {p} {l} (c IG.∷ .(injL l)) x with (last c)
  irred-PL-odd {p} {l} (c IG.∷ .(injL l)) x₁ | injP x = evenOdd (irred-PP-even c (irred-init (c IG.∷ injL l) tt x₁))
  irred-PL-odd {p} {l} ((c IG.∷ .(injL l)) {q}) x | injL y = ⊥-elim (irred-∷ c (injL l) x (cong injL (eq-#-L q)))

  irred-LL-even : ∀ {l l'} → (c : chain (injL l) (injL l')) → irred c → Even (len c)
  irred-LL-even {.l'} {l'} IG.[ .(injL l') ] x = evenZero
  irred-LL-even {l} {l'} (c IG.∷ .(injL l')) x with (last c)
  irred-LL-even {l} {l'} (c IG.∷ .(injL l')) x₁ | injP x rewrite (len-rev c) = oddEven (irred-PL-odd (rev c) (irred-rev c (irred-init (c IG.∷ injL l')  tt x₁)))
  irred-LL-even {l} {l'} ((c IG.∷ .(injL l')) {q}) x | injL y = ⊥-elim (irred-∷ c (injL l') x (cong injL (eq-#-L q)))
 
  shortest-PP-even : ∀ {p p'} → (c : chain (injP p) (injP p')) → shortest c → Even (len c)
  shortest-PP-even c sc = irred-PP-even c (shortest-irred c sc)

  shortest-PL-odd : ∀ {p l} → (c : chain (injP p) (injL l)) → shortest c → Odd (len c)
  shortest-PL-odd c sc = irred-PL-odd c (shortest-irred c sc)

  module GenPolygon (n : ℕ) where
    postulate
      A₁ : ∀ (e f : O) → ∃ {A = chain e f} (λ c → (len  c) ≤ n)
      A₂ : ∀ (e f : O) → Maybe (∃! {A = chain e f} _≡_ (λ c → irred c × len c < n)) 
  
    open Data.Nat.≤-Reasoning
 
    len-shortest-≤n : ∀ {e f} → (c : chain e f) → shortest c → len c > n → ⊥
    len-shortest-≤n {e} {f} c sc l with proj₁ (A₁ e f) | proj₂(A₁ e f) 
    ... | c' | p  = sc c' (begin suc (len c') ≤⟨ s≤s p ⟩ (relTo l))

    nondegen : ∀ {e f} → Set
    nondegen {e} {f} = ∃ {A = chain e f} (λ c → shortest c × (len c) ≡ n)

    closed-even : ∀ {e} → (c : chain e e) → irred c → Even (len c)
    closed-even {injP x} c = irred-PP-even c
    closed-even {injL y} c = irred-LL-even c    

    mid : ∀ {e f} → (c : chain e f) → Even (len c) → O
    mid [ e ] p = e
    mid (IG.[ e ] IG.∷ f) (oddEven ())
    mid ([ e ] ∷ f ∷ g) p = f
    mid (((c ∷ f) {c#f}) ∷ g) (oddEven (evenOdd p)) = mid (init ((c ∷ f) {c#f}) tt) p
