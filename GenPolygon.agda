open import Relation.Binary
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product

open import Data.Empty

open import Data.Unit using (⊤; tt)
open import Data.Unit.Core

open import Data.Fin using (Fin)

open import Relation.Binary.PropositionalEquality as PropEq
--open ≡-Reasoning
open Data.Nat.≤-Reasoning

open import Relation.Nullary.Core

open import Function.Bijection
open import Function.Equality hiding (setoid; _∘_)

open import Misc

import Level

module GenPolygon where
  open import IncidenceGeometry public

  postulate
    _n : Hidden ℕ

  n : ℕ
  n = reveal _n
  
  postulate
    n≰2 : n ≰ 2
    s t : ℕ
  
  n>2 : n > 2
  n>2 = ≰⇒> n≰2
 
  -- Axioms for incidence plane. Two points (or lines) can be incident only when they are equal
  postulate
    A-pt#eq : ∀ {e f} → .((pt e) # (pt f)) → .((pt e) ≡ (pt f) → ⊥) → ⊥
    A-ln#eq : ∀ {e f} → .((ln e) # (ln f)) → .((ln e) ≡ (ln f) → ⊥) → ⊥

  infixr 5 _∷_

  -- A p-chain is between two points. It can grow only by point-line pair
  data p-chain : P → O → Set
  data l-chain : L → O → Set

  -- 
  data p-chain where
   [_] : (e : P) → p-chain e (pt e)
   _∷_  : ∀ {f g} (e : P) .{{e#f : (pt e) # (ln f)}} (c : l-chain f g) → p-chain e g

  data l-chain where
    [_] : (e : L) → l-chain e (ln e)
    _∷_  : ∀ {f g} (e : L) .{{e#f : (ln e) # (pt f)}} (c : p-chain f g) → l-chain e g
    
  p-len : ∀ {e f} → p-chain e f → ℕ
  l-len : ∀ {e f} → l-chain e f → ℕ
  p-len {e} [ .e ] = zero
  p-len {e} (_∷_ .e {{e#f}} c) = suc (l-len c)
  l-len {e} [ .e ] = zero
  l-len {e} (_∷_ .e {{e#f}} c) = suc (p-len c)

  -- Convert a p-chain to a chain
  pc-to-c : ∀ {e f} (c : p-chain e f) → chain (pt e) f
  lc-to-c : ∀ {e f} (c : l-chain e f) → chain (ln e) f
  
  pc-to-c [ e ]  = [ (pt e) ] 
  pc-to-c (_∷_ {e₁} e c) =  _∷_ (pt e) {{λ ()}} (lc-to-c c)

  lc-to-c [ e ] = [ (ln e) ]
  lc-to-c (_∷_ {e₁} e c) = _∷_ (ln e) {{λ ()}} (pc-to-c c)

  -- Convert a chain to a pchain
  c-to-pc : ∀ {e f} (c : chain (pt e) f) → p-chain e f
  c-to-lc : ∀ {e f} (c : chain (ln e) f) → l-chain e f  
  c-to-pc {e} [ .(pt e) ] = [ e ]
  c-to-pc {e} (_∷_ {pt f} .(pt e) {{e<>f}} {{e#f}} c) = ⊥-elim (A-pt#eq e#f e<>f)
  c-to-pc {e} (_∷_ {ln f} .(pt e) {{e<>f}} {{e#f}} c) = e ∷ c-to-lc c
  c-to-lc {e} [ .(ln e) ] = [ e ]
  c-to-lc {e} (_∷_ {pt x} .(ln e) {{e<>f}} {{e#f}} c) = e ∷ c-to-pc c
  c-to-lc {e} (_∷_ {ln x} .(ln e) {{e<>f}} {{e#f}} c) = ⊥-elim (A-ln#eq e#f e<>f)

  plen-len : ∀ {e f} (pc : p-chain e f) → p-len pc ≡ len (pc-to-c pc)
  llen-len : ∀ {e f} (lc : l-chain e f) → l-len lc ≡ len (lc-to-c lc)
  plen-len {e} [ .e ] = refl
  plen-len {e} (_∷_ .e {{e#f}} c) = PropEq.cong suc (llen-len c)
  llen-len {e} [ .e ] = refl
  llen-len {e} (_∷_ .e {{e#f}} c) = PropEq.cong suc (plen-len c)

  pcc-id : ∀ {e f} → (c : chain (pt e) f) → pc-to-c (c-to-pc c) ≡ c
  lcc-id : ∀ {e f} → (c : chain (ln e) f) → lc-to-c (c-to-lc c) ≡ c
  pcc-id {e} [ .(pt e) ] = refl
  pcc-id {e} (_∷_ {pt f} .(pt e) {{e<>f}} {{e#f}} c) = ⊥-elim (A-pt#eq e#f e<>f)
  pcc-id {e} (_∷_ {ln x} .(pt e) c) = PropEq.cong (λ z → (_∷_ (pt e) z)) (lcc-id c) 
  lcc-id {e} [ .(ln e) ] = refl
  lcc-id {e} (_∷_ {pt f} .(ln e) c) = PropEq.cong (λ z → (_∷_ (ln e) z)) (pcc-id c)
  lcc-id {e} (_∷_ {ln f} .(ln e) {{e<>f}} {{e#f}} c) = ⊥-elim (A-ln#eq e#f e<>f)
 {-  
  pp-len-even : ∀ {e f} → (pc : p-chain e (pt f)) → Even (p-len pc)
  lp-len-odd : ∀ {e f} → (lc : l-chain e (pt f)) → Odd (l-len lc)
  pp-len-even {.f} {f} [ .f ] = evenZero
  pp-len-even {e} (_∷_ .e {{e#f}} c) = oddEven (lp-len-odd c)
  lp-len-odd {e} (_∷_ .e {{e#f}} c) = evenOdd (pp-len-even c)

  ll-len-even : ∀ {e f} → (lc : l-chain e (ln f)) → Even (l-len lc)
  pl-len-odd : ∀ {e f} → (pc : p-chain e (ln f)) → Odd (p-len pc)
  ll-len-even {.f} {f} [ .f ] = evenZero
  ll-len-even {e} (_∷_ .e {{e#f}} c) = oddEven (pl-len-odd c)
  pl-len-odd {e} (_∷_ .e {{e#f}} c) = evenOdd (ll-len-even c)
-}
  -- That a len-lambda chain exists between any two elements of O and they have length lambda e f

  spc : (e : P) (f : O) → p-chain e f
  spc e f = c-to-pc (sc (pt e) f)

  spc-len-lambda : ∀ {e f} → p-len (spc e f) ≡ (lambda (pt e) f)
  spc-len-lambda {e} {f} = trans (plen-len (spc e f)) (trans (PropEq.cong len (pcc-id (sc (pt e) f))) sc-len-lambda)
  
  slc : (e : L) (f : O) → l-chain e f
  slc e f = c-to-lc (sc (ln e) f)

  slc-len-lambda : ∀ {e f} → l-len (slc e f) ≡ (lambda (ln e) f)
  slc-len-lambda {e} {f} rewrite (lcc-id (sc (ln e) f)) = trans (llen-len (slc e f)) (trans (PropEq.cong len (lcc-id (sc (ln e) f))) sc-len-lambda)

  -- TODO : Make c implicit
  pp-len-even : ∀ {e f} → (c : chain (pt e) (pt f)) → Even (len c)
  lp-len-odd : ∀ {e f} → (c : chain (ln e) (pt f)) → Odd (len c)
  pp-len-even {.f} {f} [ .( pt f) ] = evenZero
  pp-len-even {e} (_∷_ {pt x} .(pt e) {{e<>f}} {{e#f}} c) = ⊥-elim (A-pt#eq e#f e<>f)
  pp-len-even {e} (_∷_ {ln x} .(pt e) {{e<>f}} {{e#f}} c) = oddEven (lp-len-odd c)
  lp-len-odd {e} (_∷_ {pt x} .(ln e) {{e<>f}} {{e#f}} c) = evenOdd (pp-len-even c)
  lp-len-odd {e} (_∷_ {ln x} .(ln e) {{e<>f}} {{e#f}} c) = ⊥-elim (A-ln#eq  e#f e<>f)

  ll-len-even : ∀ {e f} → (c : chain (ln e) (ln f)) → Even (len c)
  pl-len-odd : ∀ {e f} → (c : chain (pt e) (ln f)) → Odd (len c)
  ll-len-even {.f} {f} [ .(ln f) ] = evenZero
  ll-len-even {e} (_∷_ {pt x} .(ln e) {{e<>f}} {{e#f}} c) = oddEven (pl-len-odd c)
  ll-len-even {e} (_∷_ {ln x} .(ln e) {{e<>f}} {{e#f}} c) = ⊥-elim (A-ln#eq e#f e<>f)
  pl-len-odd {e} (_∷_ {pt x} .(pt e) {{e<>f}} {{e#f}} c) = ⊥-elim (A-pt#eq e#f e<>f)
  pl-len-odd {e} (_∷_ {ln x} .(pt e) {{e<>f}} {{e#f}} c) = evenOdd (ll-len-even c)


  ChainsWithProperty : ∀ {e f} (prop : chain e f → Set) → Set
  ChainsWithProperty {e} {f} prop = Σ (chain e f) prop

  ChainsWithPropertySetoid : ∀ {e f} (prop : chain e f → Set)  → Setoid _ _
  ChainsWithPropertySetoid prop = record { Carrier = ChainsWithProperty prop; _≈_ = λ a b → (proj₁ a) ≡ (proj₁ b);
                                           isEquivalence = record { refl = refl; sym = sym; trans = trans } }

  _≈_ : ∀ {e f} {prop : chain e f → Set} (c c' : Σ (chain e f) prop) → Set
  _≈_ {prop = prop} = Setoid._≈_ (ChainsWithPropertySetoid prop)

  -- A₂ : There exists at most one irreducible chain of length less than n from e to f
  postulate
    A₁ : (e f : O) → Σ (chain e f) (λ c → len c ≤ n)
    A₂ : ∀ {e f} (c c' : Σ (chain e f) (λ c → len c < n)) → (proj₁ c) ≡ (proj₁ c')
 
  -- A₁ imples that the shortest length between any two elements can't be more than n
  A₁' :  ∀ {e f} → ((lambda e f) > n) → ⊥
  A₁' {e} {f} p = lambda-shortest (proj₁ (A₁ e f))
                  (begin
                    suc (len (proj₁ (A₁ e f)))
                      ≤⟨ s≤s (proj₂ (A₁ e f)) ⟩
                    suc (reveal _n)
                      ≤⟨ p ⟩
                    lambda e f
                  ∎)

  -- Set of all lines incident with a given point.
  record L# (p : P) : Set where
    constructor _⟦_⟧
    field
      #l : L
      .p#l : (pt p) # (ln #l)
  open L# public

  -- Set of all points incident with a given line.
  record P# (l : L) : Set where
    constructor _⟦_⟧
    field
      #p : P
      .l#p : (ln l) # (pt #p)
  open P# public

  postulate
    B₁ : (l : L) → Bijection (setoid (P# l)) (setoid (Fin (s + 1)))
    B₂ : (p : P) → Bijection (setoid (L# p)) (setoid (Fin (t + 1)))

  -- There exists a f with lambda e f ≡ n
  postulate
    GP : (e : O) → Σ O (λ f → lambda e f ≡ n)

  pp-lambda-even : ∀ {e f} → Even ( lambda (pt e) (pt f) )
  pp-lambda-even {e} {f} = even≡ sc-len-lambda (pp-len-even (sc (pt e) (pt f)))

  rho : (e f : P) → ℕ
  rho e f = ⌊ (lambda (pt e) (pt f)) /2⌋

  rho-zero : ∀ {e} → rho e e ≡ 0
  rho-zero {e} rewrite (lambda-zero {pt e}) = refl

  -- rho ≡ 0 between two points implies the points are equal
  rho-zero-eq : ∀ {e f} → rho e f ≡ zero → e ≡ f
  rho-zero-eq {e} {f} p with (lambda (pt e) (pt f)) | sc (pt e) (pt f) | sc-len-lambda {pt e} {pt f}
  rho-zero-eq {.f} {f} p | zero | [ .(pt f) ] | b = refl
  rho-zero-eq {e} p | zero | _∷_ .(pt e) {{e<>f}} {{e#f}} a | ()
  rho-zero-eq {.f} {f} p | suc zero | [ .(pt f) ] | ()
  rho-zero-eq {e} {f} refl | suc zero | _∷_ .(pt e) {{e<>f}} {{e#f}} [ .(pt f) ] | b = ⊥-elim (A-pt#eq e#f e<>f)
  rho-zero-eq {e} refl | suc zero | _∷_ {f₁} .(pt e) {{e<>f}} {{e#f}} (_∷_ .f₁ {{e<>f₁}} {{e#f₁}} a) | ()
  rho-zero-eq () | suc (suc z) | a | _
