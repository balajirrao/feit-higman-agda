module IncidencePlane where
  open import Data.Bool using (Bool; true; false)
  open import Data.Nat
  open import Data.Unit hiding (_≤_)
  open import Data.Empty
  open import Data.Product
  open import
    Relation.Binary.PropositionalEquality
  open import Data.Sum
  open import Data.Maybe

  open import Relation.Nullary.Core

  open import Misc
 
  --private
  postulate
    P L : Set
    
  data O : Set where
    pt : (p : P) → O
    ln : (l : L) → O
  
  alt-type : O → Set
  alt-type (pt _) = L
  alt-type (ln _) = P

  alt-inj : (x : O) → (alt-type x) → O
  alt-inj (pt _) = ln
  alt-inj (ln _) = pt

  data _#_ : O → O → Set where
    #symP : ∀ {p l} → (pt p) # (ln l) → (ln l) # (pt p)
    #symL : ∀ {l p} → (ln l) # (pt p) → (pt p) # (ln l) 
    #refl : ∀ {e} → e # e  

  #sym-all : ∀ {e f} → e # f → f # e
  #sym-all {pt .p₁} {pt p₁} #refl = #refl
  #sym-all {pt p} {ln l} p₁ = #symP p₁
  #sym-all {ln l} {pt p} p₁ = #symL p₁
  #sym-all {ln .l₁} {ln l₁} #refl = #refl

  import IncidenceGeometry as IG
  open IG O _#_ #refl #sym-all
  
  data alt-chain : O → O → ℕ → Set where
    alt2 : ∀ {x y} .(p : x # (alt-inj x y)) → alt-chain x (alt-inj x y) 1
    alts : ∀ {e f g k} .(p : e # (alt-inj e f)) (c : alt-chain (alt-inj e f) g k) → alt-chain e g (suc k)

  iz-alt : ∀ {e f g} (e#f : e # f) (f#g : f # g) (¬e#g : e # g → ⊥) → alt-chain e g 2
  iz-alt (#symP p₁) (#symL q) r = alts (#symP p₁) (alt2 (#symL q))
  iz-alt (#symP p₁) #refl r = ⊥-elim (r (#symP p₁))
  iz-alt (#symL p₁) (#symP q) r = alts (#symL p₁) (alt2 (#symP q))
  iz-alt (#symL p₁) #refl r = ⊥-elim (r (#symL p₁))
  iz-alt #refl (#symP q) r = ⊥-elim (r (#symP q))
  iz-alt #refl (#symL q) r = ⊥-elim (r (#symL q))
  iz-alt #refl #refl r = ⊥-elim (r #refl)

  irred-alt : ∀ {e f k} (c : chain e f k) (ic : irred c) → alt-chain e f k
  irred-alt ._ (iz e#f f#g ¬e#g) = iz-alt e#f f#g ¬e#g
  irred-alt ._ (is (#symP e#f) c _ ic _) = alts (#symP e#f) (irred-alt c ic)
  irred-alt ._ (is (#symL e#f) c _ ic _) = alts (#symL e#f) (irred-alt c ic)
  irred-alt ._ (is #refl nil _ () _)
  irred-alt ._ (is #refl (e#f ∷ c) (s≤s z≤n) _ ¬e#c) = ⊥-elim (¬e#c e#f)

  alt-pp-chain-even : ∀ {p p' k} (c : alt-chain (pt p) (pt p') k) → Even k
  alt-lp-chain-odd : ∀ {l p k} (c : alt-chain (ln l) (pt p) k) → Odd k

  alt-pp-chain-even (alts p₁ c) = oddEven (alt-lp-chain-odd c)
  alt-lp-chain-odd (alt2 _) = oddOne
  alt-lp-chain-odd (alts _ c) = evenOdd (alt-pp-chain-even c)

  alt-ll-chain-even :  ∀ {l l' k} (c : alt-chain (ln l) (ln l') k) → Even k
  alt-ll-chain-even (alts _ (alt2 _)) = oddEven (evenOdd evenZero)
  alt-ll-chain-even (alts _ (alts _ c)) = evenSuc (alt-ll-chain-even c)

  module GenPolygon (n : ℕ) where
    postulate
      A₁ : ∀ {k} (e f : O) → ∃ {A = chain e f k} (λ c → k ≤ n)
      A₂ : ∀ {e f k k'} (c : chain e f k) (c' : chain e f k') (p : k < n) (q : k' < n) → (c =c= c')
