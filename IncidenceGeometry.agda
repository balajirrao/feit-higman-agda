module IncidenceGeometry (O : Set) (_#_ : O → O → Set) where
  open import Data.Nat
  open import Data.Unit using (⊤; tt)
  open import Data.Empty
  open import Data.Product
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; _≢_; subst; subst₂; sym; trans)
  open import Data.Maybe
  open import Data.Sum
  open import Data.Bool
  open import Relation.Binary
  open import Relation.Nullary.Core
  
  open import Misc

  postulate
    #-refl : ∀ {e} → e # e
    #-sym : ∀ {e f} → e # f → f # e

  fst : ∀ {e f} → e # f → O
  fst {e} {_} _ = e

  snd : ∀ {e f} → e # f → O
  snd {_} {f} _ = f
  
  infixl 5 _∷_  
 
  data chain : O → O → Set
  last : ∀ {e f} → chain e f → O
  head : ∀ {e f} → chain e f → O
  
  data chain where
    [_] : (e : O) → chain e e
    _∷_ :{e f : O} → (c : chain e f) → (g : O) → .{p : f # g} → chain e g

  last {_} {f} _ = f
  head {e}     _ = e

  len : ∀ {e f} → chain e f → ℕ
  len [ _ ] = zero
  len (c ∷ _) = suc (len c)

  nonempty : ∀ {e f} → chain e f → Set
  nonempty [ _ ] = ⊥
  nonempty (_ ∷ _) = ⊤

  last-but-one : ∀ {e f} → (c : chain e f) → (ne : nonempty c) → O
  last-but-one [ _ ] ne = ⊥-elim ne
  last-but-one (c ∷ _) _ = last c

  init : ∀ {e f} (c : chain e f) → (ne : nonempty c) → chain e (last-but-one c ne)
  init [ _ ] ne = ⊥-elim ne
  init (c ∷ _) _ = c

  infixl 5 _++_ 
  _++_ : ∀ {e f g} → (c₁ : chain e f) → (c₂ : chain f g) → chain e g
  (c₁ ++ [ _ ])  = c₁
  (c₁ ++ (c₂ ∷ e) {p}) = (c₁ ++ c₂ ∷ e) {p}
 
  ++-nonempty : ∀ {e f g} → (c₁ : chain e f) → (c₂ : chain f g) →
                (nonempty c₁) → (nonempty (c₁ ++ c₂))
  ++-nonempty c₁ [ _ ] p = p
  ++-nonempty _ (_ ∷ _) _ = tt

  ++-[] : ∀ {e f} → (c : chain e f) → [ e ] ++ c ≡ c
  ++-[] [ _ ] = refl
  ++-[] (c ∷ _) rewrite (++-[] c) = refl

  ++-assoc : ∀ {e f g h} (c₁ : chain e f) (c₂ : chain f g) (c₃ : chain g h) →
               c₁ ++ (c₂ ++ c₃) ≡ c₁ ++ c₂ ++ c₃  
  ++-assoc _ c₂ [ _ ] rewrite (++-[] c₂) = refl
  ++-assoc c₁ c₂ (c₃ ∷ _) rewrite (++-assoc c₁ c₂ c₃) = refl

  
  ++-len : ∀ {e f g} → (c₁ : chain e f) → (c₂ : chain f g) →
             (len c₁) + (len c₂) ≡ len (c₁ ++ c₂)
  ++-len c₁ [ _ ] rewrite (+-com (len c₁) 0) = refl
  ++-len c₁ (c₂ ∷ _) rewrite (sym (++-len c₁ c₂))
                             = sym (+-suc (len c₁) (len c₂))
  
  rev : ∀ {e f} → (c : chain e f) → (chain f e)
  rev [ x ] = [ x ]
  rev ((c ∷ _) {p} ) = ([ _ ] ∷ (last c)) {#-sym p} ++ rev c
 
  rev-++ : ∀ {e f g} → (c₁ : chain e f) → (c₂ : chain f g) →
             rev (c₁ ++ c₂) ≡ (rev c₂) ++ (rev c₁)
  rev-++ c₁ [ _ ] = sym (++-[] (rev c₁))
  rev-++ c₁ ((c₂ ∷ _) {p}) rewrite 
            rev-++ c₁ c₂ |
            ++-assoc (([ _ ] ∷ last c₂) {#-sym p}) (rev c₂) (rev c₁) = refl

  rev-id : ∀ {e f} → (c : chain e f) → rev (rev c) ≡ c
  rev-id [ _ ] = refl
  rev-id (c ∷ _) with (rev-++ ([ _ ] ∷ (last c)) (rev c))
  ... | p rewrite (rev-id c) = p

  len-rev : ∀ {e f} → (c : chain e f) → (len c) ≡ len (rev c)
  len-rev [ _ ] = refl
  len-rev (c ∷ f) rewrite (len-rev c) = ++-len ([ f ] ∷ last c) (rev c)

  rev-nonempty : ∀ {e f} → (c : chain e f) → nonempty c → nonempty (rev c)
  rev-nonempty [ _ ] p = p
  rev-nonempty (c ∷ f) p₁ = ++-nonempty ([ f ] ∷ (last c)) (rev c) tt

  -- Second element of the chain
  second : ∀ {e f} → (c : chain e f) → (ne : nonempty c) → O
  second c p rewrite (len-rev c) = last-but-one (rev c) (rev-nonempty c p)

  -- tail of the chain
  tail : ∀ {e f} (c : chain e f) → (ne : nonempty c) → (chain (second c ne) f)
  tail c p rewrite (len-rev c) = rev (init (rev c) (rev-nonempty c p))

  infixl 3 _∈_
  _∈_ : ∀ {e f} → O → chain e f → Set
  x ∈ ([ e ]) = x ≡ e
  x ∈ (c ∷ f) = x ≡ f ⊎ x ∈ c
  
  irred : ∀ {e f} → chain e f → Set
  irred [ _ ] = ⊤
  irred (([ e ]) ∷ f) = (e ≡ f) → ⊥
  irred ((c ∷ e) {p} ∷ f) = (.(last c # f) → ⊥) × irred ((c ∷ e) {p})

  irred-∷ : ∀ {e f} → (c : chain e f) → (g : O) →
              .{f#g : f # g} → irred ((c ∷ g) {f#g}) → f ≡ g → ⊥
  irred-∷ [ _ ] _ ic eq = ic eq
  irred-∷ ((c ∷ f) {p}) g ic eq = proj₁ ic (subst (_#_ (last c)) eq p)

  irred-++ : ∀ {h} → (e f g : O) → .{e#f : e # f} → .{f#g : f # g} →
               (irred ((([ e ] ∷ f) {e#f} ∷ g) {f#g})) → (c : chain g h) →
               irred (([ f ] ∷ g) {f#g} ++ c) →
               irred (([ e ] ∷ f) {e#f} ++ (([ f ] ∷ g) {f#g} ++ c))
  irred-++ {h} e f .h x [ .h ] x₁ = x
  irred-++ {h} e f .f₁ x (_∷_ {.f₁} {f₁} [ .f₁ ] .h) x₁ = proj₁ x₁ , x
  irred-++ {h} e f g x (_∷_ {.g} {f₁} (c ∷ .f₁) .h) x₁ = proj₁ x₁ , irred-++ e f g x (c ∷ f₁) (proj₂ x₁)

  irred-init : ∀ {e f} → (c : chain e f) → (ne : nonempty c) → irred c → irred (init c ne)
  irred-init [ _ ] ne ic = ⊥-elim ne
  irred-init (c ∷ _) _ ic with c
  ... | [ _ ] = tt
  ... | _ ∷ _ = proj₂ ic  

  irred-rev : ∀ {e f} → (c : chain e f) → irred c → irred (rev c)
  irred-rev [ _ ] _ = tt
  irred-rev ([ _ ] ∷ _) ic = λ t → ic (sym t)
  irred-rev (((c ∷ e) {p}) ∷ f)  ic with irred-rev (c ∷ e) (proj₂ ic)
  ... | q = irred-++ f e (last c) ((λ t → proj₁ ic (#-sym t)) ,
            (λ t → proj₁ ic (subst (_#_ (last c)) (sym t) p))) (rev c) q

  shortest : ∀ {e f} → (c : chain e f) → Set
  shortest {e} {f} c = (c' : chain e f) → (len c) ≯ (len c')
                                    
  shortest-irred-helper : ∀ {e f} → .(e # f) →
                        ((c' : chain e f) → suc (len c') ≤ 1 → ⊥) → (e ≡ f) → ⊥
  shortest-irred-helper {f} _ p refl = p [ f ] (s≤s z≤n)

  shortest-irred : ∀ {e f} → (c : chain e f) → shortest c → irred c
  shortest-irred [ _ ] s = Data.Unit.tt
  shortest-irred (([ _ ] ∷ _) {p}) s = shortest-irred-helper p s
  shortest-irred ((c ∷ g ∷ h) {g#h}) s =
                     (λ t → s ((c ∷ h) {t}) (m≤m)) ,
                     shortest-irred (c ∷ g)
                       (λ c' z → s ((c' ∷ h) {g#h}) (s≤s z))

  len-init-suc : ∀ {e f} → (c : chain e f) → (ne : nonempty c) →
                   (len c) ≡ suc (len (init c ne))
  len-init-suc [ _ ] ne = ⊥-elim ne
  len-init-suc (_ ∷ _) _ = refl
   



