module IncidenceGeometry (O : Set) (_#_ : O → O → Set) where
  open import Data.Nat
  open import Data.Unit using (⊤)
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
  nonempty c = (len c ≢ 0)

  last-but-one : ∀ {e f} → (c : chain e f) → (ne : nonempty c) → O
  last-but-one [ _ ] ne = ⊥-elim (ne refl)
  last-but-one (c ∷ _) _ = last c

  init : ∀ {e f} (c : chain e f) → (ne : nonempty c) → chain e (last-but-one c ne)
  init [ _ ] ne = ⊥-elim (ne refl)
  init (c ∷ _) _ = c

  infixl 5 _++_ 
  _++_ : ∀ {e f g} → (c₁ : chain e f) → (c₂ : chain f g) → chain e g

  (c₁ ++ [ _ ])  = c₁
  (c₁ ++ (c₂ ∷ e) {p}) = (c₁ ++ c₂ ∷ e) {p}
 
  ++-[] : ∀ {e f} → (c : chain e f) → [ e ] ++ c ≡ c
  ++-[] [ _ ] = refl
  ++-[] ((c ∷ e#f)) rewrite (++-[] c) = refl

  ++-∷ : ∀ {e f h} → (c₁ : chain e f) → (g : O) → .{p : f # g} → (c₂ : chain g h) → (c₁ ++ (([ f ] ∷ g) {p}) ++ c₂ ) ≡ ((c₁ ∷ g) {p} ) ++ c₂
  ++-∷ c₁ _ c₂  = refl

  ++-assoc : ∀ {e f g h} (c₁ : chain e f) (c₂ : chain f g) (c₃ : chain g h) → c₁ ++ (c₂ ++ c₃) ≡ c₁ ++ c₂ ++ c₃ 
  ++-assoc c₁ c₂ [ _ ] rewrite (++-[] c₂) = refl
  ++-assoc c₁ c₂ (c₃ ∷ p) rewrite (++-assoc c₁ c₂ c₃) = refl


  ++-len : ∀ {e f g} → (c₁ : chain e f) → (c₂ : chain f g) → (len c₁) + (len c₂) ≡ len (c₁ ++ c₂)
  ++-len {e} {.g} {g} c₁ [ .g ] rewrite (+-com (len c₁) 0) = refl
  ++-len {e} {f} {g} c₁ (c₂ ∷ .g) rewrite (sym (++-len c₁ c₂)) = sym (+-suc (len c₁) (len c₂))
  
  rev : ∀ {e f} → (c : chain e f) → (chain f e)
  rev [ x ] = [ x ]
  rev ((c ∷ g) {p} ) = ([ _ ] ∷ (last c)) {#-sym p} ++ rev c
 
  rev-++ : ∀ {e f g} → (c₁ : chain e f) → (c₂ : chain f g) → rev (c₁ ++ c₂) ≡ (rev c₂) ++ (rev c₁)
  rev-++ c₁ [ _ ] = sym (++-[] (rev c₁))
  rev-++ c₁ ((c₂ ∷ e) {p}) rewrite rev-++ c₁ c₂ | ++-assoc (([ _ ] ∷ last c₂) {#-sym p}) (rev c₂) (rev c₁) = refl

  rev-id : ∀ {e f} → (c : chain e f) → rev (rev c) ≡ c
  rev-id [ _ ] = refl
  rev-id (c ∷ e#f) with (rev-++ ([ _ ] ∷ (last c)) (rev c))
  ... | p rewrite (rev-id c) = p

  len-rev : ∀ {e f} → (c : chain e f) → (len c) ≡ len (rev c)
  len-rev {.f} {f} [ .f ] = refl
  len-rev {e} {f} (c ∷ .f) rewrite  (len-rev c) = ++-len ([ f ] ∷ last c) (rev c)

  -- Second element of the chain
  second : ∀ {e f} → (c : chain e f) → (ne : nonempty c) → O
  second {e} {f} c p rewrite (len-rev c) = last-but-one (rev c) p

  -- tail of the chain
  tail : ∀ {e f} (c : chain e f) → (ne : nonempty c) → (chain (second c ne) f)
  tail c p rewrite (len-rev c) = rev (init (rev c) p)

  infixl 3 _∈_

  _∈_ : ∀ {e f} → O → chain e f → Set
  x ∈ ([ e ]) = x ≡ e
  x ∈ (c ∷ f) = x ≡ f ⊎ x ∈ c

  -- inj₁ is ≡ last element; inj₂ is ∈ c
  _≺[_]_ : ∀ {e f} → (x : O) → (c : chain e f) → (y : O) → {x∈c : x ∈ c} → {y∈c : y ∈ c} → Set
  x ≺[ [ _ ] ] y = ⊥
  ((_ ≺[ c ∷ _ ] _) {x∈c} {y∈c} ) with (x∈c , y∈c)
  _ ≺[ _ ∷ _ ] _ | inj₁ _ , _ = ⊥ -- x is last element of the chain
  x ≺[ c ∷ _ ] _ | inj₂ _ , inj₁ _ = x ≡ last c
  x ≺[ c ∷ _ ] y | inj₂ x∈c , inj₂ y∈c = (x ≺[ c ] y) {x∈c} {y∈c}
  
  irred : ∀ {e f} → chain e f → Set
  irred [ _ ] = ⊤
  irred (([ e ]) ∷ f) = (e ≡ f) → ⊥
  irred ((c ∷ e) {p} ∷ f) = (.(last c # f) → ⊥) × irred ((c ∷ e) {p})

  irred-∷ : ∀ {e f} → (c : chain e f) → (g : O) → .{f#g : f # g} → irred ((c ∷ g) {f#g}) → f ≡ g → ⊥
  irred-∷ {.f} {f} [ .f ] g ic eq = ic eq
  irred-∷ {e} {f} ((c ∷ .f) {p}) g ic eq = proj₁ ic (subst (_#_ (last c)) eq p)

  irred-++ : ∀ {h} → (e f g : O) → .{e#f : e # f} → .{f#g : f # g} → (irred ((([ e ] ∷ f) {e#f} ∷ g) {f#g})) → 
            (c : chain g h) → irred (([ f ] ∷ g) {f#g} ++ c) → irred (([ e ] ∷ f) {e#f} ++ (([ f ] ∷ g) {f#g} ++ c))
  irred-++ {h} e f .h x [ .h ] x₁ = x
  irred-++ {h} e f .f₁ x (_∷_ {.f₁} {f₁} [ .f₁ ] .h) x₁ = proj₁ x₁ , x
  irred-++ {h} e f g x (_∷_ {.g} {f₁} (c ∷ .f₁) .h) x₁ = proj₁ x₁ , irred-++ e f g x (c ∷ f₁) (proj₂ x₁)

  irred-init : ∀ {e f} → (c : chain e f) → (ne : len c ≢ zero) → irred c → irred (init c ne)
  irred-init [ _ ] ne ic = ⊥-elim (ne refl)
  irred-init (c ∷ e#f) _ ic with c
  irred-init (c ∷ e#f) ne ic | [ _ ] = Data.Unit.tt
  irred-init (c ∷ e#f₁) ne ic | c' ∷ e#f = proj₂ ic  

  irred-rev : ∀ {e f} → (c : chain e f) → irred c → irred (rev c)
  irred-rev {.f} {f} [ .f ] ic = Data.Unit.tt
  irred-rev {.f₁} {f} (_∷_ {.f₁} {f₁} [ .f₁ ] .f) ic = λ t → ic (sym t)
  irred-rev {e} {f} (_∷_ {.e} {f₁} ((c ∷ .f₁) {p}) .f ) ic with irred-rev (c ∷ f₁) (proj₂ ic)
  ... | q = irred-++ f f₁ (last c) ((λ t → proj₁ ic (#-sym t)) , (λ t → proj₁ ic (subst (_#_ (last c)) (sym t) p))) (rev c) q

  shortest : ∀ {e f} → (c : chain e f) → Set
  shortest {e} {f} c = (c' : chain e f) → (len c) ≯ (len c')
                                    
  sh-irred-helper : ∀ {e f} → .(e # f) → ((c' : chain e f) → suc (len c') ≤ 1 → ⊥) → (e ≡ f) → ⊥
  sh-irred-helper {f} f₁ p refl = p [ f ] (s≤s z≤n)

  m≤m : ∀ {m} → m ≤ m
  m≤m {zero} = z≤n
  m≤m {suc m} = s≤s m≤m

  shortest-irred : ∀ {e f} → (c : chain e f) → shortest c → irred c
  shortest-irred [ _ ] s = Data.Unit.tt
  shortest-irred (([ e ] ∷ _) {p}) s = sh-irred-helper p s
  shortest-irred {e} ((c ∷ g ∷ h) {g#h}) s = (λ t → s ((c ∷ h) {t}) (m≤m)) , shortest-irred (c ∷ g) (λ c' z → s ((c' ∷ h) {g#h}) (s≤s z))

  len-init-suc : ∀ {e f} → (c : chain e f) → (ne : nonempty c) → (len c) ≡ suc (len (init c ne))
  len-init-suc {.f} {f} [ .f ] ne = ⊥-elim (ne refl)
  len-init-suc {e} {f} (c ∷ .f) ne = refl
    
  rev-nonempty : ∀ {e f} → (c : chain e f) → nonempty c → nonempty (rev c)
  rev-nonempty c p rewrite (len-rev c) = p

  len-tail-suc : ∀ {e f} → (c : chain e f) → (ne : nonempty c) → (len c) ≡ suc (len (tail c ne))
  len-tail-suc c p rewrite (len-rev c) | sym (len-rev (init (rev c) p )) = len-init-suc (rev c) p

