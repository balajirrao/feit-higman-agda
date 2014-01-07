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

  data chain where
    [_] : (e : O) → chain e e
    _∷_ : ∀ {e f} → (c : chain e f) → (g : O) → .{p : f # g} → chain e g

  head : ∀ {e f} → chain e f → O
  head {e} _ = e

  last : ∀ {e f} → chain e f → O
  last {_} {f} _ = f

  infixr 5 _++_
  _++_ : ∀ {f g} → (e : O) → chain f g → .{p : e # f} → chain e g
  _++_ e [ g ] {p} = ([ e ] ∷ g) {p}
  _++_ e ((c ∷ g) {q}) {p} = (((e ++ c) {p}) ∷ g) {q}

  
  rev : ∀ {e f} → (c : chain e f) → chain f e
  rev [ f ] = [ f ]
  rev ((c ∷ f) {p}) = (f ++ rev c) {#-sym p}

  rev-++ : ∀ {f g} (e : O) → (c : chain f g) → .{p : e # f} → rev ((e ++ c) {p}) ≡ ((rev c) ∷ e) {#-sym p}
  rev-++ {.g} {g} e [ .g ] = refl
  rev-++ {f} {g} e (c ∷ .g) {p}  rewrite (rev-++ e c {p}) = refl
  
  rev-id : ∀ {e f} (c : chain e f) → rev (rev c) ≡ c
  rev-id [ _ ] = refl
  rev-id ((c ∷ f) {p}) rewrite rev-++ f (rev c) {#-sym p} | rev-id c = refl
  
  ++-∷ : ∀ {f g} (e : O) → (c : chain f g) → .{p : e # f} → (e ++ c) {p} ≡ rev(((rev c) ∷ e) {#-sym p})
  ++-∷ {.g} {g} e [ .g ] = refl
  ++-∷ {f} {g} e ((c ∷ .g) {p}) rewrite rev-++ g (rev c) {#-sym p} | rev-id c = refl

  ∷-++ : ∀ {e f} (c : chain e f) (g : O) .{p : f # g} → (c ∷ g) {p} ≡ rev ((g ++ (rev c)) {#-sym p})
  ∷-++ c g {p} rewrite (rev-++ g (rev c) {#-sym p}) | rev-id c = refl
  
  len : ∀ {e f} → (c : chain e f) → ℕ
  len [ _ ] = zero
  len (c ∷ _) = suc (len c)

  nonempty : ∀ {e f} → (c : chain e f) → Set
  nonempty [ _ ] = ⊥
  nonempty (_ ∷ _) = ⊤

  last¹ : ∀ {e f} (c : chain e f) {ne : nonempty c} → O
  last¹ [ _ ] {ne} = ⊥-elim ne
  last¹ (c ∷ _)  = last c

  init : ∀ {e f} (c : chain e f) → {ne : nonempty c} → chain e (last¹ c {ne})
  init [ _ ] {ne} = ⊥-elim ne
  init (c ∷ _) = c

  joinr : ∀ {e f g h} → (c₁ : chain e f) → (c₂ : chain g h) → .{p : f # g} → chain e h
  joinr {e} {f} {.h} {h} c₁ [ .h ] {p} = (c₁ ∷ h) {p}
  joinr {e} {f} {g} {h} c₁ ((c₂ ∷ .h) {p}) {q} = (((joinr c₁ c₂) {q}) ∷ h) {p}
  
  --joinr-++ : ∀ {f g} → (e : O) → (c : chain f g) → .{p : e # f} → joinr [ e ] c {p} ≡ (e ++ c) {p}
  --joinr-++ {.g} {g} e [ .g ] = refl
  --joinr-++ {f} {g} e (c ∷ .g) {p} rewrite sym (joinr-++ e c {p}) = refl

  joinl : ∀ {e f g h} → (c₁ : chain e f) → (c₂ : chain g h) → .{p : f # g} → chain e h
  joinl {.f} {f} [ .f ] c₂ {p} = (f ++ c₂) {p}
  joinl {e} {f} ((c₁ ∷ .f) {p}) c₂ {q} = joinl c₁ ((f ++ c₂) {q}) {p}
 
  joinl-rev : ∀ {e f g h} → (c₁ : chain e f) → (c₂ : chain g h) → .{p : f # g} → rev (joinr (rev c₂) (rev c₁)) ≡ joinr c₁ c₂
  joinl-rev {.f} {f} [ .f ] c₂ = {!!}
  joinl-rev {e} {f} (c₁ ∷ .f) c₂ = {!!}

  joinl-∷ : ∀ {e f} (c : chain e f) (g : O) .{p : f # g} → joinl c [ g ] {p} ≡ (c ∷ g) {p}
  joinl-∷ {.f} {f} [ .f ] g = {!!}
  joinl-∷ {e} {f} ((c ∷ .f) {p}) g {q} = {!!}

  joinl-assoc :  ∀ {e f g h i j} (c₁ : chain e f) (c₂ : chain g h) (c₃ : chain i j)
                   .{p : f # g} .{q : h # i} →
                   joinl (joinl c₁ c₂ {p}) c₃ {q} ≡ joinl c₁ (joinl c₂ c₃ {q}) {p}
  joinl-assoc {.f} {f} {.h} {h} [ .f ] [ .h ] c₃ = {!!}
  joinl-assoc {.f} {f} {g} {h} [ .f ] (c₂ ∷ .h) c₃ = {!!}
  joinl-assoc {e} {f} {.h} {h} (c₁ ∷ .f) [ .h ] c₃ = {!!}
  joinl-assoc {e} {f} {g} {h} (c₁ ∷ .f) (c₂ ∷ .h) c₃ = {!joinl-assoc [ f ] c₂ [ h ]!}

  joinlr : ∀ {e f g h} → (c₁ : chain e f) → (c₂ : chain g h) → .{p : f # g} → joinr c₁ c₂ {p} ≡ rev (joinl (rev c₂) (rev c₁) {#-sym p})
  joinlr {e} {f} {.h} {h} c₁ [ .h ] = {!!}
  joinlr {e} {f} {g} {h} c₁ (c₂ ∷ .h) = {!!}


{- 

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
  
  ∈-head : ∀ {e f} → (c : chain e f) → e ∈ c
  ∈-head {.f} {f} [ .f ] = refl
  ∈-head {e} {f} (c ∷ .f) = inj₂ (∈-head c)

  irred : ∀ {e f} → chain e f → Set
  irred [ _ ] = ⊤
  irred (([ e ]) ∷ f) = (e ≡ f) → ⊥
  irred ((c ∷ e) {p} ∷ f) = (.(last c # f) → ⊥) × irred ((c ∷ e) {p})

  irred-∷ : ∀ {e f} → (c : chain e f) → (g : O) →
              .{f#g : f # g} → irred ((c ∷ g) {f#g}) → f ≡ g → ⊥
  irred-∷ [ _ ] _ ic eq = ic eq
  irred-∷ ((c ∷ .g) {p}) g ic refl = proj₁ ic p

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
  
  next : ∀ {e f} → (x : O) → (c : chain e f) → (ne : nonempty c) → x ∈ (init c ne) → O
  next _ [ _ ] ne _ = ⊥-elim ne
  next x (c ∷ f) ne _ with c
  ... | [ e ] = e
  next _ (_ ∷ f) _ (inj₁ _) | _ ∷ _ = f
  next x (_ ∷ _) _ (inj₂ x∈c') | ((c' ∷ g) {p}) = next x ((c' ∷ g) {p}) tt x∈c'


{-
  ∈-++ : ∀ {e f g} → (x : O) → (c₁ : chain e f) → (c₂ : chain f g) → x ∈ c₁ ⊎ x ∈ c₂ → x ∈ (c₁ ++ c₂)
  ∈-++ {.f} {f} .f [ .f ] c₂ (inj₁ refl) = ∈-head ([ f ] ++ c₂)
  ∈-++ {e} {f} .f (c₁ ∷ .f) c₂ (inj₁ (inj₁ refl)) = {!!}
  ∈-++ {e} {f} x (c₁ ∷ .f) c₂ (inj₁ (inj₂ y)) = {!!}
  ∈-++ x c₁ c₂ (inj₂ y) = {!!}
-}
  ∈-rev : ∀ {e f} (x : O) (c : chain e f) → (x ∈ c) → x ∈ (rev c)
  ∈-rev _ [ _ ] x∈c = x∈c
  ∈-rev .f₁ (c ∷ f₁) (inj₁ refl) = ∈-head ([ f₁ ] ∷ (last c) ++ rev c)
  ∈-rev x (_∷_ {.f} {f} [ .f ] f₁) (inj₂ x∈c) = {!!}
  ∈-rev x (_∷_ {e} {f} (c ∷ .f) f₂) (inj₂ x∈c) = {!!}

{-  
  ∈-rev-inv : ∀ {e f} (x : O) (c : chain e f) → x ∈ (rev c) → (x ∈ c)
  ∈-rev-inv x c p with ∈-rev x (rev c) p
  ... | q rewrite (rev-id c) = q

  prev : ∀ {e f} → (x : O) → (c : chain e f) → (ne : nonempty c) → x ∈ (tail c ne) → O
  prev x c ne p rewrite (len-rev c) =
       next x (rev c) (rev-nonempty c ne)
           (∈-rev-inv x (init (rev c) (rev-nonempty c ne)) p)

  dropr : ∀ {e f} → (x : O) →  (c : chain e f) → x ∈ c → chain e x
  dropr {.f} {f} .f [ .f ] refl = [ f ]
  dropr {e} {f} .f ((c ∷ .f) {p}) (inj₁ refl) = (c ∷ f) {p}
  dropr {e} {f} x (c ∷ .f) (inj₂ y) = dropr x c y

  dropl : ∀ {e f} → (x : O) →  (c : chain e f) → x ∈ c → chain x f
  dropl x c p = rev (dropr x (rev c) (∈-rev x c p))

  drop-split : ∀ {e f} (x : O) →  (c : chain e f) → (p : x ∈ c) → ((dropr x c p) ++ (dropl x c p)) ≡ c
  drop-split {.f} {f} x [ .f ] p = {!!}
  drop-split {e} {f} .f (c ∷ .f) (inj₁ refl) = {!!}
  drop-split {e} {f} x (c ∷ .f) (inj₂ y) = {!!}

-}
-}
