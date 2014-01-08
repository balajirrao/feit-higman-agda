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
 
  data chain : O → O → Set where
    [_] : (e : O) → chain e e
    _∷_ :{e f : O} → (c : chain e f) → (g : O) → .{p : f # g} → chain e g

  data lchain : O → O → Set where
    [_] : (e : O) → lchain e e
    _++_ : {f g : O} → (e : O) (c : lchain f g) .{p : e # f} → lchain e g

  last : ∀ {e f} → chain e f → O
  head : ∀ {e f} → chain e f → O
  last {_} {f} _ = f
  head {e}     _ = e

  headl : ∀ {e f} → lchain e f → O
  headl {e} _ = e

  rev : ∀ {e f} (c : chain e f) → lchain f e
  rev {.f} {f} [ .f ] = [ f ]
  rev {e} {f} ((c ∷ .f) {p}) = (f ++ rev c) {#-sym p}

  revl : ∀ {e f} (c : lchain e f) → chain f e
  revl {.f} {f} [ .f ] = [ f ]
  revl {e} ((.e ++ c) {p}) = (revl c ∷ e) {#-sym p}
  
  rev-id : ∀ {e f} (c : chain e f) → revl (rev c) ≡ c
  rev-id {.f} {f} [ .f ] = refl
  rev-id {e} {f} (c ∷ .f) rewrite (rev-id c) = refl

  revl-id : ∀ {e f} (c : lchain e f) → rev (revl c) ≡ c
  revl-id {.f} {f} [ .f ] = refl
  revl-id {e} (.e ++ c) rewrite (revl-id c) = refl

  rtol' : ∀ {e f h} → chain e h → lchain h f → lchain e f
  rtol' {.h} {f} {h} [ .h ] acc = acc
  rtol' {e} {f} {h} ((c ∷ .h) {p}) acc = rtol' c (((last c) ++ acc) {p})
  
  rtol : ∀ {e f} → chain e f → lchain e f
  rtol c = rtol' c [ _ ]

  ltor' : ∀ {e f h} → lchain h f → chain e h → chain e f
  ltor' {e} {f} [ .f ] acc = acc
  ltor' {e} {f} {h} ((.h ++ c) {p}) acc = ltor' c ((acc ∷ headl c) {p})
                                                                   
  ltor : ∀ {e f} → lchain e f → chain e f
  ltor c = ltor' c [ _ ]
  
{-
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
  _++_ : ∀ {e f g h} (c₁ : chain e f) (c₂ : chain g h) .{p : f # g} → chain e h
  (c₁ ++ [ e ]) {p} = (c₁ ∷ e) {p}
  (c₁ ++ (c₂ ∷ e) {p}) {q} = ((c₁ ++ c₂) {q} ∷ e) {p}
 
  ++-nonempty : ∀ {e f g h} (c₁ : chain e f) (c₂ : chain g h) .{p : f # g} →
                (nonempty c₁) → nonempty ((c₁ ++ c₂) {p})
  ++-nonempty _ [ _ ] _ = tt
  ++-nonempty _ (_ ∷ _) _ = tt

  ++-assoc : ∀ {e f g h i j} (c₁ : chain e f) (c₂ : chain g h) (c₃ : chain i j) →
               .{p : f # g} .{q : h # i} →
               (c₁ ++ ((c₂ ++ c₃) {q})) {p} ≡ (((c₁ ++ c₂) {p}) ++ c₃) {q}
  ++-assoc _ _ [ _ ] = refl
  ++-assoc c₁ c₂ (c₃ ∷ _) {p} {q} rewrite sym (++-assoc c₁ c₂ c₃ {p} {q}) = refl
  
  ++-len : ∀ {e f g h} (c₁ : chain e f) (c₂ : chain g h) .{p : f # g} →
             suc ((len c₁) + (len c₂)) ≡ len ((c₁ ++ c₂) {p})
  ++-len {e} {f} {.h} {h} c₁ [ .h ] rewrite sym(+-com 0 (len c₁)) = refl
  ++-len {e} {f} {g} {h} c₁ (c₂ ∷ .h) {p} rewrite sym (+-suc (len c₁) (len c₂)) | ++-len c₁ c₂ {p} = refl

  rev : ∀ {e f} → (c : chain e f) → (chain f e)
  rev [ x ] = [ x ]
  rev ((c ∷ g) {p} ) = ([ g ] ++ rev c) {#-sym p}
 
  rev-++ : ∀ {e f g h} (c₁ : chain e f) (c₂ : chain g h) .{p : f # g} →
             rev ((c₁ ++ c₂) {p}) ≡ ((rev c₂) ++ (rev c₁)) {#-sym p}
  rev-++ {e} {f} {.h} {h} c₁ [ .h ] = refl
  rev-++ {e} {f} {g} {h} c₁ ((c₂ ∷ .h) {q}) {p}
             rewrite rev-++ c₁ c₂ {p}
             | ++-assoc [ h ]  (rev c₂) (rev c₁) {#-sym q} {#-sym p} = refl

  rev-id : ∀ {e f} → (c : chain e f) → rev (rev c) ≡ c
  rev-id [ _ ] = refl
  rev-id ((c ∷ f) {p}) rewrite rev-++ [ f ] (rev c) {#-sym p}
                             | rev-id c = refl

  len-rev : ∀ {e f} → (c : chain e f) → (len c) ≡ len (rev c)
  len-rev [ _ ] = refl
  len-rev ((c ∷ f) {p}) rewrite
              sym(++-len [ f ] (rev c) {#-sym p}) | len-rev c = refl


  rev-nonempty : ∀ {e f} → (c : chain e f) → nonempty c → nonempty (rev c)
  rev-nonempty [ _ ] p = p
  rev-nonempty (_∷_ {.f} {f} [ .f ] f₁) p₁ = tt
  rev-nonempty (_∷_ {e} {f} ((c ∷ .f) {p}) g {q}) p₂
               rewrite ++-assoc [ g ] [ f ] (rev c) {#-sym q} {#-sym p} =
                       ++-nonempty ([ g ] ++ [ f ]) (rev c) {#-sym p} tt

  -- Second element of the chain
  second : ∀ {e f} → (c : chain e f) → (ne : nonempty c) → O
  second c p rewrite (len-rev c) = last-but-one (rev c) (rev-nonempty c p)

  -- tail of the chain
  tail : ∀ {e f} (c : chain e f) → (ne : nonempty c) → (chain (second c ne) f)
  tail c p rewrite (len-rev c) = rev (init (rev c) (rev-nonempty c p))

  irred : ∀ {e f} → chain e f → Set
  irred [ _ ] = ⊤
  irred (([ e ]) ∷ f) = (e ≡ f) → ⊥
  irred ((c ∷ e) {p} ∷ f) = (.(last c # f) → ⊥) × irred ((c ∷ e) {p})

  irred-∷ : ∀ {e f} → (c : chain e f) → (g : O) →
              .{f#g : f # g} → irred ((c ∷ g) {f#g}) → f ≡ g → ⊥
  irred-∷ [ _ ] _ ic eq = ic eq
  irred-∷ ((c ∷ f) {p}) g ic eq = proj₁ ic (subst (_#_ (last c)) eq p)

  irred-++ : ∀ {h} → (e f g : O) → .{p : e # f} → .{q : f # g} →
               (irred ((([ e ] ∷ f) {p} ∷ g) {q})) → (c : chain g h) →
               irred (([ f ] ++ c) {q} ) →
               irred (([ e ] ++ (([ f ] ++ c) {q})) {p})
  irred-++ {h} e f .h x [ .h ] x₁ = x
  irred-++ {h} _ _ _ x ([ ._ ] ∷ ._) x₁ = proj₁ x₁ , proj₁ x , proj₂ x
  irred-++ {h} e f g x (c ∷ k ∷ .h ) x₁ =
               proj₁ x₁ , irred-++ e f g x (c ∷ k) (proj₂ x₁)

  irred-init : ∀ {e f} → (c : chain e f) → (ne : nonempty c) → irred c → irred (init c ne)
  irred-init [ _ ] ne ic = ⊥-elim ne
  irred-init (c ∷ _) _ ic with c
  ... | [ _ ] = tt
  ... | _ ∷ _ = proj₂ ic  

  irred-rev : ∀ {e f} → (c : chain e f) → irred c → irred (rev c)
  irred-rev [ _ ] _ = tt
  irred-rev ([ _ ] ∷ _) ic = λ t → ic (sym t)
  irred-rev ((((c ∷ e) {p}) ∷ f) {r})  ic with irred-rev (c ∷ e) (proj₂ ic)
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
  
  infixl 3 _∈_
  _∈_ : ∀ {e f} → O → chain e f → Set
  x ∈ ([ e ]) = x ≡ e
  x ∈ (c ∷ f) = x ≡ f ⊎ x ∈ c
  
  ∈-head : ∀ {e f} (c : chain e f) → e ∈ c
  ∈-head {.f} {f} [ .f ] = refl
  ∈-head {e} {f} (c ∷ .f) = inj₂ (∈-head c)

  next : ∀ {e f} → (x : O) → (c : chain e f) → (ne : nonempty c) →
         x ∈ (init c ne) → O
  next _ [ _ ] ne _ = ⊥-elim ne
  next x (c ∷ f) ne _ with c
  ... | [ e ] = e
  next _ (_ ∷ f) _ (inj₁ _) | _ ∷ _ = f
  next x (_ ∷ _) _ (inj₂ x∈c') | ((c' ∷ g) {p}) = next x ((c' ∷ g) {p}) tt x∈c'

  ∈-++ : ∀ {e f g h} (x : O) (c₁ : chain e f) (c₂ : chain g h) .{p : f # g} →
         x ∈ c₁ ⊎ x ∈ c₂ → x ∈ ((c₁ ++ c₂) {p})
  ∈-++ _ _ [ _ ] (inj₁ x₁) = inj₂ x₁
  ∈-++ _ _ [ _ ] (inj₂ y) = inj₁ y
  ∈-++ x c₁ (c₂ ∷ _) (inj₁ x₁) = inj₂ (∈-++ x c₁ c₂ (inj₁ x₁))
  ∈-++ x c₁ (c₂ ∷ h) (inj₂ (inj₁ x₁)) = inj₁ x₁
  ∈-++ x c₁ (c₂ ∷ h) (inj₂ (inj₂ y)) = inj₂ (∈-++ x c₁ c₂ (inj₂ y))
  
  ∈-rev : ∀ {e f} (x : O) (c : chain e f) → (x ∈ c) → x ∈ (rev c)
  ∈-rev _ [ _ ] x∈c = x∈c
  ∈-rev .f (c ∷ f) (inj₁ refl) = ∈-++ f [ f ] (rev c) (inj₁ refl)
  ∈-rev x (c ∷ f) (inj₂ x∈c) = ∈-++ x ([ f ]) (rev c) (inj₂ (∈-rev x c x∈c))
  
  ∈-rev-inv : ∀ {e f} (x : O) (c : chain e f) → x ∈ (rev c) → (x ∈ c)
  ∈-rev-inv x c p with ∈-rev x (rev c) p
  ... | q rewrite (rev-id c) = q

  prev : ∀ {e f} → (x : O) → (c : chain e f) →
                   (ne : nonempty c) → x ∈ (tail c ne) → O
  prev x c ne p rewrite (len-rev c) =
       next x (rev c) (rev-nonempty c ne)
           (∈-rev-inv x (init (rev c) (rev-nonempty c ne)) p)

  -- Extend c₁ by c₂. Like c₁, but in the case c₁ ends where c₂ begins,
  -- unlike ++ this function does not make a chain with redundant entry
  -- for (last c₁) (≡ last c₂)
  extend : ∀ {e f g} (c₁ : chain e f) (c₂ : chain f g) → chain e g
  extend [ _ ] c₂ = c₂
  extend ((c₁ ∷ _) {p}) c₂ = (c₁ ++ c₂) {p}
  
  -- this theorem, though holds for ++, does not hold automatically
  -- for extend, because of the existence of cases in extend
  extend-∷ : ∀ {e f g} (c₁ : chain e f) (c₂ : chain f g) (h : O) .{p : g # h} →
             extend c₁ ((c₂ ∷ h) {p}) ≡ ((extend c₁ c₂) ∷ h) {p}
  extend-∷ [ _ ] _ _ = refl
  extend-∷ (_ ∷ _) _ _ = refl

  -- drop the elements to the right hand side of x
  dropr : ∀ {e f} → (x : O) →  (c : chain e f) → x ∈ c → chain e x
  dropr f [ .f ] refl = [ f ]
  dropr f ((c ∷ .f) {p}) (inj₁ refl) = (c ∷ f) {p}
  dropr x (c ∷ _) (inj₂ x∈c) = dropr x c x∈c
  
  -- drop the elements to the left hand side of x
  dropl : ∀ {e f} → (x : O) →  (c : chain e f) → x ∈ c → chain x f
  dropl x c p = rev (dropr x (rev c) (∈-rev x c p))

  dropr-tail : ∀ {f g} (e : O) (c : chain f g) .{p : e # f} →
             dropr e (([ e ] ++ c) {p}) (∈-++ e [ e ] c (inj₁ refl)) ≡ [ e ]
  dropr-tail e [ g ] = refl
  dropr-tail e (c ∷ _) = dropr-tail e c

  dropr-body : ∀ {e f g} (x : O) (c : chain f g) .{p : e # f} (x∈c : x ∈ c) →
             dropr x (([ e ] ++ c) {p})
               (∈-++ x [ e ] c (inj₂ x∈c)) ≡ ([ e ] ++ dropr x c x∈c) {p}
  dropr-body _ [ ._ ] refl = refl
  dropr-body _ (_ ∷ ._) (inj₁ refl) = refl
  dropr-body x (c ∷ _) (inj₂ x∈c) = dropr-body x c x∈c
  
  dropl-body : ∀ {e f g} (c : chain e f) (x : O) (x∈c : x ∈ c) .{p : f # g} →
             dropl x ((c ∷ g) {p}) (inj₂ x∈c) ≡ ((dropl x c x∈c) ∷ g) {p}
  dropl-body {g = g} c x x∈c {p} rewrite
                         dropr-body {e = g} x (rev c) {#-sym p} (∈-rev x c x∈c) 
                     with (dropr x (rev c) (∈-rev x c x∈c))
  ... | c' rewrite rev-++ [ g ] c' {#-sym p} = refl
                       
  drop-split : ∀ {e f} (x : O) →  (c : chain e f) → (p : x ∈ c) →
                 extend (dropr x c p) (dropl x c p) ≡ c
  drop-split _ [ ._ ] refl = refl
  drop-split f ((c ∷ .f) {p}) (inj₁ refl)
               rewrite dropr-tail f (rev c) {#-sym p} = refl
  drop-split x ((c ∷ f) {p}) (inj₂ x∈c)
               rewrite dropl-body c x x∈c {p} |
                       extend-∷ (dropr x c x∈c) (dropl x c x∈c) f {p} |
                       drop-split x c x∈c = refl
                                                 

  nth : ∀ {e f n} (c : chain e f) → (p : n ≤ len c) → O
  nth [ f ] z≤n = f
  nth {e} (_ ∷ _) z≤n = e
  nth (c ∷ _) (s≤s p) = nth c p

  nth-∈ : ∀ {e f n} (c : chain e f) → (p : (n ≤ len c)) → (nth c p) ∈ c
  nth-∈ {.f} {f} [ .f ] z≤n = refl
  nth-∈ {e} {f} (c ∷ .f) z≤n = inj₂ (∈-head c)
  nth-∈ {e} {f} (c ∷ .f) (s≤s p₁) = inj₂ (nth-∈ c p₁)

-}
