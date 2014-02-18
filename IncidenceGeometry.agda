module IncidenceGeometry where
  open import Data.Nat
  open import Data.Nat.Properties
  open import Data.Unit using (⊤; tt)
  open import Data.Empty
  open import Data.Product
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; _≢_; subst; subst₂; sym; trans)
  open import Relation.Binary
  open import Data.Maybe
  open import Data.Sum
  --open import Data.Bool
  open import Relation.Binary
  open import Relation.Nullary.Core
  open import Misc

  open import Function

  open Data.Nat.≤-Reasoning

  import Level

  postulate
    P L : Set

  data O : Set where
    pt : P → O
    ln : L → O

  postulate
    _#_ : Rel O Level.zero
    #sym : ∀ {e f} → e # f → f # e
    #refl : ∀ {e} → e # e    
  
  infixr 5 _∷_   
  data chain : O → O → Set where
    [_] : (e : O) → chain e e
    _∷_ : ∀ {f g} (e : O) .{{e<>f : e ≡ f → ⊥}} .{{e#f : e # f}} (c : chain f g) → chain e g    

  len : ∀ {e f} (c : chain e f) → ℕ
  len [ _ ] = zero
  len (_ ∷ c) = suc (len c)

  data _∈_ : ∀ {e f} (x : O) (c : chain e f) → Set where
    ∈z : ∀ {e f} (c : chain e f) → e ∈ c
    ∈s : ∀ {e f x} (y : O) .{{y<>e : y ≡ e → ⊥}} (c : chain e f) .{{q : y # e}} (p : x ∈ c) → x ∈ (y ∷ c)

  nth : ∀ {e f n} (c : chain e f) (p : n ≤ (len c))  → O
  nth [ e ] z≤n = e
  nth (e ∷ _) z≤n = e
  nth (e#f ∷ c) (s≤s p) = nth c p
                                                                       
  data irred : ∀ {e f} (c : chain e f) → Set where
    iz : ∀ (e f g : O) .{{e<>f : e ≡ f → ⊥}} .{{f<>g : f ≡ g → ⊥}}
           .{{e#f : e # f}} .{{f#g : f # g}} (¬e#g : .(e # g) → ⊥) → irred (e ∷ f ∷ [ g ])
    is : ∀ {f g} (e : O) .{{e#f : e # f}} .{{e<>f : e ≡ f → ⊥}}
           (c : chain f g) (p : (len c) ≥ 1) (ic : irred c)
           (¬e#c : .(e # (nth c p)) → ⊥) → irred (e ∷ c) 

  nth-∈ : ∀ {e f n} (c : chain e f) (p : n ≤ (len c)) → (nth c p) ∈ c
  nth-∈ [ e ] z≤n = ∈z [ e ]
  nth-∈ (e ∷ c) z≤n = ∈z (e ∷ c)
  nth-∈ (e ∷ c) (s≤s p) = ∈s e c (nth-∈ c p)


  head : ∀ {e f} (c : chain e f) → O
  head {e} c = nth c z≤n

  last : ∀ {e f} (c : chain e f) → O
  last c = nth c m≤m

  tail : ∀ {e f} (c : chain e f) (p : (len c) ≥ 1) → chain (nth c p) f
  tail [ _ ] ()
  tail (e ∷ c) (s≤s p) with c
  tail {.e} {f} (e ∷ c) (s≤s z≤n) | [ .f ] = [ f ]
  tail (e ∷ c) (s≤s z≤n) | (g ∷ c') = c

  init : ∀ {e f} (c : chain e f) (p : (len c) ≥ 1) → chain e (nth {n = pred (len c)} c n≤pred)
  init [ _ ] ()
  init (e ∷ [ _ ]) (s≤s z≤n) = [ e ] 
  init (e#f ∷ e#f₁ ∷ c) (s≤s z≤n) = e#f ∷ init (e#f₁ ∷ c) (s≤s z≤n)

  infixl 5 _++_
  _++_ : ∀ {e f} (c : chain e f) (g : O) .{{f<>g : f ≡ g → ⊥}} .{{p : f # g}} → chain e g
  [ e ] ++ f = e ∷ [ f ] 
  (e#f ∷ c) ++ p = e#f ∷ (c ++ p)

  rev : ∀ {e f} (c : chain e f) → chain f e
  rev {.f} {f} [ .f ] = [ f ]
  rev {e} (_∷_ .e {{e<>f}} {{e#f}} c) = (rev c ++ e) {{λ x → e<>f (sym x)}} {{#sym e#f}}
    
  len-++ : ∀ {e f} → (c : chain e f) (g : O) .{{f<>g : f ≡ g → ⊥}} .{{p : f # g}} → suc (len c) ≡ len (c ++ g)
  len-++ {.f} {f} [ .f ] g = refl
  len-++ {e} (_∷_ .e {{e<>f}} {{e#f}} c) g = cong suc (len-++ c g)

  len-rev : ∀ {e f} {c : chain e f} → len c ≡ len (rev c)
  len-rev {.f} {f} {[ .f ]} = refl
  len-rev {e} {f} {_∷_ .e {{e<>f}} {{e#f}} c} = trans (cong suc len-rev) (len-++ (rev c) e {{λ x → e<>f (sym x)}} {{#sym e#f}})
  
  rev-++ : ∀ {e f g} {c : chain e f} .{f#g : f # g} .{f<>g : f ≢ g} → rev (c ++ g) ≡ _∷_ g {{e<>f = λ x → f<>g (sym x)}} {{e#f = #sym f#g}} (rev c) 
  rev-++ {.f} {f} {g} {[ .f ]} = refl
  rev-++ {e} {f} {g} {_∷_ {e₁} .e {{e<>e₁}} {{e#e₁}} c} {f#g} {f<>g} rewrite rev-++ {e₁} {f} {g} {c} {f#g} {f<>g} = refl                                                   

  rev²-id : ∀ {e f} {c : chain e f} → rev (rev c) ≡ c
  rev²-id {.f} {f} {[ .f ]} = refl
  rev²-id {e} {f} {_∷_ {e₁} .e {{e<>f}} {{e#f}} c} = trans (rev-++ {f} {e₁} {e} {rev c} {#sym e#f} {λ z → e<>f (sym z)}) (cong (_∷_ e) rev²-id)
 
  -- Shortest chain --

  module ShortestPredicate where
    postulate
      lambda : (e f : O) → ℕ
      lambda-sym : ∀ {e f} → (lambda e f) ≡ (lambda f e)
      sc : (e f : O) → (chain e f)
      sc-len-lambda : ∀ {e f} → (len (sc e f)) ≡ (lambda e f)
      lambda-shortest : ∀ {e f} (c : chain e f) → (lambda e f) ≯ (len c)
    
    shortest : ∀ {e f} → (c : chain e f) → Set
    shortest {e} {f} c = (len c) ≡ lambda e f

    -- Couple of obvious functions to deal with buggy pattern matching lambdas
    
    private F : ∀ {e f g} → (e ≡ f) → (c : chain f g) → chain e g
            F {e} refl c = c

    private G : ∀ {e f g} → (p : e ≡ f) (c : chain f g) → len (F p c) ≤ suc (len c)
            G refl c = n≤suc

    tail-shortest : ∀ {e f g} .{{e#f : e # f}} .{{e<>f : e ≡ f → ⊥}}
                      {c : chain f g} → shortest (e ∷ c) → shortest c
    tail-shortest {e} {f} {g} {c = c} s with len c ≤? lambda f g
    tail-shortest {e} {f} {g} {c = c} s | yes p with len c ≟ lambda f g
    tail-shortest s | yes p₁ | yes p = p
    tail-shortest {_} {f} {g} {c = c} s | yes p≤ | no ¬p≡ = ⊥-elim (lambda-shortest c
                                                                   (≤≢⇒< (
                                                                     begin
                                                                       len c
                                                                         ≤⟨ p≤ ⟩
                                                                       --len (sc f g)
                                                                         --≡⟨ sc-len-lambda ⟩
                                                                       (lambda f g ∎))
                                                                   ( ¬p≡ )))
    tail-shortest {e} {f} {g} {c = c} s | no ¬p =  ⊥-elim (lambda-shortest (e ∷ sc f g)
                                                 (begin
                                                   suc (suc (len (sc f g)))
                                                     ≡⟨ cong suc (cong suc sc-len-lambda) ⟩
                                                   suc (suc (lambda f g))
                                                     ≤⟨ s≤s (≰⇒> ¬p) ⟩
                                                   suc (len c)
                                                     ≡⟨ s ⟩
                                                   --len (sc e g)
                                                    --≡⟨ sc-len-lambda ⟩
                                                   lambda e g
                                                 ∎))
   
    shortest-irred : ∀ {e f} (c : chain e f) (p : (len c) ≥ 2) → shortest c → irred c
    shortest-irred {.f} {f} [ .f ] () sc
    shortest-irred (_ ∷ [ _ ]) (s≤s ()) sc
    shortest-irred (e ∷ f ∷ [ g ] ) (s≤s (s≤s z≤n)) sc = iz e f g
                                    (λ e#g → lambda-shortest (_∷_ e
                                      {{e<>f = λ e≡f →
                                        lambda-shortest (F e≡f [ g ])
                                          (≤≡ sc (s≤s (G e≡f [ g ])))}}
                                      {{e#f = e#g}}
                                      [ g ]) (≡⇒≤ sc))
    shortest-irred {.e} {h} (e ∷ f ∷ g ∷ c) (s≤s (s≤s z≤n)) s = is e (f ∷ g ∷ c) (s≤s z≤n)
                                                           (shortest-irred (f ∷ g ∷ c) (s≤s (s≤s z≤n))
                                                             (tail-shortest {e} {f} {h} {f ∷ g ∷ c} s))
                                                           (λ e#g → lambda-shortest (_∷_ e
                                                             {{e<>f = λ e≡g → lambda-shortest (F e≡g (g ∷ c))
                                                               (begin
                                                                 suc (len (F e≡g (g ∷ c)))
                                                                   ≤⟨ s≤s (G e≡g (g ∷ c)) ⟩
                                                                suc (suc (suc (len c)))
                                                                   ≡⟨ s ⟩
                                                                 lambda e h ∎
                                                             ) }}

                                                             {{e#f = e#g}} (g ∷ c)) (≡⇒≤ s))
                                                           
   
  open ShortestPredicate public

  
  -- upper bound for λ (e₁, f) in terms of λ (e, f) when e # e₁
  lambda-ub : ∀ {e e₁ f} .{e<>e₁ : e ≢ e₁} .{e#e₁ : e # e₁} → lambda e₁ f > suc (lambda e f) → ⊥
  lambda-ub {e} {e₁} {f} {e<>e₁} {e#e₁} p = lambda-shortest
                                       (_∷_ e₁ {{e<>f = λ eq → e<>e₁ (sym eq)}}
                                            {{e#f = #sym e#e₁}} (sc e f))
                                              (begin
                                                suc (suc (len (sc e f)))
                                                  ≡⟨ cong suc (cong suc sc-len-lambda) ⟩
                                                suc (suc (lambda e f))
                                                  ≤⟨ p ⟩
                                                lambda e₁ f ∎)

  -- lower bound for λ (e₁, f) in terms of λ (e, f) when e # e₁
  lambda-lb : ∀ {e e₁ f} .{e<>e₁ : e ≢ e₁} .{e#e₁ : e # e₁} (l>1 : lambda e f ≥ 1) →
                                                          lambda e₁ f < pred (lambda e f) → ⊥
  lambda-lb {e} {e₁} {f} {e<>e₁} {e#e₁} l>1 p = lambda-shortest (e ∷ sc e₁ f)
                                       (begin
                                         suc (suc (len (sc e₁ f)))
                                           ≡⟨ cong suc (cong suc sc-len-lambda) ⟩
                                         suc (suc (lambda e₁ f))
                                           ≤⟨ s≤s p ⟩
                                         suc (pred (lambda e f))
                                           ≡⟨ suc∘pred≡id l>1 ⟩
                                         lambda e f ∎)

{-

  mid : ∀ {e f n} (c : chain e f n) (p : Even n) → O
  mid c p = nth c (div2≤ p)

  take-left : ∀ {e f n m} (c : chain e f n) (p : m ≤ n) → chain e (nth c p) m
  take-left c z≤n = nil
  take-left (e#f ∷ c) (s≤s p) = e#f ∷ take-left c p

  take-right : ∀ {e f n m} (c : chain e f n) (p : m ≤ n) → chain (nth c p) f (n ∸ m) 
  take-right nil z≤n = nil
  take-right (e#f ∷ c) z≤n = e#f ∷ c
  take-right (e#f ∷ c) (s≤s p) = take-right c p

 
-}


