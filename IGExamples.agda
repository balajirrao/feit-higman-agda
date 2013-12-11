module IGExamples where
  open import Data.Nat
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
  open import Data.Product
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  postulate
    O : Set
    _#_ : O → O → Set
    e f g : O
    e#f : e # f
    f#g : f # g
    not-e#g : e # g → ⊥

  open import IncidenceGeometry O  _#_

      -- Construct 2 chains from e to g. One directly, and the other through f
      
  c₁ : chain e g
  c₁ = chain-ext (chain-inc e#f) f#g
    
    --c₂ : chain e g
    --c₂ = chain-inc e#g
  
  c₁-len : len c₁ ≡ 2
  c₁-len = refl

  c1-not-irred : irred c₁
  c1-not-irred p = not-e#g p
  
    --c2-irred : irred c₂
    --c2-irred = tt

