open import Function.Bijection
open import Function.Equality
open import Function.LeftInverse
open import Data.Fin
open import Relation.Binary.PropositionalEquality as PropEq

open import Data.Unit

module BijectionPractice where
  postulate
    A : Set
    F : Bijection (PropEq.setoid A) (PropEq.setoid (⊤))

  open Bijection F public 
  
  H : (x : A) → ⊤
  H x = to ⟨$⟩ x --Bijection.to F ⟨$⟩ x

  K : ⊤ → A
  K tt = LeftInverse.from (Bijection.left-inverse F) ⟨$⟩ tt

  L : (x : A) → x ≡ K tt
  L x = injective refl
