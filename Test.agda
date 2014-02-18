open import Data.Nat
open import Relation.Binary.PropositionalEquality

open import Data.Unit.Core

module Test where
  postulate _n : Hidden ℕ

  n : ℕ
  n = 0

  postulate
    nz : n ≡ 0

  f : suc n ≡ m + 1
  f = {!!}
  
