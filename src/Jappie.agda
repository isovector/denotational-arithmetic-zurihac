module Jappie where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_)

-- A set to far
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩
inc (next O) = next I
inc (⟨⟩ I)   = ⟨⟩ I O
inc (next I) = (inc next) O

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc rem) = inc (to rem)

from : Bin → ℕ
from (x I) = suc (from x)
from (x O) = (from x)
from ⟨⟩ = 0

pwoof :  ∀ {n : ℕ} → from (to n) ≡ n
pwoof 0 =  refl

_ : to 0 ≡  ⟨⟩ O
_ = refl
