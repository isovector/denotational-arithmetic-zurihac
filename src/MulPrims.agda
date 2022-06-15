module MulPrims where

open import Mul
open import Function.Base
open import Data.Bool.Base hiding (_<_; _≤_)
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Vec hiding (map)
import Data.Vec as V
open import Data.Product as P hiding (map)
open import Data.Fin.Base as F hiding (_+_; _<_; _≤_)
open import Data.Fin.Properties hiding (bounded)
open import Relation.Binary.PropositionalEquality

open Adder
open Multiplier

--------------------------------------------------------------------------------

interpret2 : Bool → Fin 2
interpret2 false = zero
interpret2 true  = suc zero

add2 : Adder interpret2
add add2 (zero , false , false)     = false , zero
add add2 (zero , false , true)      = true  , zero
add add2 (zero , true , false)      = true  , zero
add add2 (zero , true , true)       = false , suc zero
add add2 (suc zero , false , false) = true  , zero
add add2 (suc zero , false , true)  = false , suc zero
add add2 (suc zero , true , false)  = false , suc zero
add add2 (suc zero , true , true)   = true  , suc zero
zeroA add2 = false
proof-add add2 (zero , false , false) = refl
proof-add add2 (zero , false , true)  = refl
proof-add add2 (zero , true  , false) = refl
proof-add add2 (zero , true  , true)  = refl
proof-add add2 (suc zero , false , false) = refl
proof-add add2 (suc zero , false , true)  = refl
proof-add add2 (suc zero , true  , false) = refl
proof-add add2 (suc zero , true  , true)  = refl

mul2 : Multiplier interpret2
mult mul2 false false = false , false
mult mul2 false true  = false , false
mult mul2 true  false = false , false
mult mul2 true  true  = false , true
zeroM mul2 = false
proof-mult mul2 false false = refl
proof-mult mul2 false true  = refl
proof-mult mul2 true  false = refl
proof-mult mul2 true  true  = refl

--------------------------------------------------------------------------------

data Three : Set where
  zero : Three
  one : Three
  two : Three

interpret3 : Three → Fin 3
interpret3 zero = zero
interpret3 one = suc zero
interpret3 two = suc (suc zero)

add3 : Adder interpret3
add add3 (zero , zero , zero)     = zero , zero
add add3 (zero , zero , one)      = one  , zero
add add3 (zero , zero , two)      = two  , zero
add add3 (zero , one , zero)      = one  , zero
add add3 (zero , one , one)       = two  , zero
add add3 (zero , one , two)       = zero , suc zero
add add3 (zero , two , zero)      = two  , zero
add add3 (zero , two , one)       = zero , suc zero
add add3 (zero , two , two)       = one  , suc zero
add add3 (suc zero , zero , zero) = one  , zero
add add3 (suc zero , one , zero)  = two  , zero
add add3 (suc zero , two , zero)  = zero , suc zero
add add3 (suc zero , zero , one)  = two  , zero
add add3 (suc zero , one , one)   = zero , suc zero
add add3 (suc zero , two , one)   = one  , suc zero
add add3 (suc zero , zero , two)  = zero , suc zero
add add3 (suc zero , one , two)   = one  , suc zero
add add3 (suc zero , two , two)   = two  , suc zero
zeroA add3 = zero
proof-add add3 (zero , zero , zero)     = refl
proof-add add3 (zero , zero , one)      = refl
proof-add add3 (zero , zero , two)      = refl
proof-add add3 (zero , one , zero)      = refl
proof-add add3 (zero , one , one)       = refl
proof-add add3 (zero , one , two)       = refl
proof-add add3 (zero , two , zero)      = refl
proof-add add3 (zero , two , one)       = refl
proof-add add3 (zero , two , two)       = refl
proof-add add3 (suc zero , zero , zero) = refl
proof-add add3 (suc zero , one , zero)  = refl
proof-add add3 (suc zero , two , zero)  = refl
proof-add add3 (suc zero , zero , one)  = refl
proof-add add3 (suc zero , one , one)   = refl
proof-add add3 (suc zero , two , one)   = refl
proof-add add3 (suc zero , zero , two)  = refl
proof-add add3 (suc zero , one , two)   = refl
proof-add add3 (suc zero , two , two)   = refl

mul3 : Multiplier interpret3
mult mul3 zero zero = zero , zero
mult mul3 zero one  = zero , zero
mult mul3 zero two  = zero , zero
mult mul3 one zero  = zero , zero
mult mul3 one one   = zero , one
mult mul3 one two   = zero , two
mult mul3 two zero  = zero , zero
mult mul3 two one   = zero , two
mult mul3 two two   = one  , one
zeroM mul3 = zero
proof-mult mul3 zero zero = refl
proof-mult mul3 zero one  = refl
proof-mult mul3 zero two  = refl
proof-mult mul3 one zero  = refl
proof-mult mul3 one one   = refl
proof-mult mul3 one two   = refl
proof-mult mul3 two zero  = refl
proof-mult mul3 two one   = refl
proof-mult mul3 two two   = refl

--------------------------------------------------------------------------------

add2x2 : Adder (pairμ interpret2)
add2x2 = bigger-adder add2 add2

mul2x2 : _
mul2x2 = compose add2 add2x2 mul2

add2x2x2x2 : Adder (pairμ (pairμ interpret2))
add2x2x2x2 = bigger-adder add2x2 add2x2

mul2x2x2x2 : _
mul2x2x2x2 = compose add2x2 add2x2x2x2 mul2x2

add3x3 : Adder (pairμ interpret3)
add3x3 = bigger-adder add3 add3

mul3x3 : Multiplier (pairμ interpret3)
mul3x3 = compose add3 add3x3 mul3

--------------------------------------------------------------------------------

composeTheValues : {A B : Set} {m n : ℕ} → Vec A m → Vec B n → Vec (A × B) (m * n)
composeTheValues as bs = concat $ V.map (λ a → V.map (a ,_) bs) as

--------------------------------------------------------------------------------

allBools : Vec Bool 2
allBools = false ∷ true ∷ []

allBools2x2 : Vec (Bool × Bool) 4
allBools2x2 = composeTheValues allBools allBools

allBools2x2x2x2 : Vec ((Bool × Bool) × (Bool × Bool)) 16
allBools2x2x2x2 = composeTheValues allBools2x2 allBools2x2

--------------------------------------------------------------------------------

allThrees : Vec Three 3
allThrees = zero ∷ one ∷ two ∷ []

allThrees3x3 : Vec (Three × Three) 9
allThrees3x3 = composeTheValues allThrees allThrees

--------------------------------------------------------------------------------

-- 2 bit multiplcation table
_ : (V.map (toℕ ∘ pairμ (pairμ interpret2) ∘ uncurry (mult mul2x2)) $ composeTheValues allBools2x2 allBools2x2)
  ≡ (0 ∷ 0 ∷ 0 ∷ 0
   ∷ 0 ∷ 1 ∷ 2 ∷ 3
   ∷ 0 ∷ 2 ∷ 4 ∷ 6
   ∷ 0 ∷ 3 ∷ 6 ∷ 9
   ∷ [])
_ = refl

_ : (V.map (toℕ ∘ pairμ (pairμ interpret2) ∘ uncurry (mult mul2x2)) $ composeTheValues allBools2x2 allBools2x2)
  ≡ V.concat (V.tabulate {n = 4} λ a → V.tabulate {n = 4} λ b → toℕ a * toℕ b)
_ = refl

-- 4 bit multiplcation table
_ : (V.map (toℕ ∘ pairμ (pairμ (pairμ interpret2)) ∘ uncurry (mult mul2x2x2x2)) $ composeTheValues allBools2x2x2x2 allBools2x2x2x2)
  ≡ (0 ∷  0 ∷  0 ∷  0 ∷  0 ∷ 0  ∷ 0  ∷   0 ∷   0 ∷   0 ∷   0 ∷   0 ∷   0 ∷   0 ∷   0 ∷   0
   ∷ 0 ∷  1 ∷  2 ∷  3 ∷  4 ∷ 5  ∷ 6  ∷   7 ∷   8 ∷   9 ∷  10 ∷  11 ∷  12 ∷  13 ∷  14 ∷  15
   ∷ 0 ∷  2 ∷  4 ∷  6 ∷  8 ∷ 10 ∷ 12 ∷  14 ∷  16 ∷  18 ∷  20 ∷  22 ∷  24 ∷  26 ∷  28 ∷  30
   ∷ 0 ∷  3 ∷  6 ∷  9 ∷ 12 ∷ 15 ∷ 18 ∷  21 ∷  24 ∷  27 ∷  30 ∷  33 ∷  36 ∷  39 ∷  42 ∷  45
   ∷ 0 ∷  4 ∷  8 ∷ 12 ∷ 16 ∷ 20 ∷ 24 ∷  28 ∷  32 ∷  36 ∷  40 ∷  44 ∷  48 ∷  52 ∷  56 ∷  60
   ∷ 0 ∷  5 ∷ 10 ∷ 15 ∷ 20 ∷ 25 ∷ 30 ∷  35 ∷  40 ∷  45 ∷  50 ∷  55 ∷  60 ∷  65 ∷  70 ∷  75
   ∷ 0 ∷  6 ∷ 12 ∷ 18 ∷ 24 ∷ 30 ∷ 36 ∷  42 ∷  48 ∷  54 ∷  60 ∷  66 ∷  72 ∷  78 ∷  84 ∷  90
   ∷ 0 ∷  7 ∷ 14 ∷ 21 ∷ 28 ∷ 35 ∷ 42 ∷  49 ∷  56 ∷  63 ∷  70 ∷  77 ∷  84 ∷  91 ∷  98 ∷ 105
   ∷ 0 ∷  8 ∷ 16 ∷ 24 ∷ 32 ∷ 40 ∷ 48 ∷  56 ∷  64 ∷  72 ∷  80 ∷  88 ∷  96 ∷ 104 ∷ 112 ∷ 120
   ∷ 0 ∷  9 ∷ 18 ∷ 27 ∷ 36 ∷ 45 ∷ 54 ∷  63 ∷  72 ∷  81 ∷  90 ∷  99 ∷ 108 ∷ 117 ∷ 126 ∷ 135
   ∷ 0 ∷ 10 ∷ 20 ∷ 30 ∷ 40 ∷ 50 ∷ 60 ∷  70 ∷  80 ∷  90 ∷ 100 ∷ 110 ∷ 120 ∷ 130 ∷ 140 ∷ 150
   ∷ 0 ∷ 11 ∷ 22 ∷ 33 ∷ 44 ∷ 55 ∷ 66 ∷  77 ∷  88 ∷  99 ∷ 110 ∷ 121 ∷ 132 ∷ 143 ∷ 154 ∷ 165
   ∷ 0 ∷ 12 ∷ 24 ∷ 36 ∷ 48 ∷ 60 ∷ 72 ∷  84 ∷  96 ∷ 108 ∷ 120 ∷ 132 ∷ 144 ∷ 156 ∷ 168 ∷ 180
   ∷ 0 ∷ 13 ∷ 26 ∷ 39 ∷ 52 ∷ 65 ∷ 78 ∷  91 ∷ 104 ∷ 117 ∷ 130 ∷ 143 ∷ 156 ∷ 169 ∷ 182 ∷ 195
   ∷ 0 ∷ 14 ∷ 28 ∷ 42 ∷ 56 ∷ 70 ∷ 84 ∷  98 ∷ 112 ∷ 126 ∷ 140 ∷ 154 ∷ 168 ∷ 182 ∷ 196 ∷ 210
   ∷ 0 ∷ 15 ∷ 30 ∷ 45 ∷ 60 ∷ 75 ∷ 90 ∷ 105 ∷ 120 ∷ 135 ∷ 150 ∷ 165 ∷ 180 ∷ 195 ∷ 210 ∷ 225
   ∷ [])
_ = refl


_ : (V.map (toℕ ∘ pairμ (pairμ (pairμ interpret2)) ∘ uncurry (mult mul2x2x2x2)) $ composeTheValues allBools2x2x2x2 allBools2x2x2x2)
  ≡ V.concat (V.tabulate {n = 16} λ a → V.tabulate {n = 16} λ b → toℕ a * toℕ b)
_ = refl


-- 2 trit multiplcation table
_ : (V.map (toℕ ∘ pairμ (pairμ interpret3) ∘ uncurry (mult mul3x3)) $ composeTheValues allThrees3x3 allThrees3x3)
 ≡ (0 ∷ 0 ∷  0 ∷  0 ∷  0 ∷  0 ∷  0 ∷  0 ∷  0
  ∷ 0 ∷ 1 ∷  2 ∷  3 ∷  4 ∷  5 ∷  6 ∷  7 ∷  8
  ∷ 0 ∷ 2 ∷  4 ∷  6 ∷  8 ∷ 10 ∷ 12 ∷ 14 ∷ 16
  ∷ 0 ∷ 3 ∷  6 ∷  9 ∷ 12 ∷ 15 ∷ 18 ∷ 21 ∷ 24
  ∷ 0 ∷ 4 ∷  8 ∷ 12 ∷ 16 ∷ 20 ∷ 24 ∷ 28 ∷ 32
  ∷ 0 ∷ 5 ∷ 10 ∷ 15 ∷ 20 ∷ 25 ∷ 30 ∷ 35 ∷ 40
  ∷ 0 ∷ 6 ∷ 12 ∷ 18 ∷ 24 ∷ 30 ∷ 36 ∷ 42 ∷ 48
  ∷ 0 ∷ 7 ∷ 14 ∷ 21 ∷ 28 ∷ 35 ∷ 42 ∷ 49 ∷ 56
  ∷ 0 ∷ 8 ∷ 16 ∷ 24 ∷ 32 ∷ 40 ∷ 48 ∷ 56 ∷ 64
  ∷ [])
_ = refl

_ : (V.map (toℕ ∘ pairμ (pairμ interpret3) ∘ uncurry (mult mul3x3)) $ composeTheValues allThrees3x3 allThrees3x3)
 ≡ V.concat (V.tabulate {n = 9} λ a → V.tabulate {n = 9} λ b → toℕ a * toℕ b)
_ = refl

