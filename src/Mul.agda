module Mul where

open import Function.Base
open import Data.Bool.Base hiding (_<_; _≤_)
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Product as P hiding (map)
open import Data.Fin.Base as F hiding (_+_; _<_; _≤_)
open import Data.Fin.Properties hiding (bounded)
open import Relation.Binary.PropositionalEquality

addF' : {m n : ℕ} → Fin (suc m) → Fin n → Fin (m + n)
addF' {m} {n} (zero {x}) y = cast (+-comm n m) (inject+ m y)
addF' {suc m} {n} (suc x) y = suc (addF' x y)

mulF' : {m n : ℕ} → Fin m → Fin n → Fin (m * n)
mulF' zero zero = zero
mulF' zero (suc n) = zero
mulF' (suc m) zero = zero
mulF' {m = suc m} {suc n} (suc x) (suc y) = inject₁ (addF' (suc y) (mulF' x (suc y)))

interpretBF : Bool → Fin 2
interpretBF false = zero
interpretBF true = suc zero



add3 : ∀ {m n p} → Fin m × Fin n × Fin p → ℕ
add3 (m , n , p) = toℕ m + toℕ n + toℕ p

digitize : ∀ {m n} → Fin m × Fin n → ℕ
digitize = toℕ ∘ uncurry combine ∘ swap

record IsAdd {τ : Set} {size : ℕ} (μ : τ → Fin size) : Set where
  constructor adds
  field
    add : Fin 2 × τ × τ → τ × Fin 2
    zeroA : τ
    proof-add
      : (mnp : Fin 2 × τ × τ)
      → digitize (P.map μ id (add mnp)) ≡ add3 (P.map id (P.map μ μ) mnp)


record IsMult {τ : Set} {size : ℕ} (μ : τ → Fin size) : Set where
  constructor multiples
  field
    mult : τ → τ → τ × τ
    zeroM : τ
    proof-mult
      : (m n : τ)
      → uncurry combine (P.map μ μ (mult m n))  -- 1
      ≡ mulF' (μ m) (μ n)  -- 2

open IsAdd
open IsMult

pairμ : {τ : Set} → {size : ℕ} → (τ → Fin size) → (τ × τ → Fin (size * size))
pairμ μ = uncurry combine ∘ P.map μ μ

module _ {τ : Set} {size : ℕ} {μ : τ → Fin size} where
  add3Adder' : IsAdd (pairμ μ) → Fin 2 → τ → τ → τ → (τ × τ)
  add3Adder' (adds add z _) cin a b c =
    let (ab  , cout1)  = add (cin , (proj₂ z , a) , (proj₂ z , b))
        (abc , cout2)  = add (zero , ab , (proj₂ z , c))
     in abc

-- (a , b) * (c , d)
-- (ax + b) * (cx + d)
-- (acx^2 + adx + bcx + bd)
-- ((0x + 6)x^2 + (0x + 3)x + (3x + 0)x + (1x + 5))
-- (0x^3 + 6x^2 + 0x^2 + 3x + 3x^2 + 0x + 1x + 5)
-- (0x^3 + (6 + 0 + 3)x^2 + (3 + 0 + 1)x + 5)
-- ((0 , 9) , (4 , 5))


compose
    : {τ : Set} {size : ℕ} {μ : τ → Fin size}
    → IsAdd μ
    → IsAdd (pairμ μ)
    → IsMult μ
    → IsMult {τ × τ} {size * size} (pairμ μ)
IsMult.mult (compose {τ} {size} {μ} small adder multipler) (a , b) (c , d) =
  let (k0 , l) = multipler .mult a c -- x2
      (g , h)  = multipler .mult a d
      (e , f)  = multipler .mult b d
      (i , j)  = multipler .mult b c

      (ehjhi , ehj)   = add3Adder' {τ = τ} {size} {μ} adder zero e h j
      (lighi , liglo) = add3Adder' {τ = τ} {size} {μ} adder zero l i g
      (lig , carry)   = small .add (zero  , ehjhi , liglo)
      (k , _)         = small .add (carry , k0    , lighi)

      -- (ax + b) * (cx + d) = (acx^2 + bcx + adx + bd)
      -- bd = (ex + f)
      -- ad = (gx + h)
      -- bc = (ix + j)
      -- ac = (kx + l)
      -- = (kx + l)x^2 + (ix + j)x + (gx + h)x + (ex + f))
      -- = (kx^3 + (l + i + g)x^2 + (j + h + e)x + f
   in (k , lig) , (ehj , f)
IsMult.zeroM (compose small adder multipler) = multipler .zeroM  , multipler .zeroM
IsMult.proof-mult (compose {μ = μ} small adder multipler) ab@(a , b) cd@(c , d) = {!!}

open IsMult

bvalA : IsAdd interpretBF
add bvalA (zero , false , false) = false , zero
add bvalA (zero , false , true) = true , zero
add bvalA (zero , true , false) = true , zero
add bvalA (zero , true , true) = false , suc zero
add bvalA (suc zero , false , false) = true , zero
add bvalA (suc zero , false , true) = false , suc zero
add bvalA (suc zero , true , false) = false , suc zero
add bvalA (suc zero , true , true) = true , suc zero
zeroA bvalA = false
proof-add bvalA (zero , false , false) = refl
proof-add bvalA (zero , false , true) = refl
proof-add bvalA (zero , true , false) = refl
proof-add bvalA (zero , true , true) = refl
proof-add bvalA (suc zero , false , false) = refl
proof-add bvalA (suc zero , false , true) = refl
proof-add bvalA (suc zero , true , false) = refl
proof-add bvalA (suc zero , true , true) = refl


bval : IsMult interpretBF
mult bval false false = false , false
mult bval false true = false , false
mult bval true false = false , false
mult bval true true = false , true
zeroM bval = false
proof-mult bval false false = refl
proof-mult bval false true = refl
proof-mult bval true false = refl
proof-mult bval true true = refl

data Three : Set where
  zero : Three
  one : Three
  two : Three

interpretThree : Three → Fin 3
interpretThree zero = zero
interpretThree one = suc zero
interpretThree two = suc (suc zero)

addThree : IsAdd interpretThree
add addThree (zero , zero , zero) = zero , zero
add addThree (zero , zero , one) = one , zero
add addThree (zero , zero , two) =  two , zero
add addThree (zero , one , zero) = one , zero
add addThree (zero , one , one) = two , zero
add addThree (zero , one , two) = zero , suc zero
add addThree (zero , two , zero) = two , zero
add addThree (zero , two , one) = zero , suc zero
add addThree (zero , two , two) = one , suc zero
add addThree (suc zero , zero , zero) = one , zero
add addThree (suc zero , one , zero) = two , zero
add addThree (suc zero , two , zero) = zero , suc zero
add addThree (suc zero , zero , one) = two , zero
add addThree (suc zero , one , one) = zero , suc zero
add addThree (suc zero , two , one) = one , suc zero
add addThree (suc zero , zero , two) = zero , suc zero
add addThree (suc zero , one , two) = one , suc zero
add addThree (suc zero , two , two) = two , suc zero
zeroA addThree = zero
proof-add addThree (zero , zero , zero) = refl
proof-add addThree (zero , zero , one) = refl
proof-add addThree (zero , zero , two) = refl
proof-add addThree (zero , one , zero) = refl
proof-add addThree (zero , one , one) = refl
proof-add addThree (zero , one , two) = refl
proof-add addThree (zero , two , zero) = refl
proof-add addThree (zero , two , one) = refl
proof-add addThree (zero , two , two) = refl
proof-add addThree (suc zero , zero , zero) = refl
proof-add addThree (suc zero , one , zero) = refl
proof-add addThree (suc zero , two , zero) = refl
proof-add addThree (suc zero , zero , one) = refl
proof-add addThree (suc zero , one , one) = refl
proof-add addThree (suc zero , two , one) = refl
proof-add addThree (suc zero , zero , two) = refl
proof-add addThree (suc zero , one , two) = refl
proof-add addThree (suc zero , two , two) = refl

multThree : IsMult interpretThree
mult multThree zero zero = zero , zero
mult multThree zero one = zero , zero
mult multThree zero two = zero , zero
mult multThree one zero = zero , zero
mult multThree one one = zero , one
mult multThree one two = zero , two
mult multThree two zero = zero , zero
mult multThree two one = zero , two
mult multThree two two = one , one
zeroM multThree = zero
proof-mult multThree zero zero = refl
proof-mult multThree zero one = refl
proof-mult multThree zero two = refl
proof-mult multThree one zero = refl
proof-mult multThree one one = refl
proof-mult multThree one two = refl
proof-mult multThree two zero = refl
proof-mult multThree two one = refl
proof-mult multThree two two = refl

bigger-adder : {τ : Set} {size : ℕ} {μ : τ → Fin size} → IsAdd μ → IsAdd μ → IsAdd (pairμ μ)
add (bigger-adder x y) (cin , (mhi , mlo) , (nhi , nlo)) =
  let (lo , cmid) = y .add (cin , mlo ,  nlo)
      (hi , cout) = x .add (cmid , mhi , nhi)
   in ((hi , lo) , cout)
zeroA (bigger-adder x y) = x .zeroA , y .zeroA
proof-add (bigger-adder {μ = μ} x y) mnp@(cin , m@(mhi , mlo) , n@(nhi , nlo))
  with y .add (cin , mlo ,  nlo)
... | (lo , cmid) with x .add (cmid , mhi , nhi)
... | (hi , cout) =
  begin
    toℕ (combine cout (combine (μ hi) (μ lo)))
  ≡⟨ ? ⟩
    ?
  ≡⟨ {! proof-add !} ⟩
    toℕ cin + (toℕ (combine (μ mhi) (μ mlo)) + toℕ (combine (μ nhi) (μ nlo)))
  ≡⟨ sym $ +-assoc (toℕ cin) _ _ ⟩
    (toℕ cin + toℕ (combine (μ mhi) (μ mlo))) + toℕ (combine (μ nhi) (μ nlo))
  ∎
  where open ≡-Reasoning

  -- begin
  --   digitize (P.map (pairμ μ) id (add (bigger-adder x y) mnp))
  -- ≡⟨⟩
  --   (toℕ ∘ uncurry combine ∘ swap) (P.map (pairμ μ) id (add (bigger-adder x y) mnp))
  -- ≡⟨⟩
  --   (toℕ ∘ uncurry combine ∘ swap) (P.map (pairμ μ) id (add (bigger-adder x y) mnp))
  -- ≡⟨ ? ⟩
  --   toℕ cin + toℕ (pairμ μ m) + toℕ (pairμ μ n)
  -- ≡⟨⟩
  --   add3 (P.map id (P.map (pairμ μ) (pairμ μ)) mnp)
  -- ∎
  --


-- _ : mult (compose bvalA bval) (true , true) (true , true) ≡ ((true , false) , (false , true))
-- _ = refl


-- _ : mult (compose addThree multThree) (zero , one) (zero , one) ≡ ((zero , zero) , (zero , one))
-- _ = refl


-- _ : mult (compose addThree multThree) (zero , one) (one , zero) ≡ ((zero , zero) , (one , zero))
-- _ = refl


-- -- 4 * 4
-- _ : mult (compose addThree multThree) (one , zero) (one , zero) ≡ ((zero , one) , (two , one))
-- _ = {!!}
