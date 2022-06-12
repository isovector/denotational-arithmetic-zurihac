module Mul where

open import Function
open import Data.Bool hiding (_<_; _≤_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product hiding (map)
import Data.Product as P
open import Data.Fin hiding (_+_; _<_; _≤_)
open import Data.Fin.Properties hiding (bounded)
import Data.Fin as F
open import Data.Vec
open import Relation.Binary.PropositionalEquality

addℕ : ℕ → ℕ → ℕ
addℕ zero x = x
addℕ (suc a) x = suc (addℕ a x)

-- record Bounded (n : ℕ) : Set where
--   constructor bounded-by
--   field
--     value : ℕ
--     bounded : value < n

-- addB : {m n : ℕ} → Bounded (suc m) → Bounded (suc n) → Bounded (suc (m + n))
-- addB (bounded-by value bounded) (bounded-by value₁ bounded₁) =
--   bounded-by (value + value₁) (let z = +-mono-< bounded bounded₁ in ?)


addF : {m n : ℕ} → Fin (suc m) → Fin (suc n) → Fin (suc (m + n))
addF {m} {n} (zero {x}) y = cast (cong suc (+-comm n m)) (inject+ m y)
addF {suc m} {n} (suc x) y = suc (addF x y)

addF' : {m n : ℕ} → Fin (suc m) → Fin n → Fin (m + n)
addF' {m} {n} (zero {x}) y = cast (+-comm n m) (inject+ m y)
addF' {suc m} {n} (suc x) y = suc (addF' x y)

im-finna-add
    : {m n : ℕ}
    → (x : Fin (suc m))
    → (y : Fin (suc n))
    → toℕ (addF x y) ≡ toℕ x + toℕ y
im-finna-add {n = n} (zero {x}) y =
  begin
    toℕ (cast _ (inject+ x y))  ≡⟨ toℕ-cast (cong suc (+-comm n x)) (inject+ x y) ⟩
    toℕ (inject+ x y)           ≡⟨ sym (toℕ-inject+ x y) ⟩
    toℕ y                       ∎
  where open ≡-Reasoning
im-finna-add {suc m} (suc x) y = cong suc (im-finna-add x y)

mulℕ : ℕ → ℕ → ℕ
mulℕ zero b = zero
mulℕ (suc a) b = b + mulℕ a b

mulF : {m n : ℕ} → Fin (suc m) → Fin (suc n) → Fin (suc (m * n))
mulF zero y = zero
mulF {suc m} {n} (suc x) y = addF y (mulF x y)

mulF' : {m n : ℕ} → Fin m → Fin n → Fin (m * n)
mulF' zero zero = zero
mulF' zero (suc n) = zero
mulF' (suc m) zero = zero
mulF' {m = suc m} {suc n} (suc x) (suc y) = suc {! addF' !}




im-finna-mul
    : {m n : ℕ}
    → (x : Fin (suc m))
    → (y : Fin (suc n))
    → toℕ (mulF x y) ≡ toℕ x * toℕ y
im-finna-mul zero y = refl
im-finna-mul {suc m} (suc x) y =
  begin
    toℕ (mulF (suc x) y)     ≡⟨⟩
    toℕ (addF y (mulF x y))  ≡⟨ im-finna-add y (mulF x y) ⟩
    toℕ y + toℕ (mulF x y)   ≡⟨ cong (toℕ y +_) (im-finna-mul x y) ⟩
    toℕ y + toℕ x * toℕ y    ∎
  where open ≡-Reasoning

infixl 6 _Fℕ+_
-- Fin addition with a nat on the left
_Fℕ+_ : ∀ {n} (i : ℕ) (j : Fin n) → Fin (i + n)
zero  Fℕ+ j = j
suc i Fℕ+ j = suc (i Fℕ+ j)

Bits : ℕ → Set
Bits = Vec Bool

interpret2^ : {m : ℕ} → Bits m → Fin (2 ^ m)
interpret2^ [] = zero
interpret2^ (false ∷ y) = inject+ _ (interpret2^ y)
interpret2^ {suc m} (true ∷ y) rewrite +-comm (2 ^ m) (0 * 2 ^ m) =
  2 ^ m Fℕ+ interpret2^ {m} y


interpretBF : Bool → Fin 2
interpretBF false = zero
interpretBF true = suc zero

interpretB : Bool → ℕ
interpretB false = 0
interpretB true = 1

interpretV : {n : ℕ} → Bits n → ℕ
interpretV = sum ∘ map interpretB

zeroV : {n : ℕ} → Bits n
zeroV = replicate false

oneV : {n : ℕ} → Bits (suc n)
oneV = true ∷ zeroV

addV : {m n : ℕ} → Bits m → Bits n → Bits (m + n)
addV = _++_


map-++ : {A B : Set} {m n : ℕ} → (f : A → B) → (x : Vec A m) → (y : Vec A n) → map f (x ++ y) ≡ map f x ++ map f y
map-++ f [] y = refl
map-++ f (x ∷ xs) y rewrite map-++ f xs y = refl

sum-++ : {m n : ℕ} → (x : Vec ℕ m) → (y : Vec ℕ n) → sum (x ++ y) ≡ sum x + sum y
sum-++ [] y = refl
sum-++ (x ∷ xs) y rewrite sum-++ xs y | sym (+-assoc x (sum xs) (sum y)) = refl

homoAddV : {m n : ℕ} → (x : Bits m) → (y : Bits n) → interpretV (addV x y) ≡ interpretV x + interpretV y
homoAddV x y =
  begin
    interpretV (addV x y)                       ≡⟨⟩
    sum (map interpretB (x ++ y))               ≡⟨ cong sum $ map-++ interpretB x y ⟩
    sum (map interpretB x ++ map interpretB y)  ≡⟨ sum-++ (map interpretB x) (map interpretB y) ⟩
    interpretV x + interpretV y                 ∎
  where open ≡-Reasoning

homo0 : {n : ℕ} → interpretV (zeroV {n}) ≡ 0
homo0 {zero} = refl
homo0 {suc n} rewrite homo0 {n} = refl

homo1 : {n : ℕ} → interpretV (oneV {n}) ≡ 1
homo1 {zero} = refl
homo1 {suc n} rewrite homo0 {n} = refl

mulV : {m n : ℕ} → Bits m → Bits n → Bits (m * n)
mulV [] y = []
mulV (false ∷ xs) y = addV zeroV $ mulV xs y
mulV (true ∷ xs) y = addV y $ mulV xs y

-- -- homoAddV : interpretV (addV x y) ≡ interpretV x + interpretV y
-- homoMulV : {m n : ℕ} → (x : Bits m) → (y : Bits n) → interpretV (mulV x y) ≡ interpretV x * interpretV y
-- homoMulV [] y = refl
-- --  ≡
-- homoMulV {m} {n} (false ∷ xs) y = ?
--   -- begin
--   --   interpretV (addV {m = m} zeroV (mulV xs y))
--   -- ≡⟨ ? ⟩
--   --   interpretV (false ∷ xs) * interpretV y
--   -- ∎
--   -- where open ≡-Reasoning
-- homoMulV (true ∷ xs) y = {! !}

-- (

add3 : ∀ {m n p} → Fin m × Fin n × Fin p → ℕ
add3 (m , n , p) = toℕ m + toℕ n + toℕ p

digitize : ∀ {m n} → Fin m × Fin n → ℕ
digitize = toℕ ∘ uncurry combine

record IsAdd {τ : Set} {size : ℕ} (μ : τ → Fin size) : Set where
  constructor adds
  field
    add : Fin 2 × τ × τ → τ × Fin 2
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
      → uncurry combine (P.map μ μ (mult m n)) ≡ mulF' (μ m) (μ n)

open IsAdd
open IsMult

module _ {τ : Set} {size : ℕ} {μ : τ → Fin size} where
  add3Adder : IsAdd μ → Fin 2 → τ → τ → τ → τ × Fin 2
  add3Adder (adds add _) cin a b c =
    let (ab , cout) = add (cin , a , b)
     in add (cout , ab , c)

composeMultFin : {τ : Set} → {size : ℕ} → (τ → Fin size) → (τ × τ → Fin (size * size))
composeMultFin μ = uncurry combine ∘ P.map μ μ

compose
    : {τ : Set} {size : ℕ} {μ : τ → Fin size}
    → IsAdd μ
    → IsMult μ
    → IsMult {τ × τ} {size * size} (composeMultFin μ)
IsMult.mult (compose adder multipler) (a , b) (c , d) =
  let (k , l) = multipler .mult a c -- x2
      (g , h) = multipler .mult a d
      (e , f) = multipler .mult b d
      (i , j) = multipler .mult b c

      (ehj , carry1)  = add3Adder adder zero   e h j
      (lig , carry2)  = add3Adder adder carry1 l i g

      -- (ax + b) * (cx + d) = (acx^2 + bcx + adx + bd)
      -- bd = (ex + f)
      -- ad = (gx + h)
      -- bc = (ix + j)
      -- ac = (kx + l)
      -- = (kx + l)x^2 + (ix + j)x + (gx + h)x + (ex + f))
      -- = (kx^3 + (l + i + g)x^2 + (j + h + e)x + f
   in (proj₁ (adder .add (carry2 , k , multipler .zeroM)) , lig) , (ehj , f)
IsMult.zeroM (compose adder multipler) = multipler .zeroM  , multipler .zeroM
IsMult.proof-mult (compose {μ = μ} adder multipler) ab@(a , b) cd@(c , d) = ?
  -- begin
  --   digitize
  --    (P.map (composeMultFin μ) (composeMultFin μ)
  --     (mult (compose adder multipler) ab cd))
  -- ≡⟨⟩
  --   (toℕ ∘ uncurry combine)
  --    (P.map (composeMultFin μ) (composeMultFin μ)
  --     (mult (compose adder multipler) ab cd))
  -- ≡⟨ ? ⟩
  --   toℕ (composeMultFin μ ab) * toℕ (composeMultFin μ cd)
  -- ∎
  -- where open ≡-Reasoning

-- digitize : ∀ {m n} → Fin m × Fin n → ℕ
-- digitize = toℕ ∘ uncurry combine


-- -- 9 : Fin 10 *
-- -- 8 : Fin 10

-- -- v (hi : Fin 10)
-- --  v (lo : Fin 10)
-- -- 72 : Fin 100


open IsMult

bval : IsMult interpretBF
-- add bval = ?
mult bval false false = false , false
mult bval false true = false , false
mult bval true false = false , false
mult bval true true = false , true
zeroM bval = false
proof-mult bval false false = refl
proof-mult bval false true = ?
proof-mult bval true false = ?
proof-mult bval true true = ?

-- compose
--   : ∀ {A B}
--   → {μ1 : A → ℕ} {μ2 : B → ℕ}
--   → (f : IsMult μ1)
--   → (g : IsMult μ2)
--   → IsMult {A × B} λ { (a , b) → (μ1 a) * g .a-size + μ2 b }
-- a-size (compose f g) = f .a-size * g .a-size
-- add (compose f g) (xhi , xlo) (yhi , ylo) =
--   let (cb , b) = g .add xlo ylo
--       (ca , a) = f .add xhi yhi
--    in case cb of λ
--         { false → ca , a , b
--         ; true → ca , ? , b
--         }
-- mult (compose f g) (xhi , xlo) (yhi , ylo) =
--   let (bhi , blo) = g .mult xlo ylo
--       (ahi , alo) = f .mult xhi yhi
--    in (ahi , bhi) , (alo , blo)
-- zero' (compose f g) = f .zero' , g .zero'
-- one (compose f g) = f .zero' , g .one
-- proof-zero (compose f g)
--   rewrite proof-zero f
--         | proof-zero g = refl
-- proof-one (compose f g)
--   rewrite proof-zero f
--         | proof-one g = refl
-- proof-add (compose f g) = {! !}
-- proof-mult (compose f g) (ahi , bhi) (alo , blo) = {! !}




-- -- combine : IsMult A → IsMult B → IsMult (A × B)



-- -- multV : {m n : ℕ} → Bits m → Bits n → Vec (Bits m) n
-- -- multV x y = ?

-- -- mult' : τ → σ → τ × σ


-- -- addV : {m n : ℕ} → Bits m → Bits n → Bits (suc (m ⊔ n))
-- -- addV = ?



-- -- _ : mulℕ 2 5 ≡ 10
-- -- _ = refl


-- -- toBool : Fin 2 → Bool
-- -- toBool zero = false
-- -- toBool (suc x) = true

-- -- splice : {m : ℕ} → Fin (2 ^ m) → Vec Bool m
-- -- splice {zero} x = []
-- -- splice {suc m} x =
-- --   let b , f = remQuot {2} (2 ^ m) x
-- --    in toBool b ∷ splice f

-- -- sixteen : Fin 16
-- -- sixteen = inject+ _ (fromℕ 15)


-- -- _ : interpret2^ {4} (splice sixteen) ≡ sixteen
-- -- _ = refl

-- -- -- -- addV : {m n : ℕ} → Vec Bool m → Vec Bool n → Fin (2 ^ m + 2 ^ n)
-- -- -- -- addV a b = interpret2^ a + interpret2^ b

-- -- -- -- mulV : {m n : ℕ} → Vec Bool m → Vec Bool n → Fin (2 ^ (m + n))
-- -- -- -- mulV a b = {! !}

