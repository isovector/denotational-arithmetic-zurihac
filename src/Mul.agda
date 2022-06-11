module Mul where

open import Function
open import Data.Bool hiding (_<_; _≤_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product hiding (map)
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

record IsSemiring {A : Set} (μ : A → ℕ) : Set where
  field
    -- some constraint on a-size
    a-size : ℕ
    add : A → A → Bool × A
    mult : A → A → A × A
    zero' : A
    one : A
    proof-zero : μ zero' ≡ 0
    proof-one : μ one ≡ 1

  carry-size : Bool × A → ℕ
  carry-size = λ { (overflow , result) → (if overflow then a-size else 0) + μ result }

  mult-size : A × A → ℕ
  mult-size = λ { (hi , lo) → μ hi * a-size + μ lo }

  field
    proof-add : (m n : A) → carry-size (add m n) ≡ μ m + μ n
    proof-mult : (m n : A) → mult-size (mult m n) ≡ μ m * μ n

open IsSemiring

bval : IsSemiring interpretB
a-size bval = 2
add bval false false = false , false
add bval false true = false , true
add bval true false = false , true
add bval true true = true , false
mult bval false false = false , false
mult bval false true = false , false
mult bval true false = false , false
mult bval true true = false , true
zero' bval = false
one bval = true
proof-zero bval = refl
proof-one bval = refl
proof-add bval false false = refl
proof-add bval false true = refl
proof-add bval true false = refl
proof-add bval true true = refl
proof-mult bval false false = refl
proof-mult bval false true = refl
proof-mult bval true false = refl
proof-mult bval true true = refl

compose
  : ∀ {A B}
  → {μ1 : A → ℕ} {μ2 : B → ℕ}
  → (f : IsSemiring μ1)
  → (g : IsSemiring μ2)
  → IsSemiring {A × B} λ { (a , b) → (μ1 a) * g .a-size + μ2 b }
a-size (compose f g) = f .a-size * g .a-size
add (compose f g) (xhi , xlo) (yhi , ylo) =
  let (cb , b) = g .add xlo ylo
      (ca , a) = f .add xhi yhi
   in case cb of λ
        { false → ca , a , b
        ; true → ca , ? , b
        }
mult (compose f g) (xhi , xlo) (yhi , ylo) =
  let (bhi , blo) = g .mult xlo ylo
      (ahi , alo) = f .mult xhi yhi
   in (ahi , bhi) , (alo , blo)
zero' (compose f g) = f .zero' , g .zero'
one (compose f g) = f .zero' , g .one
proof-zero (compose f g)
  rewrite proof-zero f
        | proof-zero g = refl
proof-one (compose f g)
  rewrite proof-zero f
        | proof-one g = refl
proof-add (compose f g) = {! !}
proof-mult (compose f g) (ahi , bhi) (alo , blo) = {! !}




-- combine : IsMult A → IsMult B → IsMult (A × B)



-- multV : {m n : ℕ} → Bits m → Bits n → Vec (Bits m) n
-- multV x y = ?

-- mult' : τ → σ → τ × σ


-- addV : {m n : ℕ} → Bits m → Bits n → Bits (suc (m ⊔ n))
-- addV = ?



-- _ : mulℕ 2 5 ≡ 10
-- _ = refl


-- toBool : Fin 2 → Bool
-- toBool zero = false
-- toBool (suc x) = true

-- splice : {m : ℕ} → Fin (2 ^ m) → Vec Bool m
-- splice {zero} x = []
-- splice {suc m} x =
--   let b , f = remQuot {2} (2 ^ m) x
--    in toBool b ∷ splice f

-- sixteen : Fin 16
-- sixteen = inject+ _ (fromℕ 15)


-- _ : interpret2^ {4} (splice sixteen) ≡ sixteen
-- _ = refl

-- -- -- addV : {m n : ℕ} → Vec Bool m → Vec Bool n → Fin (2 ^ m + 2 ^ n)
-- -- -- addV a b = interpret2^ a + interpret2^ b

-- -- -- mulV : {m n : ℕ} → Vec Bool m → Vec Bool n → Fin (2 ^ (m + n))
-- -- -- mulV a b = {! !}

