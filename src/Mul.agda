module Mul where

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

--------------------------------------------------------------------------------

addF' : {m n : ℕ} → Fin (suc m) → Fin n → Fin (m + n)
addF' {m} {n} (zero {x}) y = cast (+-comm n m) (inject+ m y)
addF' {suc m} {n} (suc x) y = suc (addF' x y)

mulF' : {m n : ℕ} → Fin m → Fin n → Fin (m * n)
mulF' zero zero = zero
mulF' zero (suc n) = zero
mulF' (suc m) zero = zero
mulF' {m = suc m} {suc n} (suc x) (suc y) = inject₁ (addF' (suc y) (mulF' x (suc y)))

--------------------------------------------------------------------------------

toℕ-addF' : ∀ {m n} (x : Fin (suc m)) (y : Fin n) → toℕ (addF' x y) ≡ toℕ x + toℕ y
toℕ-addF' {m}            zero    y = trans (toℕ-cast _ (inject+ m y)) (sym $ toℕ-inject+ m y)
toℕ-addF' {m = suc m} (suc x) y = cong suc (toℕ-addF' x y)

addF'3 : ∀ {n p} → Fin 2 × Fin n × Fin p → Fin (n + p)
addF'3 (m , n , p) = addF' (addF' m n) p

--------------------------------------------------------------------------------

digitize : ∀ {m} → Fin m × Fin 2 → Fin (m + m)
digitize {m} = cast (trans (sym $ +-assoc m m 0)(+-comm (m + m) 0)) ∘ uncurry combine ∘ swap

record IsAdd {τ : Set} {size : ℕ} (μ : τ → Fin size) : Set where
  constructor adds
  field
    add : Fin 2 × τ × τ → τ × Fin 2
    zeroA : τ
    proof-add
      : (mnp : Fin 2 × τ × τ)
      → toℕ (digitize (P.map μ id (add mnp))) ≡ toℕ (addF'3 (P.map id (P.map μ μ) mnp))
open IsAdd

--------------------------------------------------------------------------------

record IsMult {τ : Set} {size : ℕ} (μ : τ → Fin size) : Set where
  constructor multiples
  field
    mult : τ → τ → τ × τ
    zeroM : τ
    proof-mult
      : (m n : τ)
      → uncurry combine (P.map μ μ (mult m n))
      ≡ mulF' (μ m) (μ n)
open IsMult

--------------------------------------------------------------------------------

pairμ : {τ : Set} → {size : ℕ} → (τ → Fin size) → (τ × τ → Fin (size * size))
pairμ μ = uncurry combine ∘ P.map μ μ

module _ {τ : Set} {size : ℕ} {μ : τ → Fin size} where
  add3Adder' : IsAdd (pairμ μ) → Fin 2 → τ → τ → τ → (τ × τ)
  add3Adder' (adds add z _) cin a b c =
    let (ab  , cout1)  = add (cin , (proj₂ z , a) , (proj₂ z , b))
        (abc , cout2)  = add (zero , ab , (proj₂ z , c))
     in abc


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

--------------------------------------------------------------------------------

-- this exists in the future
postulate toℕ-combine : ∀ {m n} (i : Fin m) (j : Fin n) → toℕ (combine i j) ≡ n * toℕ i + toℕ j

bigger-adder : {τ : Set} {size : ℕ} {μ : τ → Fin size} → IsAdd μ → IsAdd μ → IsAdd (pairμ μ)
add (bigger-adder x y) (cin , (mhi , mlo) , (nhi , nlo)) =
  let (lo , cmid) = y .add (cin , mlo ,  nlo)
      (hi , cout) = x .add (cmid , mhi , nhi)
   in ((hi , lo) , cout)
zeroA (bigger-adder x y) = x .zeroA , y .zeroA
proof-add (bigger-adder {size = size} {μ = μ}  x y) mnp@(cin , m@(mhi , mlo) , n@(nhi , nlo))
  with y .add (cin , mlo , nlo) in y-eq
... | (lo , cmid) with x .add (cmid , mhi , nhi) in x-eq
... | (hi , cout) = let x-proof = proof-add x (cmid , mhi , nhi)
                        y-proof = proof-add y (cin , mlo , nlo) in
  begin
    toℕ (cast _ (combine cout (combine (μ hi) (μ lo))))                                                              ≡⟨ toℕ-cast _ (combine cout (combine (μ hi) (μ lo))) ⟩
    toℕ (combine cout (combine (μ hi) (μ lo)))                                                                       ≡⟨ toℕ-combine cout _ ⟩
    size * size * toℕ cout + toℕ (combine (μ hi) (μ lo))                                                             ≡⟨ cong (\ φ → size * size * toℕ cout + φ) (toℕ-combine (μ hi) (μ lo)) ⟩
    size * size * toℕ cout + (size * toℕ (μ hi) + toℕ (μ lo))                                                        ≡˘⟨ +-assoc (size * size * toℕ cout) (size * toℕ (μ hi)) (toℕ (μ lo)) ⟩
    size * size * toℕ cout + size * toℕ (μ hi) + toℕ (μ lo)                                                          ≡⟨ cong (λ z → z + size * toℕ (μ hi) + toℕ (μ lo)) (*-assoc size size (toℕ cout)) ⟩
    size * (size * toℕ cout) + size * toℕ (μ hi) + toℕ (μ lo)                                                        ≡˘⟨ cong (_+ toℕ (μ lo)) (*-distribˡ-+ size (size * toℕ cout) (toℕ (μ hi))) ⟩
    size * (size * toℕ cout + toℕ (μ hi)) + toℕ (μ lo)                                                               ≡⟨ cong (\ φ → size * φ + toℕ (μ lo)) $ sym $ toℕ-combine cout (μ hi) ⟩
    size * toℕ (combine cout (μ hi)) + toℕ (μ lo)                                                                    ≡⟨⟩
    size * toℕ (uncurry combine (cout , μ hi)) + toℕ (μ lo)                                                          ≡⟨⟩
    size * toℕ (uncurry combine (P.map₂ μ (cout , hi))) + toℕ (μ lo)                                                 ≡⟨⟩
    size * toℕ (uncurry combine (P.map₂ μ (swap (hi , cout)))) + toℕ (μ lo)                                          ≡⟨ cong (\ φ → size * toℕ (uncurry combine (P.map₂ μ (swap φ))) + toℕ (μ lo)) $ sym $ x-eq ⟩
    size * toℕ (uncurry combine (P.map₂ μ (swap (x .add (cmid , mhi , nhi))))) + toℕ (μ lo)                          ≡⟨ (cong (λ φ → size * φ + toℕ (μ lo)) $ sym $ toℕ-cast _ (uncurry combine (map₂ μ (swap (x .add (cmid , mhi , nhi)))))) ⟩
    size * toℕ (cast _ (uncurry combine (P.map₂ μ (swap (x .add (cmid , mhi , nhi)))))) + toℕ (μ lo)                 ≡⟨ cong (\ φ → size * φ + toℕ (μ lo)) x-proof ⟩
    size * toℕ (addF' (addF' cmid (μ mhi)) (μ nhi)) + toℕ (μ lo)                                                     ≡⟨ cong (\ φ → size * φ + toℕ (μ lo)) $ toℕ-addF' (addF' cmid (μ mhi)) (μ nhi) ⟩
    size * (toℕ (addF' cmid (μ mhi)) + toℕ (μ nhi)) + toℕ (μ lo)                                                     ≡⟨ cong (\ φ → size * (φ + toℕ (μ nhi)) + toℕ (μ lo)) $ toℕ-addF' cmid $ μ mhi  ⟩
    size * (toℕ cmid + toℕ (μ mhi) + toℕ (μ nhi)) + toℕ (μ lo)                                                       ≡⟨ cong (λ z → size * z + toℕ (μ lo)) (+-assoc (toℕ cmid) (toℕ (μ mhi)) (toℕ (μ nhi))) ⟩
    size * (toℕ cmid + (toℕ (μ mhi) + toℕ (μ nhi))) + toℕ (μ lo)                                                     ≡⟨ cong (_+ toℕ (μ lo)) (*-distribˡ-+ size (toℕ cmid) (toℕ (μ mhi) + toℕ (μ nhi))) ⟩
    size * toℕ cmid + size * (toℕ (μ mhi) + toℕ (μ nhi)) + toℕ (μ lo)                                                ≡⟨ +-assoc (size * toℕ cmid) (size * (toℕ (μ mhi) + toℕ (μ nhi))) (toℕ (μ lo)) ⟩
    size * toℕ cmid + (size * (toℕ (μ mhi) + toℕ (μ nhi)) + toℕ (μ lo))                                              ≡⟨ cong (size * toℕ cmid +_) (+-comm (size * (toℕ (μ mhi) + toℕ (μ nhi))) (toℕ (μ lo))) ⟩
    size * toℕ cmid + (toℕ (μ lo) + size * (toℕ (μ mhi) + toℕ (μ nhi)))                                              ≡˘⟨ +-assoc (size * toℕ cmid) (toℕ (μ lo)) (size * (toℕ (μ mhi) + toℕ (μ nhi))) ⟩
    (size * toℕ cmid + toℕ (μ lo)) + size * (toℕ (μ mhi) + toℕ (μ nhi))                                              ≡⟨ cong (\ φ → φ + size * (toℕ (μ mhi) + toℕ (μ nhi))) $ sym $ toℕ-combine cmid (μ lo) ⟩
    toℕ (combine cmid (μ lo)) + size * (toℕ (μ mhi) + toℕ (μ nhi))                                                   ≡⟨⟩
    toℕ (uncurry combine (cmid , μ lo)) + size * (toℕ (μ mhi) + toℕ (μ nhi))                                         ≡⟨⟩
    toℕ (uncurry combine (P.map₂ μ (cmid , lo))) + size * (toℕ (μ mhi) + toℕ (μ nhi))                                ≡⟨⟩
    toℕ (uncurry combine (P.map₂ μ (swap (lo , cmid)))) + size * (toℕ (μ mhi) + toℕ (μ nhi))                         ≡⟨ cong (\ φ → toℕ (uncurry combine (P.map₂ μ (swap φ))) + size * (toℕ (μ mhi) + toℕ (μ nhi))) $ sym y-eq ⟩
    toℕ (uncurry combine (P.map₂ μ (swap (y .add (cin , mlo , nlo))))) + size * (toℕ (μ mhi) + toℕ (μ nhi))          ≡⟨ cong (\ φ → φ + size * (toℕ (μ mhi) + toℕ (μ nhi))) $ sym $ toℕ-cast _ (uncurry combine (P.map₂ μ (swap (y .add (cin , mlo , nlo))))) ⟩
    toℕ (cast _ (uncurry combine (P.map₂ μ (swap (y .add (cin , mlo , nlo)))))) + size * (toℕ (μ mhi) + toℕ (μ nhi)) ≡⟨ cong (\ φ → φ + size * (toℕ (μ mhi) + toℕ (μ nhi))) $ y-proof ⟩
    toℕ (addF' (addF' cin (μ mlo)) (μ nlo)) + size * (toℕ (μ mhi) + toℕ (μ nhi))                                     ≡⟨ cong (\ φ → φ + size * (toℕ (μ mhi) + toℕ (μ nhi))) $ toℕ-addF' (addF' cin (μ mlo)) (μ nlo) ⟩
    toℕ (addF' cin (μ mlo)) + toℕ (μ nlo) + size * (toℕ (μ mhi) + toℕ (μ nhi))                                       ≡⟨ cong (\ φ → φ + toℕ (μ nlo) + size * (toℕ (μ mhi) + toℕ (μ nhi))) $ toℕ-addF' cin (μ mlo) ⟩
    toℕ cin + toℕ (μ mlo) + toℕ (μ nlo) + size * (toℕ (μ mhi) + toℕ (μ nhi))                                         ≡⟨⟩
    ((toℕ cin + toℕ (μ mlo)) + toℕ (μ nlo)) + size * (toℕ (μ mhi) + toℕ (μ nhi))                                     ≡⟨ cong₂ _+_ (+-assoc (toℕ cin) (toℕ (μ mlo)) (toℕ (μ nlo))) (*-distribˡ-+ size (toℕ (μ mhi)) (toℕ (μ nhi))) ⟩
    (toℕ cin + (toℕ (μ mlo) + toℕ (μ nlo))) + (size * toℕ (μ mhi) + size * toℕ (μ nhi))                              ≡˘⟨ +-assoc (toℕ cin + (toℕ (μ mlo) + toℕ (μ nlo))) (size * toℕ (μ mhi)) (size * toℕ (μ nhi)) ⟩
    ((toℕ cin + (toℕ (μ mlo) + toℕ (μ nlo))) + size * toℕ (μ mhi)) + size * toℕ (μ nhi)                              ≡⟨ cong (_+ size * toℕ (μ nhi)) (+-assoc (toℕ cin) (toℕ (μ mlo) + toℕ (μ nlo)) (size * toℕ (μ mhi))) ⟩
    (toℕ cin + ((toℕ (μ mlo) + toℕ (μ nlo)) + size * toℕ (μ mhi))) + size * toℕ (μ nhi)                              ≡⟨ cong (λ z → toℕ cin + z + size * toℕ (μ nhi)) (+-assoc (toℕ (μ mlo)) (toℕ (μ nlo)) (size * toℕ (μ mhi))) ⟩
    (toℕ cin + (toℕ (μ mlo) + (toℕ (μ nlo) + size * toℕ (μ mhi)))) + size * toℕ (μ nhi)                              ≡⟨ cong (λ z → toℕ cin + (toℕ (μ mlo) + z) + size * toℕ (μ nhi)) (+-comm (toℕ (μ nlo)) (size * toℕ (μ mhi))) ⟩
    (toℕ cin + (toℕ (μ mlo) + (size * toℕ (μ mhi) + toℕ (μ nlo)))) + size * toℕ (μ nhi)                              ≡˘⟨ cong (λ z → toℕ cin + z + size * toℕ (μ nhi)) (+-assoc (toℕ (μ mlo)) (size * toℕ (μ mhi)) (toℕ (μ nlo))) ⟩
    (toℕ cin + ((toℕ (μ mlo) + size * toℕ (μ mhi)) + toℕ (μ nlo))) + size * toℕ (μ nhi)                              ≡˘⟨ cong (_+ size * toℕ (μ nhi)) (+-assoc (toℕ cin) (toℕ (μ mlo) + size * toℕ (μ mhi)) (toℕ (μ nlo))) ⟩
    ((toℕ cin + (toℕ (μ mlo) + size * toℕ (μ mhi))) + toℕ (μ nlo)) + size * toℕ (μ nhi)                              ≡⟨ +-assoc (toℕ cin + (toℕ (μ mlo) + size * toℕ (μ mhi))) (toℕ (μ nlo)) (size * toℕ (μ nhi)) ⟩
    (toℕ cin + (toℕ (μ mlo) + size * toℕ (μ mhi))) + (toℕ (μ nlo) + size * toℕ (μ nhi))                              ≡⟨ cong₂ (λ ϕ ψ → toℕ cin + ϕ + ψ) (+-comm (toℕ (μ mlo)) (size * toℕ (μ mhi))) (+-comm (toℕ (μ nlo)) (size * toℕ (μ nhi))) ⟩
    toℕ cin + (size * toℕ (μ mhi) + toℕ (μ mlo)) + (size * toℕ (μ nhi) + toℕ (μ nlo))                                ≡⟨ (sym $ cong (λ φ → toℕ cin + φ + (size * toℕ (μ nhi) + toℕ (μ nlo))) (toℕ-combine (μ mhi) (μ mlo))) ⟩
    toℕ cin + toℕ (combine (μ mhi) (μ mlo)) + (size * toℕ (μ nhi) + toℕ (μ nlo))                                     ≡⟨ (sym $ cong₂ _+_ (toℕ-addF' cin (combine (μ mhi) (μ mlo))) (toℕ-combine (μ nhi) (μ nlo)))  ⟩
    toℕ (addF' cin (combine (μ mhi) (μ mlo))) + toℕ (combine (μ nhi) (μ nlo))                                        ≡⟨ sym $ toℕ-addF' (addF' cin (combine (μ mhi) (μ mlo))) (combine (μ nhi) (μ nlo)) ⟩
    toℕ (addF' (addF' cin (combine (μ mhi) (μ mlo))) (combine (μ nhi) (μ nlo)))
  ∎
  where open ≡-Reasoning

--------------------------------------------------------------------------------

interpret2 : Bool → Fin 2
interpret2 false = zero
interpret2 true  = suc zero

add2 : IsAdd interpret2
add add2 (zero , false , false)     = false , zero
add add2 (zero , false , true)      = true , zero
add add2 (zero , true , false)      = true , zero
add add2 (zero , true , true)       = false , suc zero
add add2 (suc zero , false , false) = true , zero
add add2 (suc zero , false , true)  = false , suc zero
add add2 (suc zero , true , false)  = false , suc zero
add add2 (suc zero , true , true)   = true , suc zero
zeroA add2 = false
proof-add add2 (zero , false , false) = refl
proof-add add2 (zero , false , true)  = refl
proof-add add2 (zero , true  , false) = refl
proof-add add2 (zero , true  , true)  = refl
proof-add add2 (suc zero , false , false) = refl
proof-add add2 (suc zero , false , true)  = refl
proof-add add2 (suc zero , true  , false) = refl
proof-add add2 (suc zero , true  , true)  = refl

mul2 : IsMult interpret2
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

add3 : IsAdd interpret3
add add3 (zero , zero , zero) = zero , zero
add add3 (zero , zero , one) = one , zero
add add3 (zero , zero , two) =  two , zero
add add3 (zero , one , zero) = one , zero
add add3 (zero , one , one) = two , zero
add add3 (zero , one , two) = zero , suc zero
add add3 (zero , two , zero) = two , zero
add add3 (zero , two , one) = zero , suc zero
add add3 (zero , two , two) = one , suc zero
add add3 (suc zero , zero , zero) = one , zero
add add3 (suc zero , one , zero) = two , zero
add add3 (suc zero , two , zero) = zero , suc zero
add add3 (suc zero , zero , one) = two , zero
add add3 (suc zero , one , one) = zero , suc zero
add add3 (suc zero , two , one) = one , suc zero
add add3 (suc zero , zero , two) = zero , suc zero
add add3 (suc zero , one , two) = one , suc zero
add add3 (suc zero , two , two) = two , suc zero
zeroA add3 = zero
proof-add add3 (zero , zero , zero) = refl
proof-add add3 (zero , zero , one) = refl
proof-add add3 (zero , zero , two) = refl
proof-add add3 (zero , one , zero) = refl
proof-add add3 (zero , one , one) = refl
proof-add add3 (zero , one , two) = refl
proof-add add3 (zero , two , zero) = refl
proof-add add3 (zero , two , one) = refl
proof-add add3 (zero , two , two) = refl
proof-add add3 (suc zero , zero , zero) = refl
proof-add add3 (suc zero , one , zero) = refl
proof-add add3 (suc zero , two , zero) = refl
proof-add add3 (suc zero , zero , one) = refl
proof-add add3 (suc zero , one , one) = refl
proof-add add3 (suc zero , two , one) = refl
proof-add add3 (suc zero , zero , two) = refl
proof-add add3 (suc zero , one , two) = refl
proof-add add3 (suc zero , two , two) = refl

mul3 : IsMult interpret3
mult mul3 zero zero = zero , zero
mult mul3 zero one = zero , zero
mult mul3 zero two = zero , zero
mult mul3 one zero = zero , zero
mult mul3 one one = zero , one
mult mul3 one two = zero , two
mult mul3 two zero = zero , zero
mult mul3 two one = zero , two
mult mul3 two two = one , one
zeroM mul3 = zero
proof-mult mul3 zero zero = refl
proof-mult mul3 zero one = refl
proof-mult mul3 zero two = refl
proof-mult mul3 one zero = refl
proof-mult mul3 one one = refl
proof-mult mul3 one two = refl
proof-mult mul3 two zero = refl
proof-mult mul3 two one = refl
proof-mult mul3 two two = refl

--------------------------------------------------------------------------------

add2x2 : IsAdd (pairμ interpret2)
add2x2 = bigger-adder add2 add2

mul2x2 : _
mul2x2 = compose add2 add2x2 mul2

add2x2x2x2 : IsAdd (pairμ (pairμ interpret2))
add2x2x2x2 = bigger-adder add2x2 add2x2

mul2x2x2x2 : _
mul2x2x2x2 = compose add2x2 add2x2x2x2 mul2x2

add3x3 : IsAdd (pairμ interpret3)
add3x3 = bigger-adder add3 add3

mul3x3 : IsMult (pairμ interpret3)
mul3x3 = compose add3 add3x3 mul3

--------------------------------------------------------------------------------

allBools : Vec Bool 2
allBools = false ∷ true ∷ []

allThrees : Vec Three 3
allThrees = zero ∷ one ∷ two ∷ []

composeTheValues : {A B : Set} {m n : ℕ} → Vec A m → Vec B n → Vec (A × B) (m * n)
composeTheValues as bs = concat $ V.map (λ a → V.map (a ,_) bs) as

--------------------------------------------------------------------------------

allBools2x2 : Vec (Bool × Bool) 4
allBools2x2 = composeTheValues allBools allBools

allThrees3x3 : Vec (Three × Three) 9
allThrees3x3 = composeTheValues allThrees allThrees

allBools2x2x2x2 : Vec ((Bool × Bool) × (Bool × Bool)) 16
allBools2x2x2x2 = composeTheValues allBools2x2 allBools2x2

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
