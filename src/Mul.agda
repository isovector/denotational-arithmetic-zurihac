{-# OPTIONS --allow-unsolved-metas #-}

module Mul where

open import Function.Base
open import Data.Bool.Base hiding (_<_; _≤_)
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Nat.Solver
open import Data.Vec hiding (map)
open import Data.Sum as S hiding (swap)
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

toℕ-suc : ∀ {m} (x : Fin m) → toℕ (suc x) ≡ suc (toℕ x)
toℕ-suc zero = refl
toℕ-suc (suc x) rewrite toℕ-suc x = refl

toℕ-mulF' : ∀ {m n} (x : Fin m) (y : Fin n) → toℕ (mulF' x y) ≡ toℕ x * toℕ y
toℕ-mulF' zero zero = refl
toℕ-mulF' zero (suc y) = refl
toℕ-mulF' (suc x) zero rewrite *-comm (toℕ x) 0 = refl
toℕ-mulF' (suc x) (suc y) =
  begin
    toℕ (inject₁ (addF' (suc y) (mulF' x (suc y))))
  ≡⟨ toℕ-inject₁ (addF' (suc y) (mulF' x (suc y))) ⟩
    toℕ (addF' (suc y) (mulF' x (suc y)))
  ≡⟨ toℕ-addF' (suc y) _ ⟩
    toℕ (suc y) + toℕ (mulF' x (suc y))
  ≡⟨ cong (\ φ → toℕ (suc y) + φ) $ toℕ-mulF' x (suc y) ⟩
    suc (toℕ y + toℕ x * toℕ (suc y))
  ≡⟨ cong (\ φ → suc (toℕ y + toℕ x * φ)) $ toℕ-suc y ⟩
    suc (toℕ y + toℕ x * suc (toℕ y))
  ∎
  where
    open ≡-Reasoning


addF'3 : ∀ {n p} → Fin 2 × Fin n × Fin p → Fin (n + p)
addF'3 (m , n , p) = addF' (addF' m n) p

--------------------------------------------------------------------------------

record Adder {τ ρ : Set} {sizeτ sizeρ : ℕ} (μ : τ → Fin sizeτ) (ν : ρ → Fin sizeρ) : Set where
  constructor adds
  field
    add : τ × ρ → τ ⊎ ρ
    zeroA : ρ
    proof-add
      : (mnp : τ × ρ)
      →
      let
      x : Fin sizeτ ⊎ Fin sizeρ
      x = S.map μ ν (add mnp)
      in
      toℕ (F.join sizeτ sizeρ x) ≡ toℕ (uncurry addF' ((P.map (suc ∘ μ) ν) mnp))
open Adder

--------------------------------------------------------------------------------




record Multiplier {τ : Set} {size : ℕ} (μ : τ → Fin size) : Set where
  constructor multiples
  field
    mult : τ → τ → τ × τ
    zeroM : τ
    proof-mult
      : (m n : τ)
      → toℕ (uncurry combine (P.map μ μ (mult m n)))
      ≡ toℕ (mulF' (μ m) (μ n))
open Multiplier

--------------------------------------------------------------------------------

-- this exists in the future
postulate toℕ-combine : ∀ {m n} (i : Fin m) (j : Fin n) → toℕ (combine i j) ≡ n * toℕ i + toℕ j

--------------------------------------------------------------------------------

pairμ : {τ : Set} → {size : ℕ} → (τ → Fin size) → (τ × τ → Fin (size * size))
pairμ μ = uncurry combine ∘ P.map μ μ

module _ {τ : Set} {size : ℕ} {μ : τ → Fin size} where
  add3Adder' : Adder (pairμ μ) → Fin 2 → τ → τ → τ → (τ × τ)
  add3Adder' (adds add z _) cin a b c =
    let (ab  , cout1)  = add (cin , (proj₂ z , a) , (proj₂ z , b))
        (abc , cout2)  = add (zero , ab , (proj₂ z , c))
     in abc

  add3Adder'-proof
    : (adder : Adder (pairμ μ))
    → (cin : Fin 2)
    → (m n o : τ)
    → toℕ (uncurry combine (P.map μ μ (add3Adder' adder cin m n o))) ≡ toℕ cin + toℕ (μ m) + toℕ (μ n) + toℕ (μ o)
  add3Adder'-proof = {!!}

compose
    : {τ : Set} {size : ℕ} {μ : τ → Fin size}
    → Adder μ
    → Adder (pairμ μ)
    → Multiplier μ
    → Multiplier {τ × τ} {size * size} (pairμ μ)
mult (compose {τ} {size} {μ} small adder multipler) (a , b) (c , d) =
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
zeroM (compose small adder multipler) = multipler .zeroM  , multipler .zeroM
proof-mult (compose {τ} {size} {μ} small adder multipler) ab@(a , b) cd@(c , d)

    <?>
  ∎
  where
    open ≡-Reasoning
    open +-*-Solver

--------------------------------------------------------------------------------


bigger-adder : {σ τ : Set} {σ-size τ-size : ℕ} {μ : σ → Fin σ-size} {ν : τ → Fin τ-size} → Adder μ → Adder ν → Adder (uncurry combine ∘ P.map μ ν)
add (bigger-adder x y) (cin , (mhi , mlo) , (nhi , nlo)) =
  let (lo , cmid) = y .add (cin  , mlo , nlo)
      (hi , cout) = x .add (cmid , mhi , nhi)
  in ((hi , lo) , cout)
zeroA (bigger-adder x y) = x .zeroA , y .zeroA
proof-add (bigger-adder {σ-size = σ-size} {τ-size = τ-size} {μ = μ} {ν = ν} x y)  (cin , (mhi , mlo) , (nhi , nlo))
    <?>
  where
    open ≡-Reasoning
    open +-*-Solver
    lemma₁ : ∀ a b c d e → a * b * c + (b * d + e) ≡ b * (a * c + d) + e
    lemma₁ = solve 5 (λ a b c d e → a :* b :* c :+ (b :* d :+ e) := (b :* (a :* c :+ d) :+ e)) refl

    lemma₂ : ∀ a b c d e → a * (b + c + d) + e ≡ (a * b + e) + a * (c + d)
    lemma₂ = solve 5 (λ a b c d e → a :* (b :+ c :+ d) :+ e := (a :* b :+ e) :+ a :* (c :+ d)) refl

    lemma₃ : ∀ a b c d e f → a + b + c + d * (e + f) ≡ a + (d * e + b) + (d * f + c)
    lemma₃ = solve 6 (λ a b c d e f → a :+ b :+ c :+ d :* (e :+ f) := a :+ (d :* e :+ b) :+ (d :* f :+ c)) refl

