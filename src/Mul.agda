{-# OPTIONS --allow-unsolved-metas #-}

module Mul where

open import Agda.Builtin.Unit
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

-- Adder interpretUnit interpretUnit gives a crude binary adder.
-- Adder interpretUnit x doubles the size of x
interpretUnit : ⊤ → Fin 1
interpretUnit _ = zero



-- absorb an interpretation into the adder to create a bigger one
bigger-adder : {τ ρ υ : Set} {τ-size ρ-size υ-size : ℕ} {μ : τ → Fin τ-size}
    {ν : ρ → Fin ρ-size} {ξ : υ → Fin υ-size}
    → Adder μ ν → Adder μ ξ → Adder μ (F.join ρ-size υ-size ∘ S.map ν ξ)
add (bigger-adder x y ) (τ , inj₁ ρ) = S.map₂ inj₁ $ x .add $ τ , ρ
add (bigger-adder x y ) (τ , inj₂ ξ) = S.map₂ inj₂ $ y .add $ τ , ξ
proof-add (bigger-adder {τ-size = τ-size} {ρ-size = ρ-size} {υ-size = υ-size}
    {μ = μ} {ν = ν} {ξ = ξ} x y)  (τ , inj₁ ρ) =
  begin
    toℕ
    (join τ-size (ρ-size + υ-size)
    (map μ (join ρ-size υ-size ∘ map ν ξ)
        (add (bigger-adder x y) (τ , inj₁ ρ))))
  ≡⟨⟩
    toℕ (uncurry addF' ((P.map (suc ∘ μ) (F.join ρ-size υ-size ∘ S.map ν ξ)) (τ , inj₁ ρ)))
  ∎
  where
    open ≡-Reasoning
    mnp = (τ , ρ)
proof-add (bigger-adder {τ-size = τ-size} {ρ-size = ρ-size} {υ-size = υ-size}
    {μ = μ} {ν = ν} {ξ = ξ} x y)  (τ , inj₂ ρ) =
  begin
    toℕ
    (join τ-size (ρ-size + υ-size)
    (map μ (join ρ-size υ-size ∘ map ν ξ)
        (add (bigger-adder x y) (τ , inj₂ ρ))))
  -- ≡⟨ x .proof-add (τ , ρ) ⟩
  ≡⟨⟩
    toℕ (uncurry addF' ((P.map (suc ∘ μ) (F.join ρ-size υ-size ∘ S.map ν ξ)) (τ , inj₂ ρ)))
  ∎
  where
    open ≡-Reasoning

    mnp = (τ , ρ)

-- ??? wtf
-- commute-adder : Adder μ ν →  Adder ν μ
-- commute-adder = <?>
-- why is this bad?
-- do we still have low and high bits?
