{-# OPTIONS --allow-unsolved-metas #-}

module Mul where

open import Function.Base
open import Data.Bool.Base hiding (_<_; _≤_)
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Nat.Solver
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
      → toℕ (uncurry combine (P.map μ μ (mult m n)))
      ≡ toℕ (mulF' (μ m) (μ n))
open IsMult

--------------------------------------------------------------------------------

-- this exists in the future
postulate toℕ-combine : ∀ {m n} (i : Fin m) (j : Fin n) → toℕ (combine i j) ≡ n * toℕ i + toℕ j

--------------------------------------------------------------------------------

pairμ : {τ : Set} → {size : ℕ} → (τ → Fin size) → (τ × τ → Fin (size * size))
pairμ μ = uncurry combine ∘ P.map μ μ

module _ {τ : Set} {size : ℕ} {μ : τ → Fin size} where
  add3Adder' : IsAdd (pairμ μ) → Fin 2 → τ → τ → τ → (τ × τ)
  add3Adder' (adds add z _) cin a b c =
    let (ab  , cout1)  = add (cin , (proj₂ z , a) , (proj₂ z , b))
        (abc , cout2)  = add (zero , ab , (proj₂ z , c))
     in abc

  add3Adder'-proof
    : (adder : IsAdd (pairμ μ))
    → (cin : Fin 2)
    → (m n o : τ)
    → toℕ (uncurry combine (P.map μ μ (add3Adder' adder cin m n o))) ≡ toℕ cin + toℕ (μ m) + toℕ (μ n) + toℕ (μ o)
  add3Adder'-proof = ?

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
IsMult.proof-mult (compose {τ} {size} {μ} small adder multipler) ab@(a , b) cd@(c , d)
                      with multipler .mult a c in ac-eq
... | (k0 , l)        with multipler .mult a d in ad-eq
... | (g , h)         with multipler .mult b d in bd-eq
... | (e , f)         with multipler .mult b c in bc-eq
... | (i , j)         with add3Adder' {τ = τ} {size} {μ} adder zero e h j in add-ehj-eq
... | (ehjhi , ehj)   with add3Adder' {τ = τ} {size} {μ} adder zero l i g in add-lig-eq
... | (lighi , liglo) with small .add (zero  , ehjhi , liglo) in add-ehj-lig
... | (lig , carry)   with small .add (carry , k0    , lighi) in add-k0-lig
... | (k , _) = let
                    ac-proof = multipler .proof-mult a c
                    ad-proof = multipler .proof-mult a d
                    bd-proof = multipler .proof-mult b d
                    bc-proof = multipler .proof-mult b c
                    egjhi-liglo-proof = small .proof-add  (zero  , ehjhi , liglo)
                    k0-lighi-proof    = small .proof-add  (carry  , k0 , lighi)
                    add3-1-proof = add3Adder'-proof {τ = τ} {size} {μ} adder zero e h j
                    add3-2-proof = add3Adder'-proof {τ = τ} {size} {μ} adder zero l i g
                    ℕμ = toℕ ∘ μ
                    μ' = curry $ pairμ μ
                    ℕμ' = λ x y → toℕ (μ' x y)
                 in

  begin
    toℕ (combine (μ' k lig) (μ' ehj f))
  ≡⟨ toℕ-combine (μ' k lig) (μ' ehj f) ⟩
    size * size * ℕμ' k lig + ℕμ' ehj f
  ≡⟨ cong (\ φ → size * size * φ + ℕμ' ehj f) $ toℕ-combine (μ k) (μ lig) ⟩
    size * size * (size * ℕμ k + ℕμ lig) + ℕμ' ehj f
  ≡⟨ cong (\ φ → size * size * (size * ℕμ k + ℕμ lig) + φ) $ toℕ-combine (μ ehj) (μ f) ⟩
    size * size * (size * ℕμ k + ℕμ lig) + (size * ℕμ ehj + ℕμ f)
  ≡⟨ ? ⟩
    size * size * toℕ (combine (μ k0) (μ l)) + size * toℕ (combine (μ g) (μ h)) + size * toℕ (combine (μ i) (μ j)) + toℕ (combine (μ e) (μ f))
  ≡⟨⟩
    size * size * ℕμ' k0 l + size * ℕμ' g h + size * ℕμ' i j + ℕμ' e f
  ≡⟨ cong (\ φ → size * size * ℕμ' k0 l + size * ℕμ' g h + size * ℕμ' i j + toℕ (uncurry combine (P.map μ μ φ))) $ sym bd-eq ⟩
    size * size * ℕμ' k0 l + size * ℕμ' g h + size * ℕμ' i j + toℕ (uncurry combine (P.map μ μ (mult multipler b d)))
  ≡⟨ cong (\ φ → size * size * ℕμ' k0 l + size * ℕμ' g h + size * ℕμ' i j + φ) $ trans bd-proof $ toℕ-mulF' (μ b) (μ d) ⟩
    size * size * ℕμ' k0 l + size * ℕμ' g h + size * ℕμ' i j + ℕμ b * ℕμ d
  ≡⟨ cong (\ φ → size * size * ℕμ' k0 l + size * ℕμ' g h + size * toℕ (uncurry combine (P.map μ μ φ)) + ℕμ b * ℕμ d) $ sym bc-eq ⟩
    size * size * ℕμ' k0 l + size * ℕμ' g h + size * toℕ (uncurry combine (P.map μ μ (mult multipler b c))) + ℕμ b * ℕμ d
  ≡⟨ cong (\ φ → size * size * ℕμ' k0 l + size * ℕμ' g h + size * φ + ℕμ b * ℕμ d) $ trans bc-proof $ toℕ-mulF' (μ b) (μ c) ⟩
    size * size * ℕμ' k0 l + size * ℕμ' g h + size * (ℕμ b * ℕμ c) + ℕμ b * ℕμ d
  ≡⟨ cong (\ φ → size * size * ℕμ' k0 l + size * toℕ (uncurry combine (P.map μ μ φ)) + size * (ℕμ b * ℕμ c) + ℕμ b * ℕμ d) $ sym ad-eq ⟩
    size * size * ℕμ' k0 l + size * toℕ (uncurry combine (P.map μ μ (mult multipler a d))) + size * (ℕμ b * ℕμ c) + ℕμ b * ℕμ d
  ≡⟨ cong (\ φ → size * size * ℕμ' k0 l + size * φ + size * (ℕμ b * ℕμ c) + ℕμ b * ℕμ d) $ trans ad-proof $ toℕ-mulF' (μ a) (μ d) ⟩
    size * size * ℕμ' k0 l + size * (ℕμ a * ℕμ d) + size * (ℕμ b * ℕμ c) + ℕμ b * ℕμ d
  ≡⟨ cong (\ φ → (size * size * toℕ (uncurry combine (P.map μ μ φ))) + (size * (ℕμ a * ℕμ d)) + (size * (ℕμ b * ℕμ c)) + (ℕμ b * ℕμ d)) $ sym ac-eq ⟩
    (size * size * toℕ (uncurry combine (P.map μ μ (mult multipler a c)))) + (size * (ℕμ a * ℕμ d)) + (size * (ℕμ b * ℕμ c)) + (ℕμ b * ℕμ d)
  ≡⟨ cong (\ φ → (size * size * φ) + (size * (ℕμ a * ℕμ d)) + (size * (ℕμ b * ℕμ c)) + (ℕμ b * ℕμ d)) ac-proof ⟩
    (size * size * toℕ (mulF' (μ a) (μ c))) + (size * (ℕμ a * ℕμ d)) + (size * (ℕμ b * ℕμ c)) + (ℕμ b * ℕμ d)
  ≡⟨ cong (\ φ → (size * size * φ) + (size * (ℕμ a * ℕμ d)) + (size * (ℕμ b * ℕμ c)) + (ℕμ b * ℕμ d)) $ toℕ-mulF' (μ a) (μ c) ⟩
    (size * size * (ℕμ a * ℕμ c)) + (size * (ℕμ a * ℕμ d)) + (size * (ℕμ b * ℕμ c)) + (ℕμ b * ℕμ d)
  ≡⟨ {! ring solve me !} ⟩
    (size * ℕμ a + ℕμ b) * (size * ℕμ c + ℕμ d)
  ≡⟨ sym $ cong₂ _*_ (toℕ-combine (μ a) (μ b)) (toℕ-combine (μ c) (μ d)) ⟩
    ℕμ' a b * ℕμ' c d
  ≡⟨ sym $ toℕ-mulF' (μ' a b) _ ⟩
    toℕ (mulF' (μ' a b) (μ' c d))
  ∎
  where
    open ≡-Reasoning
    open +-*-Solver

--------------------------------------------------------------------------------


bigger-adder : {σ τ : Set} {σ-size τ-size : ℕ} {μ : σ → Fin σ-size} {ν : τ → Fin τ-size} → IsAdd μ → IsAdd ν → IsAdd (uncurry combine ∘ P.map μ ν)
add (bigger-adder x y) (cin , (mhi , mlo) , (nhi , nlo)) =
  let (lo , cmid) = y .add (cin  , mlo , nlo)
      (hi , cout) = x .add (cmid , mhi , nhi)
  in ((hi , lo) , cout)
zeroA (bigger-adder x y) = x .zeroA , y .zeroA
proof-add (bigger-adder {σ-size = σ-size} {τ-size = τ-size} {μ = μ} {ν = ν} x y)  (cin , (mhi , mlo) , (nhi , nlo))
  with y .add (cin , mlo , nlo) in y-eq
... | (lo , cmid) with x .add (cmid , mhi , nhi) in x-eq
... | (hi , cout) =
  let x-proof = proof-add x (cmid , mhi , nhi)
      y-proof = proof-add y (cin  , mlo , nlo)
      size = σ-size
  in begin
    toℕ (cast _ (combine cout (combine (μ hi) (ν lo))))                                                     ≡⟨ toℕ-cast _ (combine cout (combine (μ hi) (ν lo))) ⟩
    toℕ (combine cout (combine (μ hi) (ν lo)))                                                              ≡⟨ toℕ-combine cout (combine (μ hi) (ν lo)) ⟩
    σ-size * τ-size * toℕ cout + toℕ (combine (μ hi) (ν lo))                                                ≡⟨ cong (σ-size * τ-size * toℕ cout +_) (toℕ-combine (μ hi) (ν lo)) ⟩
    σ-size * τ-size * toℕ cout + (τ-size * toℕ (μ hi) + toℕ (ν lo))                                         ≡⟨ lemma₁ σ-size τ-size (toℕ cout) (toℕ (μ hi)) (toℕ (ν lo)) ⟩ -- boring algebra
    τ-size * (σ-size * toℕ cout + toℕ (μ hi)) + toℕ (ν lo)                                                  ≡˘⟨ cong (λ ϕ → τ-size * ϕ + toℕ (ν lo)) (toℕ-combine cout (μ hi)) ⟩
    τ-size * toℕ (combine cout (μ hi)) + toℕ (ν lo)                                                         ≡⟨⟩
    τ-size * toℕ (uncurry combine (map₂ μ (swap (hi , cout)))) + toℕ (ν lo)                                 ≡˘⟨ cong (λ ϕ → τ-size * toℕ (uncurry combine (map₂ μ (swap ϕ))) + toℕ (ν lo)) x-eq ⟩
    τ-size * toℕ (uncurry combine (map₂ μ (swap (x .add (cmid , mhi , nhi))))) + toℕ (ν lo)                 ≡˘⟨ cong (λ ϕ → τ-size * ϕ + toℕ (ν lo)) (toℕ-cast _ (uncurry combine (map₂ μ (swap (x .add (cmid , mhi , nhi)))))) ⟩
    τ-size * toℕ (digitize (map₁ μ (x .add (cmid , mhi , nhi)))) + toℕ (ν lo)                               ≡⟨ cong (λ ϕ → τ-size * ϕ + toℕ (ν lo)) x-proof ⟩
    τ-size * toℕ (addF' (addF' cmid (μ mhi)) (μ nhi)) + toℕ (ν lo)                                          ≡⟨ cong (λ ϕ → τ-size * ϕ + toℕ (ν lo)) (toℕ-addF' (addF' cmid (μ mhi)) (μ nhi)) ⟩
    τ-size * (toℕ (addF' cmid (μ mhi)) + toℕ (μ nhi)) + toℕ (ν lo)                                          ≡⟨ cong (λ ϕ → τ-size * (ϕ + toℕ (μ nhi)) + toℕ (ν lo)) (toℕ-addF' cmid (μ mhi)) ⟩
    τ-size * (toℕ cmid + toℕ (μ mhi) + toℕ (μ nhi)) + toℕ (ν lo)                                            ≡⟨ lemma₂ τ-size (toℕ cmid) (toℕ (μ mhi)) (toℕ (μ nhi)) (toℕ (ν lo)) ⟩ -- boring algebra
    (τ-size * toℕ cmid + toℕ (ν lo)) + τ-size * (toℕ (μ mhi) + toℕ (μ nhi))                                 ≡˘⟨ cong (_+ τ-size * (toℕ (μ mhi) + toℕ (μ nhi))) (toℕ-combine cmid (ν lo)) ⟩
    toℕ (combine cmid (ν lo)) + τ-size * (toℕ (μ mhi) + toℕ (μ nhi))                                        ≡⟨⟩
    toℕ (uncurry combine (map₂ ν (swap (lo , cmid)))) + τ-size * (toℕ (μ mhi) + toℕ (μ nhi))                ≡˘⟨ cong (λ ϕ → toℕ (uncurry combine (map₂ ν (swap ϕ))) + τ-size * (toℕ (μ mhi) + toℕ (μ nhi))) y-eq ⟩
    toℕ (uncurry combine (map₂ ν (swap (y .add (cin , mlo , nlo))))) + τ-size * (toℕ (μ mhi) + toℕ (μ nhi)) ≡˘⟨ cong (_+ τ-size * (toℕ (μ mhi) + toℕ (μ nhi))) (toℕ-cast _ (uncurry combine (map₂ ν (swap (y .add (cin , mlo , nlo)))))) ⟩
    toℕ (digitize (map₁ ν (y .add (cin , mlo , nlo)))) + τ-size * (toℕ (μ mhi) + toℕ (μ nhi))               ≡⟨ cong (_+ τ-size * (toℕ (μ mhi) + toℕ (μ nhi))) y-proof ⟩
    toℕ (addF' (addF' cin (ν mlo)) (ν nlo)) + τ-size * (toℕ (μ mhi) + toℕ (μ nhi))                          ≡⟨ cong (_+ τ-size * (toℕ (μ mhi) + toℕ (μ nhi))) (toℕ-addF' (addF' cin (ν mlo)) (ν nlo)) ⟩
    toℕ (addF' cin (ν mlo)) + toℕ (ν nlo) + τ-size * (toℕ (μ mhi) + toℕ (μ nhi))                            ≡⟨ cong (λ ϕ → ϕ + toℕ (ν nlo) + τ-size * (toℕ (μ mhi) + toℕ (μ nhi))) (toℕ-addF' cin (ν mlo)) ⟩
    toℕ cin + toℕ (ν mlo) + toℕ (ν nlo) + τ-size * (toℕ (μ mhi) + toℕ (μ nhi))                              ≡⟨ lemma₃ (toℕ cin) (toℕ (ν mlo)) (toℕ (ν nlo)) τ-size (toℕ (μ mhi)) (toℕ (μ nhi)) ⟩ -- boring algebra
    toℕ cin + (τ-size * toℕ (μ mhi) + toℕ (ν mlo)) + (τ-size * toℕ (μ nhi) + toℕ (ν nlo))                   ≡˘⟨ cong₂ (λ ϕ ψ → toℕ cin + ϕ + ψ) (toℕ-combine (μ mhi) (ν mlo)) (toℕ-combine (μ nhi) (ν nlo)) ⟩
    toℕ cin + toℕ (combine (μ mhi) (ν mlo)) + toℕ (combine (μ nhi) (ν nlo))                                 ≡˘⟨ cong (_+ toℕ (combine (μ nhi) (ν nlo))) (toℕ-addF' cin (combine (μ mhi) (ν mlo))) ⟩
    toℕ (addF' cin (combine (μ mhi) (ν mlo))) + toℕ (combine (μ nhi) (ν nlo))                               ≡˘⟨ toℕ-addF' (addF' cin (combine (μ mhi) (ν mlo))) (combine (μ nhi) (ν nlo)) ⟩
    toℕ (addF' (addF' cin (combine (μ mhi) (ν mlo))) (combine (μ nhi) (ν nlo)))                             ∎
  where
    open ≡-Reasoning
    open +-*-Solver
    lemma₁ : ∀ a b c d e → a * b * c + (b * d + e) ≡ b * (a * c + d) + e
    lemma₁ = solve 5 (λ a b c d e → a :* b :* c :+ (b :* d :+ e) := (b :* (a :* c :+ d) :+ e)) refl

    lemma₂ : ∀ a b c d e → a * (b + c + d) + e ≡ (a * b + e) + a * (c + d)
    lemma₂ = solve 5 (λ a b c d e → a :* (b :+ c :+ d) :+ e := (a :* b :+ e) :+ a :* (c :+ d)) refl

    lemma₃ : ∀ a b c d e f → a + b + c + d * (e + f) ≡ a + (d * e + b) + (d * f + c)
    lemma₃ = solve 6 (λ a b c d e f → a :+ b :+ c :+ d :* (e :+ f) := a :+ (d :* e :+ b) :+ (d :* f :+ c)) refl

