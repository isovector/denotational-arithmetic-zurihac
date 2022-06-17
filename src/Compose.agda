module Compose where

open import Function.Base
open import Data.Bool.Base hiding (_<_; _≤_)
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Nat.Solver
open import Data.Vec hiding (map)
import Data.Vec as V
open import Data.Product as P hiding (map)
open import Data.Fin.Base as F hiding (_+_; _<_; _≤_)
open import Data.Fin.Properties
open import Relation.Binary.PropositionalEquality
open import Mul
open import Tactic.Cong using (cong!)

open IsAdd
open IsMult

compose
    : {τ : Set} {size : ℕ} {μ : τ → Fin size}
    → IsAdd μ
    → IsAdd (pairμ μ)
    → IsMult μ
    → IsMult {τ × τ} {size * size} (pairμ μ)
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
proof-mult (compose {τ} {size} {μ} small adder@(adds addx _ _) multipler) (a , b) (c , d)
                      with multipler .mult a c in -ac-eq
... | (k0 , l)        with multipler .mult a d in -ad-eq
... | (g , h)         with multipler .mult b d in -bd-eq
... | (e , f)         with multipler .mult b c in -bc-eq
... | (i , j)         with add3Adder' {τ = τ} {size} {μ} adder zero e h j in add-ehj-eq
... | (ehjhi , ehj)   with add3Adder' {τ = τ} {size} {μ} adder zero l i g in add-lig-eq
... | (lighi , liglo) with small .add (zero  , ehjhi , liglo) in add-ehj-lig
... | (lig , carry)   with small .add (carry , k0    , lighi) in add-k0-lig
... | (k , _) = let
                    -ac-proof = multipler .proof-mult a c
                    -ad-proof = multipler .proof-mult a d
                    -bd-proof = multipler .proof-mult b d
                    -bc-proof = multipler .proof-mult b c
                    egjhi-liglo-proof = small .proof-add  (zero  , ehjhi , liglo)
                    k0-lighi-proof    = small .proof-add  (carry  , k0 , lighi)
                    add3-1-proof = add3Adder'-proof {τ = τ} {size} {μ} adder zero e h j
                    add3-2-proof = add3Adder'-proof {τ = τ} {size} {μ} adder zero l i g
                    ℕμ = toℕ ∘ μ
                    μ' = curry $ pairμ μ
                    ℕμ' = λ x y → toℕ (μ' x y)
                    added-lig = add3Adder' {τ = τ} {size} {μ} adder zero l i g
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
    {- next need to use add-lig-eq, but not sure how to massage everything -}
    size * size * (size * toℕ (μ k0)) + size * size * toℕ (uncurry combine (P.map μ μ (add3Adder' {τ = τ} {size} {μ} adder zero l i g))) + size * (toℕ (zero {2}) + toℕ (μ e) + toℕ (μ h) + toℕ (μ j)) + toℕ (μ f)
  ≡⟨⟩
    size * size * (size * toℕ (μ k0)) + size * size * toℕ (uncurry combine (P.map μ μ added-lig)) + size * (toℕ (zero {2}) + toℕ (μ e) + toℕ (μ h) + toℕ (μ j)) + toℕ (μ f)
  ≡⟨ cong!  add3-2-proof ⟩
    (size * size * (size * toℕ (μ k0))) + (size * size * (toℕ (zero {2}) + toℕ (μ l) + toℕ (μ i) + toℕ (μ g))) + (size * (toℕ (zero {2}) + toℕ (μ e) + toℕ (μ h) + toℕ (μ j))) + (toℕ (μ f)) ≡⟨⟩
    (size * size * (size * toℕ (μ k0))) + (size * size * (toℕ (μ l) + toℕ (μ i) + toℕ (μ g))) + (size * (toℕ (μ e) + toℕ (μ h) + toℕ (μ j))) + (toℕ (μ f))               ≡⟨ lemma₂ size (ℕμ k0) (ℕμ l) (ℕμ i) (ℕμ g) (ℕμ e) (ℕμ h) (ℕμ j) (ℕμ f) ⟩
    (size * size * (size * toℕ (μ k0) + toℕ (μ l))) + (size * (size * toℕ (μ g) + toℕ (μ h))) + (size * (size * toℕ (μ i) + toℕ (μ j))) + (size * toℕ (μ e) + toℕ (μ f)) ≡⟨ cong! (sym $ toℕ-combine (μ e) (μ f)) ⟩
    size * size * (size * toℕ (μ k0) + toℕ (μ l)) + size * (size * toℕ (μ g) + toℕ (μ h)) + size * (size * toℕ (μ i) + toℕ (μ j)) + toℕ (combine (μ e) (μ f))            ≡⟨ cong! (sym $ toℕ-combine (μ i) (μ j)) ⟩
    size * size * (size * toℕ (μ k0) + toℕ (μ l)) + size * (size * toℕ (μ g) + toℕ (μ h)) + size * toℕ (combine (μ i) (μ j)) + toℕ (combine (μ e) (μ f))                 ≡⟨ cong! (sym $ toℕ-combine (μ g) (μ h)) ⟩
    size * size * (size * toℕ (μ k0) + toℕ (μ l)) + size * toℕ (combine (μ g) (μ h)) + size * toℕ (combine (μ i) (μ j)) + toℕ (combine (μ e) (μ f))                      ≡⟨ cong (\ φ → size * size * φ + size * toℕ (combine (μ g) (μ h)) + size * toℕ (combine (μ i) (μ j)) + toℕ (combine (μ e) (μ f))) $ sym $ toℕ-combine (μ k0) (μ l) ⟩
    size * size * toℕ (combine (μ k0) (μ l)) + size * toℕ (combine (μ g) (μ h)) + size * toℕ (combine (μ i) (μ j)) + toℕ (combine (μ e) (μ f))                           ≡⟨⟩
    size * size * ℕμ' k0 l + size * ℕμ' g h + size * ℕμ' i j + ℕμ' e f                                                                                                   ≡⟨ cong (\ φ → size * size * ℕμ' k0 l + size * ℕμ' g h + size * ℕμ' i j + toℕ (uncurry combine (P.map μ μ φ))) $ sym -bd-eq ⟩
    size * size * ℕμ' k0 l + size * ℕμ' g h + size * ℕμ' i j + toℕ (uncurry combine (P.map μ μ (mult multipler b d)))                                                    ≡⟨ cong! (trans -bd-proof $ toℕ-mulF' (μ b) (μ d)) ⟩
    size * size * ℕμ' k0 l + size * ℕμ' g h + size * ℕμ' i j + ℕμ b * ℕμ d                                                                                               ≡⟨ cong (\ φ → size * size * ℕμ' k0 l + size * ℕμ' g h + size * toℕ (uncurry combine (P.map μ μ φ)) + ℕμ b * ℕμ d) $ sym -bc-eq ⟩
    size * size * ℕμ' k0 l + size * ℕμ' g h + size * toℕ (uncurry combine (P.map μ μ (mult multipler b c))) + ℕμ b * ℕμ d                                                ≡⟨ cong! (trans -bc-proof $ toℕ-mulF' (μ b) (μ c)) ⟩
    size * size * ℕμ' k0 l + size * ℕμ' g h + size * (ℕμ b * ℕμ c) + ℕμ b * ℕμ d                                                                                         ≡⟨ cong (\ φ → size * size * ℕμ' k0 l + size * toℕ (uncurry combine (P.map μ μ φ)) + size * (ℕμ b * ℕμ c) + ℕμ b * ℕμ d) $ sym -ad-eq ⟩
    size * size * ℕμ' k0 l + size * toℕ (uncurry combine (P.map μ μ (mult multipler a d))) + size * (ℕμ b * ℕμ c) + ℕμ b * ℕμ d                                          ≡⟨ cong! (trans -ad-proof $ toℕ-mulF' (μ a) (μ d)) ⟩
    size * size * ℕμ' k0 l + size * (ℕμ a * ℕμ d) + size * (ℕμ b * ℕμ c) + ℕμ b * ℕμ d                                                                                   ≡⟨ cong (\ φ → (size * size * toℕ (uncurry combine (P.map μ μ φ))) + (size * (ℕμ a * ℕμ d)) + (size * (ℕμ b * ℕμ c)) + (ℕμ b * ℕμ d)) $ sym -ac-eq ⟩
    (size * size * toℕ (uncurry combine (P.map μ μ (mult multipler a c)))) + (size * (ℕμ a * ℕμ d)) + (size * (ℕμ b * ℕμ c)) + (ℕμ b * ℕμ d)                             ≡⟨ cong! -ac-proof ⟩
    (size * size * toℕ (mulF' (μ a) (μ c))) + (size * (ℕμ a * ℕμ d)) + (size * (ℕμ b * ℕμ c)) + (ℕμ b * ℕμ d)                                                            ≡⟨ cong! (toℕ-mulF' (μ a) (μ c)) ⟩
    (size * size * (ℕμ a * ℕμ c)) + (size * (ℕμ a * ℕμ d)) + (size * (ℕμ b * ℕμ c)) + (ℕμ b * ℕμ d)                                                                      ≡⟨ lemma₁ size size (ℕμ a) (ℕμ b) (ℕμ c) (ℕμ d) ⟩
    (size * ℕμ a + ℕμ b) * (size * ℕμ c + ℕμ d)                                                                                                                          ≡⟨ sym $ cong₂ _*_ (toℕ-combine (μ a) (μ b)) (toℕ-combine (μ c) (μ d)) ⟩
    ℕμ' a b * ℕμ' c d                                                                                                                                                    ≡⟨ sym $ toℕ-mulF' (μ' a b) _ ⟩
    toℕ (mulF' (μ' a b) (μ' c d))
    ∎
  where
    open ≡-Reasoning
    open +-*-Solver

    lemma₁ : (x1 x2 a b c d : ℕ) → (x1 * x2 * (a * c)) + (x1 * (a * d)) + (x2 * (b * c)) + (b * d) ≡ (x1 * a + b) * (x2 * c + d)
    lemma₁ = solve 6 (λ x1 x2 a b c d → (x1 :* x2 :* (a :* c)) :+ (x1 :* (a :* d)) :+ (x2 :* (b :* c)) :+ (b :* d) := (x1 :* a :+ b) :* (x2 :* c :+ d)) refl

    lemma₂ : (x k0 l i g e h j f : ℕ) → (x * x * (x * k0)) + (x * x * (l + i + g)) + (x * (e + h + j)) + f ≡ ((x * x * (x * k0 + l)) + (x * (x * g + h)) + (x * (x * i + j)) + (x * e + f))
    lemma₂ = solve 9 (λ x k0 l i g e h j f → (x :* x :* (x :* k0)) :+ (x :* x :* (l :+ i :+ g)) :+ (x :* (e :+ h :+ j)) :+ f := ((x :* x :* (x :* k0 :+ l)) :+ (x :* (x :* g :+ h)) :+ (x :* (x :* i :+ j)) :+ (x :* e :+ f))) refl

