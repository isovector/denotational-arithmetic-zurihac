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
proof-mult (compose {τ} {size} {μ} small adder multipler) (a , b) (c , d)
                      with multipler .mult a c in -ac-eq
... | (k0 , l)        with multipler .mult a d in -ad-eq
... | (g , h)         with multipler .mult b d in -bd-eq
... | (e , f)         with multipler .mult b c in -bc-eq
... | (i , j)         with add3Adder' {τ = τ} {size} {μ} adder zero e h j in -add-ehj-eq
... | (ehjhi , ehj)   with add3Adder' {τ = τ} {size} {μ} adder zero l i g in -add-lig-eq
... | (lighi , liglo) with small .add (zero  , ehjhi , liglo) in -add-ehj-lig
... | (lig , carry)   with small .add (carry , k0    , lighi) in -add-k0-lig
... | (k , -drop-carry) = let
                    -ac-proof = multipler .proof-mult a c
                    -ad-proof = multipler .proof-mult a d
                    -bd-proof = multipler .proof-mult b d
                    -bc-proof = multipler .proof-mult b c
                    -egjhi-liglo-proof = small .proof-add  (zero  , ehjhi , liglo)
                    -k0-lighi-proof    = small .proof-add  (carry  , k0 , lighi)
                    -add3-1-proof = add3Adder'-proof {τ = τ} {size} {μ} adder zero e h j
                    -add3-2-proof = add3Adder'-proof {τ = τ} {size} {μ} adder zero l i g
                    ℕμ = toℕ ∘ μ
                    μ' = curry $ pairμ μ
                    ℕμ' = λ x y → toℕ (μ' x y)
                    -added-lig = add3Adder' {τ = τ} {size} {μ} adder zero l i g
                    -added-ehj = add3Adder' {τ = τ} {size} {μ} adder zero e h j
                    x = size
                    x³ = x * x * x
                    x² = x * x
                 in

  begin
    toℕ (combine (μ' k lig) (μ' ehj f))                                                                          ≡⟨ toℕ-combine (μ' k lig) (μ' ehj f) ⟩
    x² * ℕμ' k lig + ℕμ' ehj f                                                                                   ≡⟨ cong! (toℕ-combine (μ k) (μ lig)) ⟩
    x² * (x * ℕμ k + ℕμ lig) + ℕμ' ehj f                                                                         ≡⟨ cong! (toℕ-combine (μ ehj) (μ f)) ⟩
    x² * (x * ℕμ k + ℕμ lig) + (x * ℕμ ehj + ℕμ f)                                                               ≡⟨ lemma₃ x (ℕμ k) (ℕμ lig) (ℕμ ehj) (ℕμ f) ⟩
    x³ * ℕμ k + x² * ℕμ lig + x * ℕμ ehj + ℕμ f                                                                  ≡⟨ cong (\ φ → x³ * (φ + ℕμ k) + x² * ℕμ lig + x * ℕμ ehj + ℕμ f) $ *-comm (toℕ (zero {1})) x ⟩
    x³ * (x * toℕ (zero {1}) + ℕμ k) + x² * ℕμ lig + x * ℕμ ehj + ℕμ f                                           ≡⟨ cong (\ φ → x³ * (x * toℕ φ + ℕμ k) + x² * ℕμ lig + x * ℕμ ehj + ℕμ f) $ sym drop-carry-0  ⟩
    x³ * (x * toℕ -drop-carry + ℕμ k) + x² * ℕμ lig + x * ℕμ ehj + ℕμ f                                          ≡⟨ cong! (sym $ toℕ-combine -drop-carry (μ k)) ⟩
    x³ * toℕ (combine -drop-carry (μ k)) + x² * ℕμ lig + x * ℕμ ehj + ℕμ f                                       ≡⟨ cong (\ φ → x³ * φ + x² * ℕμ lig + x * ℕμ ehj + ℕμ f) $ sym $ toℕ-cast _ (combine -drop-carry (μ k)) ⟩
    x³ * toℕ (cast _ (combine -drop-carry (μ k))) + x² * ℕμ lig + x * ℕμ ehj + ℕμ f                              ≡⟨ cong (\ φ → x³ * toℕ (digitize (P.map μ id φ)) + x² * ℕμ lig + x * ℕμ ehj + ℕμ f) $ sym -add-k0-lig ⟩
    x³ * toℕ (digitize (P.map μ id (add small (carry , k0 , lighi))))
      + x² * ℕμ lig
      + x * ℕμ ehj
      + ℕμ f                                                                                                     ≡⟨ cong (\ φ → x³ * φ + x² * (ℕμ lig) + x * ℕμ ehj + ℕμ f) -k0-lighi-proof ⟩
    x³ * toℕ (addF'3 (carry , μ k0 , μ lighi)) + x² * (ℕμ lig) + x * ℕμ ehj + ℕμ f                               ≡⟨⟩
    x³ * toℕ (addF' (addF' carry (μ k0)) (μ lighi)) + x² * (ℕμ lig) + x * ℕμ ehj + ℕμ f                          ≡⟨ cong! (toℕ-addF' (addF' carry (μ k0)) (μ lighi)) ⟩
    x³ * (toℕ (addF' carry (μ k0)) + ℕμ lighi) + x² * (ℕμ lig) + x * ℕμ ehj + ℕμ f                               ≡⟨ cong! (toℕ-addF' carry (μ k0)) ⟩
    x³ * (toℕ carry + ℕμ k0 + ℕμ lighi) + x² * (ℕμ lig) + x * ℕμ ehj + ℕμ f                                      ≡⟨ lemma₄ x (toℕ carry) (ℕμ k0) (ℕμ lighi) (ℕμ lig) (ℕμ ehj) (ℕμ f) ⟩
    x³ * (ℕμ k0 + ℕμ lighi) + x² * (x * toℕ (carry) + ℕμ lig) + x * ℕμ ehj + ℕμ f                                ≡⟨ cong! (sym $ toℕ-combine carry (μ lig)) ⟩
    x³ * (ℕμ k0 + ℕμ lighi) + x² * toℕ (combine carry (μ lig)) + x * ℕμ ehj + ℕμ f                               ≡⟨ cong (\ φ → x³ * (ℕμ k0 + ℕμ lighi) + x² * φ + x * ℕμ ehj + ℕμ f) $ sym $ toℕ-cast _ (combine carry (μ lig)) ⟩
    x³ * (ℕμ k0 + ℕμ lighi) + x² * toℕ (cast _ (combine carry (μ lig))) + x * ℕμ ehj + ℕμ f                      ≡⟨ cong (\ φ → x³ * (ℕμ k0 + ℕμ lighi) + x² * toℕ (digitize (P.map μ id φ)) + x * ℕμ ehj + ℕμ f) $ sym -add-ehj-lig ⟩
    x³ * (ℕμ k0 + ℕμ lighi)
      + x² * toℕ (digitize (P.map μ id (add small (zero , ehjhi , liglo))))
      + x * ℕμ ehj
      + ℕμ f                                                                                                     ≡⟨ cong (\ φ → x³ * (ℕμ k0 + ℕμ lighi) + x² * φ + x * ℕμ ehj + ℕμ f) -egjhi-liglo-proof ⟩
    x³ * (ℕμ k0 + ℕμ lighi) + x² * toℕ (addF'3 (zero {1} , μ ehjhi , μ liglo)) + x * ℕμ ehj + ℕμ f               ≡⟨⟩
    x³ * (ℕμ k0 + ℕμ lighi) + x² * toℕ (addF' (addF' (zero {1}) (μ ehjhi)) (μ liglo)) + x * ℕμ ehj + ℕμ f        ≡⟨ cong! (toℕ-addF' ((addF' (zero {1}) (μ ehjhi))) (μ liglo)) ⟩
    x³ * (ℕμ k0 + ℕμ lighi) + x² * (toℕ (addF' (zero {1}) (μ ehjhi)) + ℕμ liglo) + x * ℕμ ehj + ℕμ f             ≡⟨ cong! (toℕ-addF' (zero {1}) (μ ehjhi)) ⟩
    x³ * (ℕμ k0 + ℕμ lighi) + x² * ((toℕ (zero {1}) + ℕμ ehjhi) + ℕμ liglo) + x * ℕμ ehj + ℕμ f                  ≡⟨ lemma₅ x (ℕμ k0) (ℕμ lighi) (ℕμ ehjhi) (ℕμ liglo) (ℕμ ehj) (ℕμ f) ⟩
    x² * (x * ℕμ k0) + x² * (x * ℕμ lighi + ℕμ liglo) + x * (x * ℕμ ehjhi + ℕμ ehj) + ℕμ f                       ≡⟨ cong! (sym $ toℕ-combine (μ ehjhi) (μ ehj)) ⟩
    x² * (x * ℕμ k0) + x² * (x * ℕμ lighi + ℕμ liglo) + x * toℕ (combine (μ ehjhi) (μ ehj)) + ℕμ f               ≡⟨⟩
    x² * (x * ℕμ k0)
      + x² * (x * ℕμ lighi + ℕμ liglo)
      + x * toℕ (uncurry combine (P.map μ μ (ehjhi , ehj)))
      + ℕμ f                                                                                                     ≡⟨ cong (\ φ → x² * (x * ℕμ k0) + x² * (x * ℕμ lighi + ℕμ liglo) + x * toℕ (uncurry combine (P.map μ μ φ)) + ℕμ f) $ sym -add-ehj-eq ⟩
    x² * (x * ℕμ k0)
      + x² * (x * ℕμ lighi + ℕμ liglo)
      + x * toℕ (uncurry combine (P.map μ μ -added-ehj))
      + ℕμ f                                                                                                     ≡⟨ cong! -add3-1-proof ⟩
    x² * (x * ℕμ k0) + x² * (x * ℕμ lighi + ℕμ liglo) + x * (toℕ (zero {1}) + ℕμ e + ℕμ h + ℕμ j) + ℕμ f         ≡⟨ cong! (sym $ toℕ-combine (μ lighi) (μ liglo)) ⟩
    x² * (x * ℕμ k0)
      + x² * toℕ (combine (μ lighi) (μ liglo))
      + x * (toℕ (zero {1}) + ℕμ e + ℕμ h + ℕμ j)
      + ℕμ f                                                                                                     ≡⟨⟩
    x² * (x * ℕμ k0)
      + x² * toℕ (uncurry combine (P.map μ μ (lighi , liglo)))
      + x * (toℕ (zero {1}) + ℕμ e + ℕμ h + ℕμ j)
      + ℕμ f                                                                                                     ≡⟨ cong (\ φ → x² * (x * ℕμ k0) + x² * toℕ (uncurry combine (P.map μ μ φ)) + x * (toℕ (zero {2}) + ℕμ e + ℕμ h + ℕμ j) + ℕμ f) $ sym -add-lig-eq ⟩
    x² * (x * ℕμ k0)
      + x² * toℕ (uncurry combine (P.map μ μ (add3Adder' {τ = τ} {x} {μ} adder zero l i g)))
      + x * (toℕ (zero {1}) + ℕμ e + ℕμ h + ℕμ j)
      + ℕμ f                                                                                                     ≡⟨⟩
    x² * (x * ℕμ k0)
      + x² * toℕ (uncurry combine (P.map μ μ -added-lig))
      + x * (toℕ (zero {1}) + ℕμ e + ℕμ h + ℕμ j)
      + ℕμ f                                                                                                     ≡⟨ cong!  -add3-2-proof ⟩
    x² * (x * ℕμ k0)
      + (x² * (toℕ (zero {1}) + ℕμ l + ℕμ i + ℕμ g))
      + (x * (toℕ (zero {1}) + ℕμ e + ℕμ h + ℕμ j))
      + ℕμ f                                                                                                     ≡⟨⟩
    x² * (x * ℕμ k0) + (x² * (ℕμ l + ℕμ i + ℕμ g)) + (x * (ℕμ e + ℕμ h + ℕμ j)) + (ℕμ f)                         ≡⟨ lemma₂ x (ℕμ k0) (ℕμ l) (ℕμ i) (ℕμ g) (ℕμ e) (ℕμ h) (ℕμ j) (ℕμ f) ⟩
    x² * (x * ℕμ k0 + ℕμ l) + (x * (x * ℕμ g + ℕμ h)) + (x * (x * ℕμ i + ℕμ j)) + (x * ℕμ e + ℕμ f)              ≡⟨ cong! (sym $ toℕ-combine (μ e) (μ f)) ⟩
    x² * (x * ℕμ k0 + ℕμ l) + x * (x * ℕμ g + ℕμ h) + x * (x * ℕμ i + ℕμ j) + toℕ (combine (μ e) (μ f))          ≡⟨ cong! (sym $ toℕ-combine (μ i) (μ j)) ⟩
    x² * (x * ℕμ k0 + ℕμ l) + x * (x * ℕμ g + ℕμ h) + x * toℕ (combine (μ i) (μ j)) + toℕ (combine (μ e) (μ f))  ≡⟨ cong! (sym $ toℕ-combine (μ g) (μ h)) ⟩
    x² * (x * ℕμ k0 + ℕμ l)
      + x * toℕ (combine (μ g) (μ h))
      + x * toℕ (combine (μ i) (μ j))
      + toℕ (combine (μ e) (μ f))                                                                                ≡⟨ cong (\ φ → x² * φ + x * toℕ (combine (μ g) (μ h)) + x * toℕ (combine (μ i) (μ j)) + toℕ (combine (μ e) (μ f))) $ sym $ toℕ-combine (μ k0) (μ l) ⟩
    x² * toℕ (combine (μ k0) (μ l))
      + x * toℕ (combine (μ g) (μ h))
      + x * toℕ (combine (μ i) (μ j))
      + toℕ (combine (μ e) (μ f))                                                                                ≡⟨⟩
    x² * ℕμ' k0 l + x * ℕμ' g h + x * ℕμ' i j + ℕμ' e f                                                          ≡⟨ cong (\ φ → x² * ℕμ' k0 l + x * ℕμ' g h + x * ℕμ' i j + toℕ (uncurry combine (P.map μ μ φ))) $ sym -bd-eq ⟩
    x² * ℕμ' k0 l + x * ℕμ' g h + x * ℕμ' i j + toℕ (uncurry combine (P.map μ μ (mult multipler b d)))           ≡⟨ cong! (trans -bd-proof $ toℕ-mulF' (μ b) (μ d)) ⟩
    x² * ℕμ' k0 l + x * ℕμ' g h + x * ℕμ' i j + ℕμ b * ℕμ d                                                      ≡⟨ cong (\ φ → x² * ℕμ' k0 l + x * ℕμ' g h + x * toℕ (uncurry combine (P.map μ μ φ)) + ℕμ b * ℕμ d) $ sym -bc-eq ⟩
    x² * ℕμ' k0 l + x * ℕμ' g h + x * toℕ (uncurry combine (P.map μ μ (mult multipler b c))) + ℕμ b * ℕμ d       ≡⟨ cong! (trans -bc-proof $ toℕ-mulF' (μ b) (μ c)) ⟩
    x² * ℕμ' k0 l + x * ℕμ' g h + x * (ℕμ b * ℕμ c) + ℕμ b * ℕμ d                                                ≡⟨ cong (\ φ → x² * ℕμ' k0 l + x * toℕ (uncurry combine (P.map μ μ φ)) + x * (ℕμ b * ℕμ c) + ℕμ b * ℕμ d) $ sym -ad-eq ⟩
    x² * ℕμ' k0 l + x * toℕ (uncurry combine (P.map μ μ (mult multipler a d))) + x * (ℕμ b * ℕμ c) + ℕμ b * ℕμ d ≡⟨ cong! (trans -ad-proof $ toℕ-mulF' (μ a) (μ d)) ⟩
    x² * ℕμ' k0 l + x * (ℕμ a * ℕμ d) + x * (ℕμ b * ℕμ c) + ℕμ b * ℕμ d                                          ≡⟨ cong (\ φ → (x² * toℕ (uncurry combine (P.map μ μ φ))) + (x * (ℕμ a * ℕμ d)) + (x * (ℕμ b * ℕμ c)) + (ℕμ b * ℕμ d)) $ sym -ac-eq ⟩
    (x² * toℕ (uncurry combine (P.map μ μ (mult multipler a c))))
      + (x * (ℕμ a * ℕμ d))
      + (x * (ℕμ b * ℕμ c))
      + (ℕμ b * ℕμ d)                                                                                            ≡⟨ cong! -ac-proof ⟩
    (x² * toℕ (mulF' (μ a) (μ c))) + (x * (ℕμ a * ℕμ d)) + (x * (ℕμ b * ℕμ c)) + (ℕμ b * ℕμ d)                   ≡⟨ cong! (toℕ-mulF' (μ a) (μ c)) ⟩
    (x² * (ℕμ a * ℕμ c)) + (x * (ℕμ a * ℕμ d)) + (x * (ℕμ b * ℕμ c)) + (ℕμ b * ℕμ d)                             ≡⟨ lemma₁ x x (ℕμ a) (ℕμ b) (ℕμ c) (ℕμ d) ⟩
    (x * ℕμ a + ℕμ b) * (x * ℕμ c + ℕμ d)                                                                        ≡⟨ sym $ cong₂ _*_ (toℕ-combine (μ a) (μ b)) (toℕ-combine (μ c) (μ d)) ⟩
    ℕμ' a b * ℕμ' c d                                                                                            ≡⟨ sym $ toℕ-mulF' (μ' a b) _ ⟩
    toℕ (mulF' (μ' a b) (μ' c d))
    ∎
  where
    open ≡-Reasoning
    open +-*-Solver

    lemma₁ : (x1 x2 a b c d : ℕ)
           → (x1 * x2 * (a * c)) + (x1 * (a * d)) + (x2 * (b * c)) + (b * d)
           ≡ (x1 * a + b) * (x2 * c + d)
    lemma₁ =
      solve 6
        (λ x1 x2 a b c d → (x1 :* x2 :* (a :* c)) :+ (x1 :* (a :* d)) :+ (x2 :* (b :* c)) :+ (b :* d)
          := (x1 :* a :+ b) :* (x2 :* c :+ d)) refl

    lemma₂ : (x k0 l i g e h j f : ℕ)
           → (x * x * (x * k0)) + (x * x * (l + i + g)) + (x * (e + h + j)) + f
           ≡ ((x * x * (x * k0 + l)) + (x * (x * g + h)) + (x * (x * i + j)) + (x * e + f))
    lemma₂ =
      solve 9
        (λ x k0 l i g e h j f → (x :* x :* (x :* k0)) :+ (x :* x :* (l :+ i :+ g)) :+ (x :* (e :+ h :+ j)) :+ f
          := ((x :* x :* (x :* k0 :+ l)) :+ (x :* (x :* g :+ h)) :+ (x :* (x :* i :+ j)) :+ (x :* e :+ f))) refl

    lemma₃ : (size k lig ehj f : ℕ)
           → size * size * (size * k + lig) + (size * ehj + f)
           ≡ size * size * size * k + size * size * lig + size * ehj + f
    lemma₃ =
      solve 5
        (λ size k lig ehj f → size :* size :* (size :* k :+ lig) :+ (size :* ehj :+ f)
          := size :* size :* size :* k :+ size :* size :* lig :+ size :* ehj :+ f) refl

    lemma₄ : (size carry k0 lighi lig ehj f : ℕ)
           → size * size * size * (carry + k0 + lighi) + size * size * lig + size * ehj + f
           ≡ size * size * size * (k0 + lighi) + size * size * (size * carry + lig) + size * ehj + f
    lemma₄ =
      solve 7
        (λ size carry k0 lighi lig ehj f → size :* size :* size :* (carry :+ k0 :+ lighi) :+ size :* size :* lig :+ size :* ehj :+ f
          := size :* size :* size :* (k0 :+ lighi) :+ size :* size :* (size :* carry :+ lig) :+ size :* ehj :+ f) refl

    lemma₅ : (size k0 lighi ehjhi liglo ehj f : ℕ)
           → size * size * size * (k0 + lighi) + size * size * (ehjhi + liglo) + size * ehj + f
           ≡ size * size * (size * k0) + size * size * (size * lighi + liglo) + size * (size * ehjhi + ehj) + f
    lemma₅ =
      solve 7
        (λ size k0 lighi ehjhi liglo ehj f → size :* size :* size :* (k0 :+ lighi) :+ size :* size :* (ehjhi :+ liglo) :+ size :* ehj :+ f
          := size :* size :* (size :* k0) :+ size :* size :* (size :* lighi :+ liglo) :+ size :* (size :* ehjhi :+ ehj) :+ f) refl

    drop-carry-0 : -drop-carry ≡ zero
    drop-carry-0 =
      let k0-not-huge = subst (λ φ → toℕ (μ (φ .proj₁)) ≤ _) -ac-eq (mul-not-huge multipler a c)
       in trans (cong proj₂ (sym -add-k0-lig)) (adder-carry-0 small carry k0 lighi {! !})


