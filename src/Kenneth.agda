module Kenneth where

data Void : Set where

open import Data.Product

¬_ : Set -> Set
¬_ a = a -> Void



-- lemma : {A : Set} → (f : A → Set) →  Σ A (λ a → ¬ (f a)) → Void
-- lemma f (fst , snd) = ?


result : {S : Set} (f : S → Set) → ¬ (¬ ((s : S) → f s) → Σ S (λ s → ¬ (f s)))
result f x = {! !}



