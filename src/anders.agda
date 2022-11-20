{-# OPTIONS --guardedness  #-}
{-# OPTIONS --type-in-type #-}

module test where

open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Product hiding (_<*>_; map)
open import Data.Sum hiding (map)
open import Data.Maybe
open import Codata.Musical.Notation

infixr 5 _:+:_
infixr 6 _:*:_

-- Reified shape of a data type
data Shape : Set where
  V1 : Shape
  U1 : Shape
  K1 : Set → Shape
  _:+:_ : Shape → Shape → Shape
  _:*:_ : Shape → Shape → Shape
  Par1 : Shape
  -- I don't have inductive types working yet; this constructor is for them.
  -- the issue is I haven't correctly threaded it through the cases, so they
  -- (currently) disagree about what the inductive type should be. I don't
  -- think this is a fundamental problem, just requires threading around as
  -- a variable.
  --
  -- Rec1 : Shape

mutual
  -- Fix points
  record μ (r : Shape) (v : Set) : Set where
    inductive
    pattern
    constructor fix
    field
      getfix : interpret r v

  go : Shape → Set → Set
  go V1 v = ⊥
  go U1 v = ⊤
  go (K1 x) v = x
  go (x :+: y) v = go x v ⊎ go y v
  go (x :*: y) v = go x v × go y v
  go Par1 v = v
  -- go Rec1 v = ? -- μ r v

  -- Evaluate a shape and a parameter into a type in Set
  interpret : Shape → Set → Set
  interpret r v = go r v

-- The instance heads we need to give algorithm instances for
data Head : Set where
  V K U Plus Times P : Head

-- The type of generic things
Generic : Set
Generic = (Set → Set) → Set → Set

-- Instantiate a generic by interpreting the shape as its first argument
Instantiated : Generic → Shape → Set → Set
Instantiated i s a = i (interpret s) a

-- A function from one generic to another
Transform : Generic → Generic → Shape → Set → Set
Transform i o s a = Instantiated i s a → Instantiated o s a

-- A polymorphic Transform
Poly : Generic → Generic → Shape → Set
Poly i o s = {a : Set} → Transform i o s a

-- Functor recursive cases for our algorithm
data Case (i : Generic) (o : Generic) : Head → Set where
  V1C : Poly i o V1 → Case i o V
  U1C : Poly i o U1 → Case i o U
  KC : ({x : Set} → Poly i o (K1 x)) → Case i o K
  +C : ( {l r : Shape}
       → (f : Poly i o l)
       → (g : Poly i o r)
       → Poly i o (l :+: r)
       )
     → Case i o Plus
  *C : ( {l r : Shape}
       → (f : Poly i o l)
       → (g : Poly i o r)
       → Poly i o (l :*: r)
       )
     → Case i o Times
  P1C : Poly i o Par1 → Case i o P
  -- R1C : Poly i o Rec1 → Case i o R

-- A function from heads to cases of it
Cases : ∀ i o → Set
Cases i o = (h : Head) → Maybe (Case i o h)

-- Get the head of a shape
caseOf : Shape → Head
caseOf V1 = V
caseOf U1 = U
caseOf (K1 x) = K
caseOf (x :+: x₁) = Plus
caseOf (x :*: x₁) = Times
caseOf Par1 = P
-- caseOf Rec1 = R


-- Transform Cases into a transformation for the given shape
implement
    : {i o : (Set → Set) → Set → Set}
    → (cases : Cases i o)
    → (r : Shape)
    → Maybe (Poly i o r)
implement cases r with cases (caseOf r)
implement cases r | nothing = nothing
implement cases V1 | just (V1C f) = just f
implement cases U1 | just (U1C f) = just f
implement cases (K1 f₁) | just (KC f) = just f
implement cases (l :+: r) | just (+C f) with implement cases l  | implement cases r
implement cases (l :+: r) | just (+C f) | just x | just y = just (f {l} {r} x y)
implement cases (l :+: r) | just (+C f) | _ | _ = nothing
implement cases (l :*: r) | just (*C f) with implement cases l  | implement cases r
implement cases (l :*: r) | just (*C f) | just x | just y = just (f {l} {r} x y)
implement cases (l :*: r) | just (*C f) | _ | _ = nothing
implement cases Par1 | just (P1C f) = just f

open import Relation.Binary.PropositionalEquality hiding (cong₂; [_])

-- -- A proof that we can encode lists with the given shape machinery
-- module lists where
--   listRep : Shape
--   listRep = U1 :+: Par1 :*: Rec1

--   open import Data.List
--   open import Function
--   open Inverse

--   inv : {A : Set} → List A ↔ interpret listRep A
--   f inv [] = inj₁ tt
--   f inv (x ∷ x₁) = inj₂ (x , fix (f inv x₁))
--   f⁻¹ inv (inj₁ tt) = []
--   f⁻¹ inv (inj₂ (fst , fix v )) = fst ∷ f⁻¹ inv v
--   cong₁ inv refl = refl
--   cong₂ inv refl = refl
--   proj₁ (inverse inv) (inj₁ tt) = refl
--   proj₁ (inverse inv) (inj₂ (fst , fix v)) = cong (\ φ → inj₂ (fst , fix φ)) (proj₁ (inverse inv) v)
--   proj₂ (inverse inv) [] = refl
--   proj₂ (inverse inv) (x ∷ x₁) = cong (\ φ → x ∷ φ) (proj₂ (inverse inv) x₁)

open import Function using (_↔_; const)
open import Data.Maybe
open import Data.Nat
open import Data.Fin using (Fin)

record Finite (A : Set) : Set where
  field
    cardinality : ℕ
    is-finite : A ↔ Fin cardinality
open Finite

Monomorphic : {A : ℕ → Set} → (F : (n : ℕ) → Finite (A n)) → (m n : ℕ) → m ≤ n → Set
Monomorphic F m n p = cardinality (F m) ≤ cardinality (F n)

postulate
  exercise-for-the-reader : {A : Set} → A

open import Data.Vec hiding (map)

open Function using (_$_)
open Function.Inverse renaming (f to fwd; f⁻¹ to bwd)

buildVec : (s : Shape) → Maybe (Σ ℕ λ n → {A : Set} → interpret s A ↔ Vec A n)
buildVec V1 = nothing
buildVec U1 = just
  ( 0
  , record
      { f = const []
      ; f⁻¹ = const tt
      ; cong₁ = const refl
      ; cong₂ = const refl
      ; inverse = (λ { [] → refl }) , λ { tt → refl }
      }
  )
buildVec (K1 x) = nothing
buildVec (s :+: s₁) = nothing
buildVec (l :*: r) with buildVec l | buildVec r
... | just (pi , pbij) | just (qi , qbij) = just
  ( pi + qi
  , record
      { f = λ { (fst , snd) → pbij .fwd fst ++ qbij .fwd snd }
      ; f⁻¹ = λ { x → let (l , (r , proof)) = splitAt pi {qi} x
                       in pbij .bwd l
                        , qbij .bwd r
                }
      ; cong₁ = exercise-for-the-reader
      ; cong₂ = exercise-for-the-reader
      ; inverse = exercise-for-the-reader
      }
  )
... | _ | _ = nothing
buildVec Par1 = just
  (1
  , record
      { f = [_]
      ; f⁻¹ = head
      ; cong₁ = λ { x → cong (_∷ []) x }
      ; cong₂ = λ { x → cong head x }
      ; inverse = (λ { (x ∷ []) → refl })
                 , λ { x → refl }
      }
  )


Natural : Generic → Set
Natural i = {F G : Set → Set} {A : Set} → ({X : Set} → F X → G X) → i F A → i G A

{-

instance (C f, C g) => C (f :+: g) where

-}

postulate
  oracle
    : {Idx : Set}
    → {rep : Idx → Set → Set}
    → {i o : Generic}
    → (_∙_ : Shape → Shape → Shape)
    → (spec : (idx : Idx) → {A : Set} → i (rep idx) A → o (rep idx) A)
    → Maybe (
      {l r : Shape}
       → (f : Poly i o l)
       → (g : Poly i o r)
       → Poly i o (l ∙ r)
       )


synthesize
      -- All of our representations are indexed by some arbitrary type
      -- we make the assumption that this is a total mapping
    : {Idx : Set}
    → {rep : Idx → Set → Set}
      -- Then, we have an input and output type family
    → {i o : Generic}
      -- For any given shape, we can decide whether there is an index which
      -- gives rise to this shape; as well as show the equivalence between the
      -- functor shape and the representation itself
    → (build : (s : Shape) → Maybe (Σ Idx λ idx → {A : Set} → interpret s A ↔ rep idx A))
      -- We have natural transformations over i and o
    → (i-nat : Natural i) → (o-nat : Natural o)
      -- We have a specification for every index
    → (spec : (idx : Idx) → {A : Set} → i (rep idx) A → o (rep idx) A)
      -- we can thus build a set of cases such that
    → Σ (Cases i o) λ cases →
      (∀ (A : Set)
        -- for any index that is isomorphic to a given shape
        → (idx : Idx)
        → (r : Shape)
        → (same : {X : Set} → interpret r X ↔ rep idx X)
        -- and some given input
        → (x : Instantiated i r A)
        -- we show that our cases compose together to produce the same answer
        -- as the specification
        → map (λ { f → f {A} x }) (implement cases r)
        ≡ just (o-nat (same .bwd) (spec idx {A} (i-nat (same .fwd) x)))
      )
proj₁ (synthesize build i-nat o-nat spec) V with build V1
... | just (idx , bij) = just (V1C λ { x → o-nat (bij .bwd) (spec idx (i-nat (bij .fwd) x)) } )
... | nothing = nothing
proj₁ (synthesize build i-nat o-nat spec) K = {! !}
proj₁ (synthesize build i-nat o-nat spec) U with build U1
... | just (idx , bij) = just (U1C λ { x → o-nat (bij .bwd) (spec idx (i-nat (bij .fwd) x)) })
... | nothing = nothing
proj₁ (synthesize build i-nat o-nat spec) Plus = {!  !}
proj₁ (synthesize build i-nat o-nat spec) Times = {! !}
proj₁ (synthesize build i-nat o-nat spec) P with build Par1
... | just (idx , bij) = just (P1C λ { x → o-nat (bij .bwd) (spec idx (i-nat (bij .fwd) x)) })
... | nothing = nothing
proj₂ (synthesize build i-nat o-nat spec) = {! !}


-- syn
--     : {Idx : Set}
--     → {rep : Idx → Set → Set}
--     → {i o : Generic}
--     → (build : {A : Set} → (s : Shape) → Maybe (A → Σ Idx λ idx → interpret s A ↔ rep idx A))
--     → (spec : {A : Set} → (idx : Idx) → i (rep idx) A → o (rep idx) A)
--     → Σ (Cases i o) λ cases →
--       (∀ (A : Set)
--         → (idx : Idx)
--         → (r : Shape)
--         → interpret r A ↔ rep idx A
--         → (x : Instantiated i r A)
--         → (res : Instantiated o r A)
--         → implement cases r ≡ nothing -- × spec {A} idx ⊤
--       )
-- proj₁ (syn build spec) V with build V1
-- ... | just x = just (V1C λ { f → {! !} })
-- ... | nothing = nothing
-- proj₁ (syn build spec) K = {! !}
-- proj₁ (syn build spec) U = {! !}
-- proj₁ (syn build spec) Plus = {! !}
-- proj₁ (syn build spec) Times = {! !}
-- proj₁ (syn build spec) P = {! !}
-- proj₂ (syn build spec) = {! !}


--postulate
--  shape-equiv : Shape → Shape → Set
--  shape-subst : {a b : Shape} → shape-equiv a b → (f : Shape → Set) → f a ≡ f b


--  synthesize
--      : -- Given type families for input and outputs
--        (i o : Generic)
--      → (build : {A : Set} → (s : Shape) → A → Maybe (interpret s A) )
--        -- and some shape
--      → (r : ℕ → Shape)
--        -- And a polymorphic function transforming from the inputs to the outputs
--      → (f : (n : ℕ) → Poly i o (r n))
--        -- synthesize a Cases
--      → Σ (Cases i o) λ cases →
--        -- such that for any instantiation of the functor variable
--        (∀ (a : Set)
--        -- and for any other shape isomorphic to r
--         → (r' : Shape) → (iso : shape-equiv (r 0) r')
--        -- for any input
--         → (x : Instantiated i (r 0) a)
--        -- the cases compose to give the same answer as f
--         → implement cases (r 0) {a} x ≡ f 0 {a} x
--        -- (imagine this uses shape-subst over iso to show it doesn't matter how you compose the cases
--        -- so long as it all works out to be the right type --- I want to get this sent off and getting
--        -- it to typecheck doesn't seem like a good use of time
--        -- )
--         )

--open import Data.Nat using (ℕ; zero; suc)

--vecRep : ℕ → Shape
--vecRep zero = U1
--vecRep (suc x) = Par1 :*: vecRep x

--postulate
--  functor-go : {a b : Set} → (a → b) → {r : Shape} → go r a → go r b

--module ex where
--  open import Agda.Primitive using (lzero)

--  record Monoid (A : Set) : Set where
--    field
--      mempty : A
--      _<>_ : A → A → A

--  input : Generic
--  input f a = Monoid a × f a

--  output : Generic
--  output f a = f a × a

----   gen-fp : ?
----   gen-fp = synthesize input output (vecRep 8)

--  result : Cases input output
--  result V = V1C λ { (mon , ()) }
--  result K = KC λ { (mon , fa) → fa , mon .Monoid.mempty }
--  result U = U1C λ { (mon , fa) → tt , mon .Monoid.mempty }
--  result Plus =
--    +C λ { f g (mon , inj₁ x) → let fa' , a' = f (mon , x) in inj₁ fa' , a'
--         ; f g (mon , inj₂ y) → let fa' , a' = g (mon , y) in inj₂ fa' , a'
--         }
--  result Times = *C λ {
--    {l} {r} f g (mon , x , y) →
--      let fa1 , a1 = f (mon , x)
--          fa2 , a2 = g (mon , y)
--       in (fa1 , functor-go (mon .Monoid._<>_ a1) {r} fa2) , mon .Monoid._<>_ a1 a2
--    }
--  result P = P1C λ { (mon , fa) → mon .Monoid.mempty , fa }
--  -- result R = R1C λ { (mon , fa) → {! !} }


--  -- ok so let's work through actually deriving this!
--  -- how can we do it? need a U case and a * case, really
--  -- U case feels underspecified;
--  --    need a transformation `(input (Vec 8) a -> output (Vec 8) a) -> input U a -> output U a`
--  -- instead we can probably tackle the * case
--  --  need to divide the problem into an L=4 and an R=4
--  --  such that (l ++ r) = z
--  --  and then we can run (f l : Vec 4, g r : Vec 4)
--  --  now just need a way to put them together
--  --    concat would work but doesnt quite
--  --  feels like we can derive
--  -- correctness from * and push it backwards
--  --  pretend we have oracles f and g; prove f * g
--  --  now INSTANTIATE f and g st they compose to the right answer
--  --
--  --  search:
--  --    oracle on *
--  --    i don't think this works; we just don't have enough to constrain the
--  --    problem
--  --
--  --  ok so what if we added more?
--  --  maybe a refinement that everything is in the right order?
--  --
--  --  i think the problem is underspecified

--  open import Data.Vec

--  postulate
--    specification
--      : (a : Set)
--      → input  (Function.flip Vec 8) a
--      → output (Function.flip Vec 8) a

--  -- we can do the work for * by taking an input,
--  -- running from; and now we have two inputs we can just futz with
--  --
--  -- i guess more generally this works for whateer the top level shape is

--  -- ok so inspect vecRep 4; first constructor is :*:
--  -- great, so we are solving for * first
--  -- generate an input term, from it, separate over :*:
--  -- ?????? angelic solve it?
--  --
--  -- problem is we can't get a base case.
--  -- so what if we let n range on the input
--  -- ST it is monotonic in the size
--  -- now if we instantiate at 0 we maybe get some work done
--  --
--  -- ????? can we find a fixpoint
--  -- angelic fixpoint stable under self substitution
--  --
--  -- is the problem easy if we have polymorphic a?
--  --
--  -- let a = ()
--  --
--  -- certainly easier if we have a generator for outputs
--  -- then we can just sidestep the problem by synthesizing good outputs and then
--  -- replacing them in the algorithm
--  --
--  -- eg:
--  --
--  -- let l r = generate @Vec4
--  -- let i = to (l :*: r) NO THIS IS NO GOOD
--  --
--  -- ok back to polymorphic a
--  --
--  -- are all we looking for is stability under self substitution? what does this
--  -- even mean
--  --
--  -- what if we count inhabitants??
--  --  - vec 8 a = a^8
--  --  - instantiate at (), now one inhabitant
--  --  - k () * k () ...
--  --  - can we now solve for k?
--  --
--  --  no because k is natural! so maybe it's exercise-for-the-reader to solve
--  --  do something symbolic?
--  --
--  --  fundamentally the problem here is we don't have a way to verify partial
--  --  solutions. a refinement would help a lot
--  --
--  -- U is exercise-for-the-reader to find in this case
--  -- K also exercise-for-the-reader
--  -- (but hard to verify)
--  -- V also exercise-for-the-reader
--  --
--  -- assuming we have K we can synthesize * by trying and then just decomposing

--  *-solved : Instantiated output (vecRep 4) ℕ
--         → Instantiated output (vecRep 4) ℕ
--         → Instantiated output (vecRep 8) ℕ
--  *-solved l r = {! by solver !}

--  *-case : Case input output Times
--  *-case = *C λ { f g x → {! !} }
--    -- synthesize polymorphic results
--    -- verify by instantiatng l = r = vecRep 4

--  v-case : Case input output V
--  v-case = V1C λ { () }
--    -- synthesize polymorphic results
--    -- verify by running *-case, instantiating at either U or *





--open import Data.List

---- work through a synthesis example by hand
---- imagine an oracle synthesizer
---- probably a matrix multiplication example

