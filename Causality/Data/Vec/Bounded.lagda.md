---
title: Causality.Data.Vec.Bounded
---

Definitions and proofs about bounded vectors (i.e. finite lists with an upper bound on their lengths)

```agda
module Causality.Data.Vec.Bounded where

open import Causality.Data.Vec.Bounded.Membership.Propositional using (_∈_)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _,_)
open import Data.Vec as Vec using ()
open import Data.Vec.Relation.Unary.Any using (here; there)
open import Data.Vec.Bounded using (Vec≤; _,_; _∷_)
open import Function using (_∘_; case_of_)
open import Level using (_⊔_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

length : ∀ {a} {A : Set a} {n} → Vec≤ A n → ℕ
length = Vec.length ∘ Vec≤.vec
```

<!--
We define a bijection between bounded vectors (useful if we want to consider them as sets).

-- ```agda
-- module _ {a b} {A : Set a} {B : Set b} where
--   record _⟷_ {n} (xs : Vec≤ A n) (ys : Vec≤ B n) : Set (a ⊔ b) where
--     X : Set _
--     X = Σ A (_∈ xs)

--     Y : Set _
--     Y = Σ B (_∈ ys)

--     field f   : X → Y
--     field f⁻¹ : Y → X

--     field f∘f⁻¹ : (y : Y) → f (f⁻¹ y) ≡ y
--     field f⁻¹∘f : (x : X) → f⁻¹ (f x) ≡ x

--   open _⟷_


--   module _ where
--     open Vec using ([]; _∷_)

--     ⟷⇒≡length : ∀ {n} {xs : Vec≤ A n} {ys : Vec≤ B n} → xs ⟷ ys → length xs ≡ length ys
--     ⟷⇒≡length {0}     {[] , _} {[] , _} _      = refl
--     ⟷⇒≡length {suc n} {xs}     {ys}     xs⟷ys = {!!}
```
-->
