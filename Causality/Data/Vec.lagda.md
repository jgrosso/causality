---
title: Causality.Data.Vec
---

Definitions and proofs about "vectors" (finite lists, except their types are indexed by their lengths).

```agda
module Causality.Data.Vec where

open import Data.Bool using (false; true)
open import Data.Nat using (_>_; s≤s; suc; z≤n)
open import Data.Product using (Σ)
open import Data.Vec using (Vec; []; _∷_; _[_]=_; count; filter; here; length; there)
open import Data.Vec.Bounded using (Vec≤)
open import Data.Vec.Relation.Unary.Any using (here; there)
open import Data.Vec.Membership.Propositional using (_∈_)
open import Level using (_⊔_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (does; no; yes)
open import Relation.Nullary.Negation.Core using (contradiction)
open import Relation.Unary using (Decidable)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; cong; refl)

count>0 : ∀ {a} {A : Set a} {p} {P : A → Set p} (P? : Decidable P) {n} {xs : Vec A n} {x}
  → P x
  → x ∈ xs
  → count P? xs > 0
count>0 P? {x = x} Px (here refl)
  with P? x
...  | yes _  = s≤s z≤n
...  | no ¬Px = contradiction Px ¬Px
count>0 P? Px (there {x = x} y∈xs)
  with P? x
...  | yes _ = s≤s z≤n
...  | no  _ = count>0 P? Px y∈xs

count≟->0 : ∀ {a} {A : Set a} (_≟_ : DecidableEquality A) {n} {xs : Vec A n} {x}
  → x ∈ xs
  → count (_≟ x) xs > 0
count≟->0 _≟_ = count>0 (_≟ _) refl

xs[]=x⇒x∈xs : ∀ {a} {A : Set a} {n} {xs : Vec A n} {x i}
  → xs [ i ]= x
  → x ∈ xs
xs[]=x⇒x∈xs here            = here refl
xs[]=x⇒x∈xs (there xs[i]=x) = there (xs[]=x⇒x∈xs xs[i]=x)

count≡length∘filter : ∀ {a p} {A : Set a} {P : A → Set p} {n} (P? : Decidable P) (xs : Vec A n)
  → Vec≤.length (filter P? xs) ≡ count P? xs
count≡length∘filter _  []       = refl
count≡length∘filter P? (x ∷ xs)
  with P? x
...  | yes _ = cong suc (count≡length∘filter P? xs)
...  | no  _ = count≡length∘filter P? xs
```

<!--
We define a bijection between bounded vectors (useful if we want to consider them as finite sets).

```agda
-- module _ {a b} {A : Set a} {B : Set b} where
--   record _⟷_ {n} (xs : Vec A n) (ys : Vec B n) : Set (a ⊔ b) where
--     X : Set _
--     X = Σ A (_∈ xs)

--     Y : Set _
--     Y = Σ B (_∈ ys)

--     field f   : X → Y
--     field f⁻¹ : Y → X

--     field f∘f⁻¹ : (y : Y) → f (f⁻¹ y) ≡ y
--     field f⁻¹∘f : (x : X) → f⁻¹ (f x) ≡ x

--   open _⟷_


--   ⟷⇒≡length : ∀ {n} {xs : Vec A n} {ys : Vec B n} → xs ⟷ ys → length xs ≡ length ys
--   ⟷⇒≡length {0}     {[]} {[]} _      = refl
--   ⟷⇒≡length {suc n} {xs} {ys} xs⟷ys = {!!}
```
-->
