---
title: Causality.Data.Vec.Bounded
---

Definitions and proofs about bounded vectors (i.e. finite lists with an upper bound on their lengths).

```agda
{-# OPTIONS --without-K --safe #-}

module Causality.Data.Vec.Bounded where

open import Causality.Data.Vec
open import Data.List as List using (_∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Vec as Vec using (Vec; []; _∷_; filter)
open import Data.Vec.Bounded as Vec≤ using (Vec≤; _,_; toList)
open import Function using (_∘_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality.Core as Eq using (_≡_; refl)
open import Relation.Nullary using (no; yes)
open import Relation.Unary using (Decidable)

private
  variable
    a : Level
    A : Set a
    n : ℕ

length : Vec≤ A n → ℕ
length = Vec.length ∘ Vec≤.vec

toList∘filter≡filter∘toList : ∀ {p} {P : A → Set p} (P? : Decidable P) (xs : Vec A n)
  → Vec≤.toList (filter P? xs) ≡ List.filter P? (Vec.toList xs)
toList∘filter≡filter∘toList P? [] = refl
toList∘filter≡filter∘toList P? (x ∷ xs)
  with P? x
...  | no ¬Px = toList∘filter≡filter∘toList P? xs
...  | yes Px = Eq.cong (x ∷_) (toList∘filter≡filter∘toList P? xs)

length∘toList≡length : (xs : Vec≤ A n)
  → List.length (toList xs) ≡ length xs
length∘toList≡length ([]     , _)                          = refl
length∘toList≡length (_ ∷ xs , _) rewrite length∘toList xs = refl
```
