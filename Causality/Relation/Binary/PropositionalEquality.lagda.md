---
title: Causality.Relation.Binary.PropositionalEquality
---

Definitions and proofs about propositional equality.

```agda
{-# OPTIONS --without-K --safe #-}

module Causality.Relation.Binary.PropositionalEquality where

open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)
open import Relation.Nullary using (¬_)

contra : ∀ {a b} {A : Set a} {B : Set b} {x y z : A}
  → y ≡ x
  → y ≡ z
  → x ≢ z
  → B
contra refl refl x≢z = ⊥-elim (x≢z refl)
```
