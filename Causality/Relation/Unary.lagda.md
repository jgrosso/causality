---
title: Causality.Relation.Unary
---

Definitions and proofs about (unary) predicates.

```agda
{-# OPTIONS --without-K --safe #-}

module Causality.Relation.Unary where

open import Data.Product using (_,_)
open import Function using (_∘_)
open import Relation.Unary using (_≐_; ∁)

∁-distr-≐ : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q}
  →   P ≐   Q
  → ∁ P ≐ ∁ Q
∁-distr-≐ (P⊆Q , Q⊆P) = _∘ Q⊆P , _∘ P⊆Q
```
