---
title: Causality.Data.Vec.Bounded.Membership.Propositional
---

Definitions and proofs about the membership relation for bounded vectors.

```agda
{-# OPTIONS --without-K --safe #-}

module Causality.Data.Vec.Bounded.Membership.Propositional where

open import Data.Vec.Bounded using (Vec≤)
open import Data.Vec.Membership.Propositional using () renaming (_∈_ to _∈ᵛ_)

_∈_ : ∀ {a} {A : Set a} {n} → A → Vec≤ A n → Set _
x ∈ xs = x ∈ᵛ vec xs
  where open Vec≤
```
