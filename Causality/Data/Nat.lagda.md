---
title: Causality.Data.Nat
---

Proofs and definitions about natural numbers.

```agda
{-# OPTIONS --without-K --safe #-}

module Causality.Data.Nat where

open import Data.Nat using (_∸_; _≤_; s≤s; suc; z≤n; zero)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl)

1+m≤1+n⇒m≤n : ∀ {m n} → suc m ≤ suc n → m ≤ n
1+m≤1+n⇒m≤n (s≤s 1+m≤1+n) = 1+m≤1+n

m≡1+n⇒m≢0 : ∀ {m n} → m ≡ suc n → m ≢ 0
m≡1+n⇒m≢0 refl ()
```
