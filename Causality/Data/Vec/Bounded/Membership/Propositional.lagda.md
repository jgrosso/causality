---
title: Causality.Data.Vec.Bounded.Membership.Propositional
---

Definitions and proofs about the membership relation for bounded vectors.

```agda
module Causality.Data.Vec.Bounded.Membership.Propositional where

open import Data.Vec.Bounded using (Vec≤)
open import Data.Vec.Membership.Propositional as Vec using ()

_∈_ : ∀ {a} {A : Set a} {n} → A → Vec≤ A n → Set _
x ∈ xs = x Vec.∈ Vec≤.vec xs
```
