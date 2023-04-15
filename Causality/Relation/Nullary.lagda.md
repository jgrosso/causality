---
title: Causality.Relation.Nullary
---

Definitions and proofs about (nullary) propositions.

```agda
{-# OPTIONS --without-K --safe #-}

module Causality.Relation.Nullary where

open import Function using (_∘_; _⇔_; Equivalence)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality as Eq using (refl)

¬-distr-⇔ : ∀ {a b} {A : Set a} {B : Set b}
  →    A  ⇔    B
  → (¬ A) ⇔ (¬ B)
¬-distr-⇔ A⇔B =
  record
    { to        = _∘ from
    ; from      = _∘ to
    ; to-cong   = λ{ refl → refl }
    ; from-cong = λ{ refl → refl }
    }
  where open Equivalence A⇔B
```
