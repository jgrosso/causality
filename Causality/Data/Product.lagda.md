---
title: Causality.Data.Product
---

Definitions and proofs about dependent products.

```agda
{-# OPTIONS --without-K --safe #-}

module Causality.Data.Product where

open import Data.Product using (∃-syntax; ∃₂; _×_; _,_)
open import Level using (Level)
open import Relation.Nullary using (_×-dec_)
open import Relation.Unary using (Decidable)

private
  variable
    a a′ b b′ c : Level
    A           : Set a
    A′          : Set a′
    B           : A       → Set b
    B′          : A       → Set b′
    C           : (x : A) → B x → Set c
```

Haskell's fanout function on arrows, `(&&&)`, specialized to `→`.

```agda
_&&&_ : ((x : A) → B x) → ((x : A) → B′ x) → ((x : A) → B x × B′ x)
f &&& g = λ x → f x , g x
```

The analogous type-level operator, i.e. with `×` instead of `,`.

```agda
_-×-_ : (A → Set a) → (A → Set b) → (A → Set _)
P -×- Q = λ x → P x × Q x

_-×-dec-_ : {P : A → Set a} {Q : A → Set b} (P? : Decidable P) (Q? : Decidable Q)
  → Decidable (P -×- Q)
P -×-dec- Q = λ x → P x ×-dec Q x
```

```agda
infix 2 ∃₂-syntax

∃₂-syntax = ∃₂

syntax ∃₂-syntax (λ x y → B) = ∃[ x y ] B

∃₃ : ∀ {d} (D : (x : A) → (y : B x) → C x y → Set d) → Set _
∃₃ D = ∃[ a ] ∃[ b ] ∃[ c ] D a b c

infix 2 ∃₃-syntax

∃₃-syntax = ∃₃

syntax ∃₃-syntax (λ x y z → C) = ∃[ x y z ] C
```
