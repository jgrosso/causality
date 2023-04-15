---
title: Causality.Function
---

Definitions and proofs about functions.

```agda
{-# OPTIONS --without-K --safe #-}

module Causality.Function where

open import Data.Product using (_,_)
open import Function using (_∘_; _↠_; _↣_; _↩_; Injection; Injective; LeftInverse; mk↠; Surjection)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl)

private
  variable
    a b c : Level
    A     : Set a
    B     : Set b
    C     : Set c

module _ (↣ : B ↣ C) where
  open Injection ↣ using () renaming (injective to f-injective; to to f)

  ↣-monic : {g h : A → B}
    → f ∘ g ≗ f ∘ h
    → g ≗ h
  ↣-monic = f-injective ∘_


module _ (↠ : A ↠ B) where
  open Surjection ↠ using () renaming (surjective to f-surjective; to to f; to⁻ to f⁻¹)

  ↠-epic : {g h : B → C}
    → g ∘ f ≗ h ∘ f
    → g ≗ h
  ↠-epic gf≡hf x
    with (f⁻¹[x] , refl) ← f-surjective x
    = gf≡hf f⁻¹[x]


module _ (↩ : A ↩ B) where
  open LeftInverse ↩ using () renaming (to to f; from to f⁻¹; inverseˡ to f-inverseˡ)

  ↩-epic : {g h : B → C}
    → g ∘ f ≗ h ∘ f
    → g ≗ h
  ↩-epic = ↠-epic (mk↠ λ y → f⁻¹ y , f-inverseˡ y)
```
