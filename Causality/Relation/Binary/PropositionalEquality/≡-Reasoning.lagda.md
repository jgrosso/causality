---
title: Causality.Relation.Binary.PropositionalEquality.≡-Reasoning
---

Definitions and proofs to help with reasoning about propositional equality.

```agda
{-# OPTIONS --without-K --safe #-}

module Causality.Relation.Binary.PropositionalEquality.≡-Reasoning {a} {A : Set a} where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

infix  3 _∎
infixr 2 _≡⟨⟩_ _≡⟨_⟩_ _≡⟨_⟩⟨_⟩_
infix  1 begin_

begin_ : {x y : A} → x ≡ y → x ≡ y
begin_ x≡y = x≡y

_≡⟨⟩_ : (x {y} : A) → x ≡ y → x ≡ y
_ ≡⟨⟩ x≡y = x≡y

_≡⟨_⟩_ : (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

_≡⟨_⟩⟨_⟩_ : ∀ {b} {B : Set b} (x {y z} : A) {x′ y′ : B} → x′ ≡ y′ → (x′ ≡ y′ → x ≡ y) → y ≡ z → x ≡ z
x ≡⟨ x′≡y′ ⟩⟨ lift ⟩ y≡z = x ≡⟨ lift x′≡y′ ⟩ y≡z

_∎ : ∀ (x : A) → x ≡ x
_∎ _ = refl
```
