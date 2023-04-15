---
title: Causality.Data.Vec
---

Definitions and proofs about vectors (finite lists, except their types are indexed by their lengths).

```agda
{-# OPTIONS --without-K --safe #-}

module Causality.Data.Vec where

open import Causality.Data.Product
open import Data.Bool using (false; true)
import Data.List as List
open import Data.List.Relation.Unary.Any as List using (here; there)
open import Data.Nat using (ℕ; _>_; s≤s; suc; z≤n)
open import Data.Nat.Properties using (n≤1+n)
open import Data.Product using (Σ; ∃-syntax; _×_; _,_)
open import Data.Vec using (Vec; []; _∷_; _++_; _[_]=_; count; filter; here; length; there; toList)
open import Data.Vec.Bounded as Vec≤ using (Vec≤)
open import Data.Vec.Relation.Unary.Any using (Any; here; there)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
open import Data.Vec.Membership.Propositional using (_∈_)
open import Function using (_∘_)
open import Level using (Level)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (¬_; does; no; yes)
open import Relation.Nullary.Negation.Core using (contradiction)
open import Relation.Unary using (Decidable)
open import Relation.Binary.PropositionalEquality.Core as Eq using (_≡_; refl)

private
  variable
    a : Level
    A : Set a
    n : ℕ

module _ {p} {P : A → Set p} (P? : Decidable P) where
  ∈⇒count>0 : ∀ {xs : Vec A n} {x}
    → P x
    → x ∈ xs
    → count P? xs > 0
  ∈⇒count>0 {x = x} Px (here refl)
    with P? x
  ...  | yes _  = s≤s z≤n
  ...  | no ¬Px = contradiction Px ¬Px
  ∈⇒count>0 Px (there {x = x} x∈xs)
    with P? x
  ...  | yes _ = s≤s z≤n
  ...  | no  _ = ∈⇒count>0 Px x∈xs

  count≡length∘filter : (xs : Vec A n)
    → Vec≤.length (filter P? xs) ≡ count P? xs
  count≡length∘filter [] = refl
  count≡length∘filter (x ∷ xs)
    with P? x
  ...  | yes _ = Eq.cong suc (count≡length∘filter xs)
  ...  | no  _ = count≡length∘filter xs

∈⇒count≟>0 : ∀ (_≟_ : DecidableEquality A) {xs : Vec A n} {x}
  → x ∈ xs
  → count (_≟ x) xs > 0
∈⇒count≟>0 _≟_ = ∈⇒count>0 (_≟ _) refl

xs[]=x⇒x∈xs : ∀ {xs : Vec A n} {x i}
  → xs [ i ]= x
  → x ∈ xs
xs[]=x⇒x∈xs here            = here  refl
xs[]=x⇒x∈xs (there xs[i]=x) = there (xs[]=x⇒x∈xs xs[i]=x)

length∘toList : (xs : Vec A n)
  → List.length (toList xs) ≡ n
length∘toList [] = refl
length∘toList (x ∷ xs) rewrite length∘toList xs = refl
```
