---
title: Causality.Data.List
---

Proofs about finite lists.

```agda
module Causality.Data.List where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; _∷_; []; head; last)
open import Data.Maybe using (just; nothing)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

triples : ∀ {a} {A : Set a} → List A → List (A × A × A)
triples []               = []
triples (_ ∷ [])         = []
triples (_ ∷ _ ∷ [])     = []
triples (x ∷ xs@(y ∷ z ∷ _)) = (x , y , z) ∷ triples xs

last≡nothing⇒[] : ∀ {a} {A : Set a} {l : List A}
  → last l ≡ nothing
  → l ≡ []
last≡nothing⇒[] {l = []}         _  = refl
last≡nothing⇒[] {l = _ ∷ []}     ()
last≡nothing⇒[] {l = _ ∷ l@(_ ∷ _)} last≡nothing
  with last≡nothing⇒[] {l = l} last≡nothing
...  | ()

last-of-nonempty : ∀ {a} {A : Set a} {l : List A}
  → l ≢ []
  → ∃[ x ] last l ≡ just x
last-of-nonempty {l = []} l≢[] = ⊥-elim (l≢[] refl)
last-of-nonempty {l = l@(_ ∷ _)} l≢[]
  with last l in last≡
...  | nothing = ⊥-elim (l≢[] (last≡nothing⇒[] last≡))
...  | just x  = x , refl

head-of-nonempty : ∀ {a} {A : Set a} {l : List A}
  → l ≢ []
  → ∃[ x ] head l ≡ just x
head-of-nonempty {l = []} l≢[] = ⊥-elim (l≢[] refl)
head-of-nonempty {l = x ∷ _} l≢[] = x , refl
```
