---
title: Causality.CausalGraph
---


Definitions and proofs about causal graphs.

```agda
module Causality.CausalGraph where
```

We import libraries for use below.

```agda
open import Causality.Data.Fin.Subset
open import Causality.Data.Graph
open import Causality.Data.Graphoid
open import Causality.Data.List
open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; ⋃)
import Data.Fin.Subset as Fin
import Data.Fin.Subset.Properties as Fin
open import Data.List using (List; _∷_; []; length)
open import Data.List.Relation.Unary.Linked using (Linked)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as Unique
open import Data.Nat using (ℕ; _≥_; s≤s)
open import Data.Product using (∃-syntax; Σ; Σ-syntax; _×_; _,_) renaming (proj₁ to _₁)
open import Data.Sum using (_⊎_)
open import Function using (_∘_; case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (¬?)
```

We define some utility functions for use below.

```agda
_-×-_ : ∀ {a b c} {A : Set a} → (A → Set b) → (A → Set c) → (A → Set _)
P -×- Q = λ x → P x × Q x

_-⊎-_ : ∀ {a b c} {A : Set a} → (A → Set b) → (A → Set c) → (A → Set _)
P -⊎- Q = λ x → P x ⊎ Q x
```

We parameterize our development by an arbitrary DAG $G$.

```agda
module CausalGraph (G : DAG) where

  open DAG G
```

```agda
  record Path : Set where
    field nodes              : List V
    field distinct-endpoints : length nodes ≥ 2
    field linked             : Linked _∃——_ nodes
    field acyclic            : Unique nodes

    nonempty : nodes ≢ []
    nonempty nodes≡[]
      with nodes | distinct-endpoints
    ...  | []    | ()
    ...  | _ ∷ _ | s≤s _ = case nodes≡[] of λ()

    start : V
    start = head-of-nonempty nonempty ₁

    end : V
    end = last-of-nonempty nonempty ₁

  open Path
```

We define a relation `—↠` s.t. for any two nodes $i, j$ of $G$, `i —↠ j` iff there exists a path starting at $i$ and ending at $j$.

```agda
  _—↠_ : V → V → Set
  from —↠ to = ∃[ p ] start p ≡ from × end p ≡ to
```



```agda
  _∃—↠_ = _—↠_

  triples-along : Path → List (V × V × V)
  triples-along = triples ∘ nodes

  _visits_ : (p : Path) → (v : V) → Set
  p visits v = v ∈ nodes p
    where open import Data.List.Membership.Propositional using (_∈_)

  ConditioningSet : V → V → Set _
  ConditioningSet i j = Σ (Subset |V|) (_⊆∖ ⁅ i , j ⁆₂)

  ∅ : ∀ {i j} → ConditioningSet i j
  ∅ = Fin.⊥ , Fin.⊥⊆


  module Pattern where

    Pattern : ∀ {a} → Set _
    Pattern {a} = V × V × V → Set a


    module Notation where

      _∙_ : ∀ {a b} → (V → V → Set a) → (V → V → Set b) → Pattern
      _l-x_ ∙ _x-r_ = λ{ (l , x , r) → l l-x x × x x-r r }

      ⟶ = _∃⟶_
      ⟵ = _∃⟵_

    open Notation


    _along_ : ∀ {a} → Pattern {a} → Path → Set _
    pat along p =
      Σ[ x ∈ V ]
        Σ[ triple@(_ , x′ , _) ∈ V × V × V ]
          x ≡ x′ × pat triple

    collider common-cause mediator : Pattern
    collider     = ⟶ ∙ ⟵
    common-cause = ⟵ ∙ ⟶
    mediator     = ⟶ ∙ ⟶

    noncollider : Pattern
    noncollider = common-cause -⊎- mediator

    colliders     = collider
    common-causes = common-cause
    mediators     = mediator
    noncolliders  = noncollider

  open Pattern


  descendants : V → Set
  descendants i = ∃[ j ] i ∃—↠ j

  unblocked_∣_ : ∀ {i j} → i —↠ j → ConditioningSet i j → Set
  unblocked (p , _) ∣ (C , _) =
    ((v : noncolliders along p) → v ₁ ∉ C) ×
    ((v : colliders along p) →
       v ₁ ∈ C ⊎
       Σ[ i ∈ descendants (v ₁) ] i ₁ ∈ C)
    where open import Data.Fin.Subset using (_∈_; _∉_)

  blocked_∣_ : ∀ {i j} → i —↠ j → ConditioningSet i j → Set
  blocked p ∣ C = ¬ unblocked p ∣ C

  _⊥_∣_ : (i j : V) → ConditioningSet i j → Set
  i ⊥ j ∣ C = ∀ p → blocked p ∣ C

  _⊥̸_∣_ : (i j : V) → ConditioningSet i j → Set
  i ⊥̸ j ∣ C = ¬ i ⊥ j ∣ C

  _⊥_ : V → V → Set
  i ⊥ j = i ⊥ j ∣ ∅

  _⊥̸_ : V → V → Set
  i ⊥̸ j = i ⊥̸ j ∣ ∅

  intervene-on : Subset |V| → DAG
  intervene-on S = filter-edges (λ{ (_ , to) → ¬? (to ∈? S) })
    where open import Data.Fin.Subset.Properties using (_∈?_)
```
