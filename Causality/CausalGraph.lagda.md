---
title: Causality.CausalGraph
---

Definitions and proofs about causal graphs.

<details>
<summary>Some initial bookkeeping.</summary>

```agda
{-# OPTIONS --without-K --safe #-}

module Causality.CausalGraph where
```

We import some of the other files in this project (to see the documentation for a module, click on its name).

```agda
open import Causality.Data.Fin.Subset
open import Causality.Data.Graph
open import Causality.Data.Graphoid
open import Causality.Data.List
```

<details>
<summary>Standard library imports.</summary>

```agda
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
open import Relation.Nullary using (¬_; ¬?; contradiction)
```
</details>

<details>
<summary>Some utility functions, for use below.</summary>

```agda
_-×-_ : ∀ {a b c} {A : Set a} → (A → Set b) → (A → Set c) → (A → Set _)
P -×- Q = λ x → P x × Q x

_-⊎-_ : ∀ {a b c} {A : Set a} → (A → Set b) → (A → Set c) → (A → Set _)
P -⊎- Q = λ x → P x ⊎ Q x
```
</details>
</details>

We parameterize our development by an arbitrary DAG $G$.

```agda
module CausalGraph (G : DAG) where

  open DAG G
```

We define a "path" through a causal graph to be a list of vertices connected by adjacencies.

```agda
  record Path : Set where
    field nodes              : List V
    field linked             : Linked _∃——_ nodes
```

We require that the path be acyclic, i.e. that no vertex is revisited, i.e. that the list of vertices
has no duplicates. We will also require that there are at least two vertices in our list, so that
we have distinct start– and endpoints.

```
    field acyclic            : Unique nodes
    field distinct-endpoints : length nodes ≥ 2

    nonempty : nodes ≢ []
    nonempty nodes≡[]
      with nodes | distinct-endpoints
    ...  | []    | ()
    ...  | _ ∷ _ | s≤s _ = contradiction nodes≡[] λ()

    start : V
    start = head-of-nonempty nonempty ₁

    end : V
    end = last-of-nonempty nonempty ₁

  open Path
```

For any two vertices $i, j$ in $G$, we will let `i —↠ j` denote the set of paths from $i$ to $j$.

```agda
  _—↠_ : V → V → Set
  from —↠ to = ∃[ p ] start p ≡ from × end p ≡ to
```

We will say `i ∃—↠ j` iff there exists a path starting at $i$ and ending at $j$.

```agda
  _∃—↠_ = _—↠_
```

<details>
<summary>Some helper functions for working with paths.</summary>

```agda
  triples-along : Path → List (V × V × V)
  triples-along = triples ∘ nodes

  _visits_ : (p : Path) → (v : V) → Set
  p visits v = v ∈ nodes p
    where open import Data.List.Membership.Propositional using (_∈_)
```
</details>

A subset of $V$ is a valid conditioning set (w.r.t. some path `i —↠ j`) iff $C \subseteq V \setminus \{ i , j \}$.

```agda
  ConditioningSet : V → V → Set _
  ConditioningSet i j = Σ (Subset |V|) (_⊆∖ ⁅ i , j ⁆₂)
```

We will denote the empty conditioning set by $\varnothing$.

```agda
  ∅ : ∀ {i j} → ConditioningSet i j
  ∅ = Fin.⊥ , Fin.⊥⊆
```

<details>
<summary>Groundwork to let us define colliders, noncolliders, etc.</summary>

```agda
  module Pattern where

    Pattern : ∀ {a} → Set _
    Pattern {a} = V × V × V → Set a


    module Notation where

      _∙_ : ∀ {a b} → (V → V → Set a) → (V → V → Set b) → Pattern
      _l-x_ ∙ _x-r_ = λ{ (l , x , r) → l l-x x × x x-r r }

      ⟶ = _∃⟶_
      ⟵ = _∃⟵_

    open Notation
```
</details>

```agda
    collider common-cause mediator : Pattern
    collider     = ⟶ ∙ ⟵
    common-cause = ⟵ ∙ ⟶
    mediator     = ⟶ ∙ ⟶
```

A noncollider is either a common cause or a mediator.

```agda
    noncollider : Pattern
    noncollider = common-cause -⊎- mediator
```

We will write `colliders along p` to denote "the set of all vertices that are colliders along some path $p$"
(and similarly for common causes, etc.).

```agda
    _along_ : ∀ {a} → Pattern {a} → Path → Set _
    pat along p =
      Σ[ x ∈ V ]
        Σ[ triple@(_ , x′ , _) ∈ V × V × V ]
          x ≡ x′ × pat triple

    colliders     = collider
    common-causes = common-cause
    mediators     = mediator
    noncolliders  = noncollider

  open Pattern
```

A vertex $j$ is a descendant of $i$ iff there exists a path from $i$ to $j$.

```agda
  descendants : V → Set
  descendants i = ∃[ j ] i ∃—↠ j
```

A path from $i$ to $j$ is unblocked (conditional on $C$) iff:

```agda
  unblocked_∣_ : ∀ {i j} → i —↠ j → ConditioningSet i j → Set
  unblocked (p , _) ∣ (C , _) =
```

1. all noncolliders along the path are not in $C$, and

```agda
    ((v : noncolliders along p) → v ₁ ∉ C) ×
```

2. all colliders along $p$ are:

```agda
    ((v : colliders along p) →
```

   a) in $C$, or

```agda
       v ₁ ∈ C ⊎
```

   b) have a descendant in $C$.

```agda
       Σ[ i ∈ descendants (v ₁) ] i ₁ ∈ C)
```

```agda
    where open import Data.Fin.Subset using (_∈_; _∉_)
```

A path is blocked iff it is not unblocked.

```agda
  blocked_∣_ : ∀ {i j} → i —↠ j → ConditioningSet i j → Set
  blocked p ∣ C = ¬ unblocked p ∣ C
```

Two vertices are $d$-separated (conditional on $C$) iff all paths between them are blocked.

```agda
  _⊥_∣_ : (i j : V) → ConditioningSet i j → Set
  i ⊥ j ∣ C = ∀ p → blocked p ∣ C
```

Two vertices are $d$-connected (conditional on $C$) iff they are not $d$-separated.

```agda
  _⊥̸_∣_ : (i j : V) → ConditioningSet i j → Set
  i ⊥̸ j ∣ C = ¬ i ⊥ j ∣ C
```

Two vertices are $d$-separated (unconditionally) iff they are $d$-separated conditional on $\varnothing$.

```agda
  _⊥_ : V → V → Set
  i ⊥ j = i ⊥ j ∣ ∅
```

Two vertices are $d$-connected (uncoditionally) iff they are not $d$-separated (unconditionally).

```agda
  _⊥̸_ : V → V → Set
  i ⊥̸ j = i ⊥̸ j ∣ ∅
```

To intervene on a set of vertices $S$, we remove all edges going into vertices of $S$.

```agda
  intervene-on : Subset |V| → DAG
  intervene-on S = filter-edges (λ{ (_ , to) → ¬? (to ∈? S) })
    where open import Data.Fin.Subset.Properties using (_∈?_)
```
