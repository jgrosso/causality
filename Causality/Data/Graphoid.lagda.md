---
title: Causality.Data.Graphoid
---

Definitions and proofs about (semi-)graphoids.

```agda
module Causality.Data.Graphoid where
```

We import libraries for use below.

```agda
open import Causality.Data.Fin.Subset
open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; _∪_; _⊆_) renaming (⊥ to ∅)
open import Data.List using (List)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Nat using (ℕ)
open import Data.Product using (∃-syntax; Σ; _×_; proj₁)
```

We begin by formalizing the following definition on pg. 11 of [@geiger]:

> A *dependency model* $M$ over a finite set of elements $U$ is any subset of triplets $(X, Z, Y)$ where $X$, $Y$, and $Z$ are disjoint subsets of $U$.

We parameterize our definitions by the cardinality $|U|$ of our universe of discourse.

```agda
module Graphoid (|U| : ℕ) where
```

We represent the universe by a finite set $U$ (namely, with cardinality $|U|$).

```agda
  U : Set
  U = Fin |U|
```

```agda
  record Triple : Set where
    constructor ⟨_,_,_⟩
    field
      _₁ : Subset |U|
      _₂ : Subset |U|
      _₃ : Subset |U|


  record DisjointTriple : Set where
    constructor _,_

    field base : Triple
    open Triple base public

    field disjoint : Disjoint _₁ _₂ × Disjoint _₂ _₃ × Disjoint _₁ _₃
```

[@geiger] defines dependency models in terms of sets, which are difficult to represent directly in Agda.
Instead, we define a dependency model as a finite list of mutually disjoint triplets.

```agda
  DependencyModel : Set
  DependencyModel = List DisjointTriple
```

We define notation to allow us to represent statements of the form $(X, Y, Z) \in M$ (i.e. $I(X, Y, Z)$) as `⟨ X , Y , Z ⟩ ∈ M`.

```agda
  _∈_ : Triple → DependencyModel → Set
  ⟨ x , y , z ⟩ ∈ M = ∃[ disjoint ] (⟨ x , y , z ⟩ , disjoint) ∈ˡ M
    where open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ˡ_)
```

We now define the graphoid axioms, and define (semi-)graphoids to be dependency models that satisfy these axioms.

```agda
  module _ (M : DependencyModel) where

    TrivialIndependence : Set
    TrivialIndependence = ∀ {x z}
      → ⟨ x , z , ∅ ⟩ ∈ M

    Symmetry : Set
    Symmetry = ∀ {x y z}
      → ⟨ x , z , y ⟩ ∈ M
      → ⟨ y , z , x ⟩ ∈ M

    Decomposition : Set
    Decomposition = ∀ {x y z w}
      → ⟨ x , z , y ∪ w ⟩ ∈ M
      → ⟨ x , z , y ⟩ ∈ M

    WeakUnion : Set
    WeakUnion = ∀ {x y z w}
      → ⟨ x , z , y ∪ w ⟩ ∈ M
      → ⟨ x , z ∪ w , y ⟩ ∈ M

    Contraction : Set
    Contraction = ∀ {x y z w}
      → ⟨ x , z , y ⟩ ∈ M
      → ⟨ x , z ∪ y , w ⟩ ∈ M
      → ⟨ x , z , y ∪ w ⟩ ∈ M

    Intersection : Set
    Intersection = ∀ {x y z w}
      → ⟨ x , z ∪ w , y ⟩ ∈ M
      → ⟨ x , z ∪ y , w ⟩ ∈ M
      → ⟨ x , z , y ∪ w ⟩ ∈ M


  record IsSemiGraphoid (M : DependencyModel) : Set where
    field
      trivial-independence : TrivialIndependence M
      symmetry             : Symmetry            M
      decomposition        : Decomposition       M
      weak-union           : WeakUnion           M
      contraction          : Contraction         M


  record SemiGraphoid : Set where
    field
      M                : DependencyModel
      is-semi-graphoid : IsSemiGraphoid M

    open IsSemiGraphoid is-semi-graphoid public


  record IsGraphoid (M : DependencyModel) : Set where
    field
      semi-graphoid : IsSemiGraphoid M
      intersection  : Intersection   M

    open IsSemiGraphoid semi-graphoid public


  record Graphoid : Set where
    field
      M           : DependencyModel
      is-graphoid : IsGraphoid M

    open IsGraphoid is-graphoid public
```
