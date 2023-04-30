---
title: Causality.Data.Graphoid
---

Definitions and proofs about (semi-)graphoids.

```agda
{-# OPTIONS --without-K --safe #-}

module Causality.Data.Graphoid where
```

We import libraries for use below.

```agda
open import Causality.Data.Fin.Subset renaming (_≟_ to _≟ˢ_)
open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; _∪_)
open import Data.List using (List)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ˡ_)
open import Data.Nat using (ℕ)
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_)
open import Level using (Level; _⊔_; suc)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_; _×-dec_; contradiction; no; yes)
open import Relation.Unary using (Pred) renaming (_∈_ to _∈ᵖ_)
```

```agda
private
  variable
    a b : Level
```

We begin by formalizing the following definition on pg. 11 of [@geiger]:

> A *dependency model* $M$ over a finite set of elements $U$ is any subset of triplets $(X, Z, Y)$ where $X$, $Y$, and $Z$ are disjoint subsets of $U$.

We will parameterize our definitions by the cardinality $|U|$ of our universe of discourse. We will represent the universe itself by a finite set $U$ (i.e. with cardinality $|U|$).

```agda
module Graphoid (∣U∣ : ℕ) where
  U : Set _
  U = Fin ∣U∣
```

We define (disjoint) triples:

```agda
  record Triple : Set where
    constructor ⟨_,_,_⟩
    field
      _₁ : Subset ∣U∣
      _₂ : Subset ∣U∣
      _₃ : Subset ∣U∣

    open import Data.Vec.Properties using (≡-dec)
    open import Relation.Nullary.Decidable.Core using (_×-dec_)

  _≟³_ : DecidableEquality Triple
  ⟨ x₁ , x₂ , x₃ ⟩ ≟³ ⟨ y₁ , y₂ , y₃ ⟩
    with x₁ ≟ˢ y₁ | x₂ ≟ˢ y₂ | x₃ ≟ˢ y₃
  ...  | no x₁≢y₁ | _        | _        = no λ{ refl → x₁≢y₁ refl }
  ...  | yes _    | no x₂≢y₂ | _        = no λ{ refl → x₂≢y₂ refl }
  ...  | yes _    | yes _    | no x₃≢y₃ = no λ{ refl → x₃≢y₃ refl }
  ...  | yes refl | yes refl | yes refl = yes refl


  record DisjointTriple : Set where
    constructor _,_

    field base : Triple
    open Triple base public

    field
      disjoint :
        Disjoint _₁ _₂ ×
        Disjoint _₂ _₃ ×
        Disjoint _₁ _₃

  _≟ᵈ³_ : DecidableEquality DisjointTriple
  (x , x-disjoint₁₂ , x-disjoint₂₃ , x-disjoint₁₃) ≟ᵈ³ (y , y-disjoint₁₂ , y-disjoint₂₃ , y-disjoint₁₃)
    with x ≟³ y
  ...  | no  x≢y  = no λ{ refl → x≢y refl }
  ...  | yes refl = yes refl
```

```agda
  record DependencyModel : Set (suc (a ⊔ b)) where
    field
      Carrier : Set a
      _∈_     : DisjointTriple → Carrier → Set b

    _⋲_ : Triple → Carrier → Set b
    x ⋲ M = ∃[ disjoint ] (x , disjoint) ∈ M

```

We now define the (semi-)graphoid axioms, and define (semi-)graphoids to be dependency models that satisfy these axioms.
The following will be parameterized by the implementation of a dependency model.

```agda
  module _ (ℳ : DependencyModel {a} {b}) where
    open DependencyModel ℳ

    module _ (M : Carrier) where
      Symmetry : Set _
      Symmetry = ∀ {x y z}
        → ⟨ x , z , y ⟩ ⋲ M
        → ⟨ y , z , x ⟩ ⋲ M

      Decomposition : Set _
      Decomposition = ∀ {x y z w}
        → ⟨ x , z , y ∪ w ⟩ ⋲ M
        → ⟨ x , z , y     ⟩ ⋲ M

      WeakUnion : Set _
      WeakUnion = ∀ {x y z w}
        → ⟨ x , z , y ∪ w ⟩ ⋲ M
        → ⟨ x , z ∪ w , y ⟩ ⋲ M

      Contraction : Set _
      Contraction = ∀ {x y z w}
        → ⟨ x , z , y     ⟩ ⋲ M
        → ⟨ x , z ∪ y , w ⟩ ⋲ M
        → ⟨ x , z , y ∪ w ⟩ ⋲ M

      Intersection : Set _
      Intersection = ∀ {x y z w}
        → ⟨ x , z ∪ w , y ⟩ ⋲ M
        → ⟨ x , z ∪ y , w ⟩ ⋲ M
        → ⟨ x , z , y ∪ w ⟩ ⋲ M


    record IsSemiGraphoid (M : Carrier) : Set b where
      field
        symmetry      : Symmetry      M
        decomposition : Decomposition M
        weak-union    : WeakUnion     M
        contraction   : Contraction   M


    record IsGraphoid (M : Carrier) : Set b where
      field
        semi-graphoid : IsSemiGraphoid M
        intersection  : Intersection   M

      open IsSemiGraphoid semi-graphoid public


  record SemiGraphoid : Set (suc (a ⊔ b)) where
    field ℳ : DependencyModel {a} {b}
    open DependencyModel ℳ using (Carrier)
    open DependencyModel ℳ using (_∈_) public

    field
      M                : Carrier
      is-semi-graphoid : IsSemiGraphoid ℳ M

    open IsSemiGraphoid is-semi-graphoid public


  record Graphoid : Set (suc (a ⊔ b)) where
    field ℳ : DependencyModel {a} {b}
    open DependencyModel ℳ using (Carrier)
    open DependencyModel ℳ using (_∈_) public

    field
      M           : Carrier
      is-graphoid : IsGraphoid ℳ M

    open IsGraphoid is-graphoid public


  predicate-dependency-model : ∀ {b} → DependencyModel {b = b}
  predicate-dependency-model {b = b} =
    record
      { Carrier = Pred DisjointTriple b
      ; _∈_     = _∈ᵖ_
      }
```

```agda
  module Free where
```

The list of generators:

```agda
    _∈_ : DisjointTriple → List DisjointTriple → Set
    x ∈ G = {!!}

    semi-graphoid : List DisjointTriple → SemiGraphoid
    semi-graphoid G =
      record
        { ℳ =
          record
            { Carrier = List DisjointTriple
            ; _∈_ = _∈_
            }
        ; M = G
        ; is-semi-graphoid =
          record
            { symmetry      = {!!}
            ; decomposition = {!!}
            ; weak-union    = {!!}
            ; contraction   = {!!}
            }
        }
```
