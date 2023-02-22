Definitions and proofs about (semi-)graphoids.

::
  module Causality.Data.Graphoid where

Import some libraries, so that we can use them below:

::
  open import Causality.Data.Fin.Subset
  open import Data.Fin using (Fin)
  open import Data.Fin.Subset using (Subset; _∪_; _⊆_) renaming (⊥ to ∅)
  open import Data.List using (List)
  open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
  open import Data.Nat using (ℕ)
  open import Data.Product using (∃-syntax; Σ; _×_; proj₁)

The definition of a graphoid is parameterized by a finite universe ([Pearl1987], pg. 13).
We thus parameterize our development by the cardinality :math:`|U|` of the universe in question.

::
  module Graphoid (|U| : ℕ) where

We will represent the universe WLOG as a finite set :math:`U` (namely, with cardinality :math`|U|`).

::
    U : Set
    U = Fin |U|

::
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


    DependencyModel : Set
    DependencyModel = Σ (List DisjointTriple) Unique

    _∈_ : Triple → DependencyModel → Set
    ⟨ x , y , z ⟩ ∈ I = ∃[ h ] (⟨ x , y , z ⟩ , h) ∈ˡ proj₁ I
      where open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ˡ_)


    module _ (I : DependencyModel) where

      TrivialIndependence : Set
      TrivialIndependence = ∀ {x z}
        → ⟨ x , z , ∅ ⟩ ∈ I

      Symmetry : Set
      Symmetry = ∀ {x y z}
        → ⟨ x , z , y ⟩ ∈ I
        → ⟨ y , z , x ⟩ ∈ I

      Decomposition : Set
      Decomposition = ∀ {x y z w}
        → ⟨ x , z , y ∪ w ⟩ ∈ I
        → ⟨ x , z , y ⟩ ∈ I

      WeakUnion : Set
      WeakUnion = ∀ {x y z w}
        → ⟨ x , z , y ∪ w ⟩ ∈ I
        → ⟨ x , z ∪ w , y ⟩ ∈ I

      Contraction : Set
      Contraction = ∀ {x y z w}
        → ⟨ x , z , y ⟩ ∈ I
        → ⟨ x , z ∪ y , w ⟩ ∈ I
        → ⟨ x , z , y ∪ w ⟩ ∈ I

      Intersection : Set
      Intersection = ∀ {x y z w}
        → ⟨ x , z ∪ w , y ⟩ ∈ I
        → ⟨ x , z ∪ y , w ⟩ ∈ I
        → ⟨ x , z , y ∪ w ⟩ ∈ I

      StrongIntersection : Set
      StrongIntersection = ∀ {x y z w}
        → ⟨ x , z ∪ w , y ⟩ ∈ I
        → ⟨ x , z ∪ y , w ⟩ ∈ I
        → z ⊆ y
        → ⟨ x , z , y ∪ w ⟩ ∈ I


    record IsSemiGraphoid (I : DependencyModel) : Set where
      field
        trivial-independence : TrivialIndependence I
        symmetry             : Symmetry            I
        decomposition        : Decomposition       I
        weak-union           : WeakUnion           I
        contraction          : Contraction         I


    record SemiGraphoid : Set where
      field
        I                : DependencyModel
        is-semi-graphoid : IsSemiGraphoid I

      open IsSemiGraphoid is-semi-graphoid public


    record IsGraphoid (I : DependencyModel) : Set where
      field
        semi-graphoid : IsSemiGraphoid I
        intersection  : Intersection   I

      open IsSemiGraphoid semi-graphoid public


    record Graphoid : Set where
      field
        I           : DependencyModel
        is-graphoid : IsGraphoid I

      open IsGraphoid is-graphoid public

.. [Pearl1987] P. Judea and A. Paz, “Graphoids: a graph-based logic for reasoning about relevance relations. UCLA Computer Science Department Technical Report 850038,” Advances in Artificial Intelligence-II, North-Holland Publishing Co, 1987.
