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
open import Causality.Data.Fin.Subset
open import Data.Fin using (Fin; #_)
open import Data.Fin.Properties using (_≟_)
open import Data.Fin.Subset using (Subset; _∪_; _⊆_; ⁅_⁆; ∣_∣) renaming (⊥ to ∅)
open import Data.Fin.Subset.Properties using (x∈p∩q⁻; x∈⁅y⁆⇒x≡y)
open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; _≤_; s≤s; z≤n)
open import Data.Product using (∃-syntax; Σ-syntax; Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec)
import Data.Vec as Vec
open import Function using (case_of_)
import Induction.WellFounded as Wf
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable.Core using (False; toWitnessFalse)
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

  open DisjointTriple
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

We now define the (semi-)graphoid axioms, and define (semi-)graphoids to be dependency models that satisfy these axioms.

```agda
  module _ (M : DependencyModel) where

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
      symmetry      : Symmetry      M
      decomposition : Decomposition M
      weak-union    : WeakUnion     M
      contraction   : Contraction   M

  open IsSemiGraphoid


  record SemiGraphoid : Set where
    field
      M                : DependencyModel
      is-semi-graphoid : IsSemiGraphoid M

    open IsSemiGraphoid is-semi-graphoid public

  open SemiGraphoid


  record IsGraphoid (M : DependencyModel) : Set where
    field
      semi-graphoid : IsSemiGraphoid M
      intersection  : Intersection   M

    open IsSemiGraphoid semi-graphoid public

  open IsGraphoid


  record Graphoid : Set where
    field
      M           : DependencyModel
      is-graphoid : IsGraphoid M

    open IsGraphoid is-graphoid public

  open Graphoid


module _ where
  private
    |U| : ℕ
    |U| = 4

  open module G = Graphoid |U| hiding (⟨_,_,_⟩)

  private
    x y z w : Subset |U|
    x = ⁅ # 0 ⁆
    y = ⁅ # 1 ⁆
    z = ⁅ # 2 ⁆
    w = ⁅ # 3 ⁆

    disjoint : ∀ m n {m≢n : False (m ≟ n)} → Disjoint {n = |U|} ⁅ m ⁆ ⁅ n ⁆
    disjoint m n {m≢n} (_ , x∈⁅m⁆∩⁅n⁆)
      with x∈p∩q⁻ _ _ x∈⁅m⁆∩⁅n⁆
    ...  | x∈⁅m⁆ , x∈⁅n⁆
           with x∈⁅y⁆⇒x≡y _ x∈⁅m⁆ | x∈⁅y⁆⇒x≡y _ x∈⁅n⁆
    ...       | refl              | refl = toWitnessFalse m≢n refl

    M₁ : G.DisjointTriple
    M₁ = G.⟨ x , z , y ⟩ , disjoint (# 0) (# 2) , disjoint (# 2) (# 1) , disjoint (# 0) (# 1)

    M₂ : G.DisjointTriple
    M₂ = G.⟨ y , z , x ⟩ , disjoint (# 1) (# 2) , disjoint (# 2) (# 0) , disjoint (# 1) (# 0)

    M₃ : G.DisjointTriple
    M₃ = G.⟨ x , z , ∅ ⟩ , disjoint (# 0) (# 2) , Disjoint-∅ʳ z , Disjoint-∅ʳ x

    M₄ : G.DisjointTriple
    M₄ = G.⟨ ∅ , z , x ⟩ , disjoint (# 0) (# 2) , Disjoint-∅ʳ z , Disjoint-∅ʳ x

    M : List G.DisjointTriple
    M = [ M₁ ] ++ [ M₂ ] ++ [ M₃ ] ++ [ M₄ ]

    ⟨x,y,z⟩∈M⇒∣x∣≤1 : ∀ {x y z} → G.⟨ x , y , z ⟩ ∈ M → ∣ x ∣ ≡ 0 ⊎ ∣ x ∣ ≡ 1
    ⟨x,y,z⟩∈M⇒∣x∣≤1 (_ , here refl)                         = inj₂ refl
    ⟨x,y,z⟩∈M⇒∣x∣≤1 (_ , there (here refl))                 = inj₂ refl
    ⟨x,y,z⟩∈M⇒∣x∣≤1 (_ , there (there (here refl)))         = inj₂ refl
    ⟨x,y,z⟩∈M⇒∣x∣≤1 (_ , there (there (there (here refl)))) = inj₁ refl

    ⟨x,y,z⟩∈M⇒∣y∣≡1 : ∀ {x y z} → G.⟨ x , y , z ⟩ ∈ M → ∣ y ∣ ≡ 1
    ⟨x,y,z⟩∈M⇒∣y∣≡1 (_ , here refl)                         = refl
    ⟨x,y,z⟩∈M⇒∣y∣≡1 (_ , there (here refl))                 = refl
    ⟨x,y,z⟩∈M⇒∣y∣≡1 (_ , there (there (here refl)))         = refl
    ⟨x,y,z⟩∈M⇒∣y∣≡1 (_ , there (there (there (here refl)))) = refl

    ⟨x,y,z⟩∈M⇒∣z∣≤1 : ∀ {x y z} → G.⟨ x , y , z ⟩ ∈ M → ∣ z ∣ ≡ 0 ⊎ ∣ z ∣ ≡ 1
    ⟨x,y,z⟩∈M⇒∣z∣≤1 (_ , here refl)                         = inj₂ refl
    ⟨x,y,z⟩∈M⇒∣z∣≤1 (_ , there (here refl))                 = inj₂ refl
    ⟨x,y,z⟩∈M⇒∣z∣≤1 (_ , there (there (here refl)))         = inj₁ refl
    ⟨x,y,z⟩∈M⇒∣z∣≤1 (_ , there (there (there (here refl)))) = inj₂ refl

  symmetry-M : Symmetry M
  symmetry-M (_ , here refl)                         = DisjointTriple.disjoint M₂ , there (here refl)
  symmetry-M (_ , there (here refl))                 = DisjointTriple.disjoint M₁ , here refl
  symmetry-M (_ , there (there (here refl)))         = DisjointTriple.disjoint M₄ , there (there (there (here refl)))
  symmetry-M (_ , there (there (there (here refl)))) = DisjointTriple.disjoint M₃ , there (there (here refl))

  decomposition-M : Decomposition M
  decomposition-M {x = x} {y = y} {z = z} {w = w} ∈M
    with ⟨x,y,z⟩∈M⇒∣x∣≤1 ∈M | ⟨x,y,z⟩∈M⇒∣y∣≡1 ∈M | ⟨x,y,z⟩∈M⇒∣z∣≤1 ∈M
  ...  | _                 | g           | (inj₁ ∣y∪w∣≡0) = {!∣x∣≡0⇒x≡∅ ∣y∪w∣≡0!}
  ...  | _                 | g           | (inj₂ ∣y∪w∣≡1) = {!∣x∣≡0⇒x≡∅ ∣y∪w∣≡1!}

  -- ⟨_,_,_⟩ : (x : Subset |U|) (y : Subset |U|) (z : Subset |U|) {∣x∣≡1 : True (∣ x ∣ ≟ 1)} {∣y∣≡1 : True (∣ y ∣ ≟ 1)} {∣z∣≡1 : True (∣ z ∣ ≟ 1)} → DisjointTriple
  -- ⟨ x , y , z ⟩ {∣x∣≡1} {∣y∣≡1} {∣z∣≡1}
  --   with toWitness ∣x∣≡1 | toWitness ∣y∣≡1 | toWitness ∣z∣≡1 | x | y | z
  -- ...  | ∣x∣≡1           | ∣y∣≡1           | ∣z∣≡1           | x | y | z =
  --   G.⟨ x , y , z ⟩ , (λ x₂ → {!!}) , {!!} , {!!}

  semi-graphoid-⊂-graphoid :
    Σ[ semi-graphoid ∈ SemiGraphoid ]
      ¬ IsGraphoid (SemiGraphoid.M semi-graphoid)
  semi-graphoid-⊂-graphoid =
    record
      { M                = M
      ; is-semi-graphoid =
        record
          { symmetry      = symmetry-M
          ; decomposition = decomposition-M
          ; weak-union    = {!!}
          ; contraction   = {!!}
          }
      } ,
    λ is-graphoid → {!!}
    where open import Data.Fin.Subset.Properties using (x∈p∪q⁻)
  ```
