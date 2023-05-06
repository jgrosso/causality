---
title: Causality.Data.Graphoid
---

Definitions and proofs about (semi-)graphoids.

<details>
<summary>Some initial bookkeeping.</summary>
<div>
```agda
{-# OPTIONS --without-K --safe #-}

module Causality.Data.Graphoid where

open import Causality.Data.Fin.Subset                                                                                                          renaming (_≟_ to _≟ˢ_; Disjoint-∪⁻ to ⊥-∪⁻; Disjoint-∪⁺ to ⊥-∪⁺; Disjoint-swap to ⊥-swap; Disjoint-sym to ⊥-sym)
open import Causality.Data.Product
open import Data.Fin                                    using (Fin)
open import Data.Fin.Subset                             using (Subset; _∪_; ⁅_⁆; _∈_)                                                          renaming (⊥ to ∅)
open import Data.Fin.Subset.Properties                  using (∪-comm; ∪-idem; Empty-unique; x∈⁅x⁆; x∈⁅y⁆⇒x≡y; x∈p∩q⁻; x∈p∪q⁻; x∈p∩q⁺; x∈p∪q⁺)
open import Data.List                                   using (List; map)
open import Data.List.Membership.Propositional          using ()                                                                               renaming (_∈_ to _∈ˡ_)
open import Data.Nat                                    using (ℕ; suc)
open import Data.Product                                using (∃-syntax; Σ-syntax; _×_; -,_)                                                   renaming (_,_ to _⸴_)
open import Data.Sum                                    using (_⊎_; inj₁; inj₂)
open import Function                                    using (_∘_; flip)
open import Level                                       using (Level; 0ℓ)                                                                      renaming (suc to ↑)
open import Relation.Binary.Definitions                 using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Relation.Nullary                            using (¬_; contradiction; no; yes)
open import Relation.Unary                              using (Pred)                                                                           renaming (_∈_ to _∈ᵖ_; _⊂_ to _⊂ᵖ_)

private
  variable
    a : Level
```
</div>
</details>

We begin by formalizing the following definition on pg. 11 of [@geiger]:

> A *dependency model* $M$ over a finite set of elements $U$ is any subset of triplets $(X, Z, Y)$ where $X$, $Y$, and $Z$ are disjoint subsets of $U$.

We will parameterize our definitions by the cardinality $|U|$ of our universe of discourse. We will represent the universe itself by a finite set $U$ (i.e. with cardinality $|U|$).

```agda
module IntersectionalGraphoid (∣U∣ : ℕ) where
  U : Set _
  U = Fin ∣U∣
```

We define (disjoint) triples, noting that they have decidable equality:

```agda
  infix 4 _,_,_
  infix 3 _⨾_,_,_

  record Triple : Set where
    constructor _,_,_
    field
      _₁ : Subset ∣U∣
      _₂ : Subset ∣U∣
      _₃ : Subset ∣U∣

    open import Data.Vec.Properties using (≡-dec)
    open import Relation.Nullary.Decidable.Core using (_×-dec_)


  _≟³_ : DecidableEquality Triple
  (x₁ , x₂ , x₃) ≟³ (y₁ , y₂ , y₃)
    with x₁ ≟ˢ y₁ | x₂ ≟ˢ y₂ | x₃ ≟ˢ y₃
  ...  | no x₁≢y₁ | _        | _        = no λ{ refl → x₁≢y₁ refl }
  ...  | yes _    | no x₂≢y₂ | _        = no λ{ refl → x₂≢y₂ refl }
  ...  | yes _    | yes _    | no x₃≢y₃ = no λ{ refl → x₃≢y₃ refl }
  ...  | yes refl | yes refl | yes refl = yes refl


  record DisjointTriple : Set where
    constructor _⨾_,_,_

    field base : Triple
    open Triple base public

    field
      ₁⊥₂ : Disjoint _₁ _₂
      ₂⊥₃ : Disjoint _₂ _₃
      ₁⊥₃ : Disjoint _₁ _₃


  module _ where
    open DisjointTriple

    _≟ᵈ³_ : DecidableEquality DisjointTriple
    x ≟ᵈ³ y
      with base x ≟³ base y
    ...  | no  x≢y  = no λ{ refl → x≢y refl }
    ...  | yes refl = yes refl
```

We define a dependency model as per [@geiger] (pg. 10):

> A *dependency model* is as a truth assignment rule for the predicate $I(X, Z, Y)$\dots.

```agda

  DependencyModel : ∀ a → Set _
  DependencyModel = Pred DisjointTriple

  _⟨_⟩ : ∀ {a} → DependencyModel a → Triple → Set _
  I ⟨ triple ⟩ = ∃[ ₁⊥₂ ₂⊥₃ ₁⊥₃ ] (triple ⨾ ₁⊥₂ , ₂⊥₃ , ₁⊥₃) ∈ᵖ I
    where open DisjointTriple
```

We now define the (semi-)graphoid axioms, and define (semi-)graphoids to be dependency models that satisfy these axioms.
The following will be parameterized by the implementation of a dependency model.

```agda
  module _ (I : DependencyModel a) where
    Symmetry : Set _
    Symmetry = ∀ {x y z}
      → I ⟨ x , z , y ⟩
      → I ⟨ y , z , x ⟩

    Decomposition : Set _
    Decomposition = ∀ {x y z w}
      → I ⟨ x , z , y ∪ w ⟩
      → I ⟨ x , z , y     ⟩

    WeakUnion : Set _
    WeakUnion = ∀ {x y z w}
      → Disjoint y w
      → I ⟨ x , z     , y ∪ w ⟩
      → I ⟨ x , z ∪ w , y     ⟩

    Contraction : Set _
    Contraction = ∀ {x y z w}
      → I ⟨ x , z     , y     ⟩
      → I ⟨ x , z ∪ y , w     ⟩
      → I ⟨ x , z     , y ∪ w ⟩

    Intersection : Set _
    Intersection = ∀ {x y z w}
      → I ⟨ x , z ∪ w , y     ⟩
      → I ⟨ x , z ∪ y , w     ⟩
      → I ⟨ x , z     , y ∪ w ⟩
```

<details>
<summary>Why does `WeakUnion` require `Disjoint y w`?</summary>
<div>
Neither [@geiger] nor [@pearl] explicitly requires that $y$ and $w$ be disjoint. However, if this were not the case, we can rule out the vast majority of "useful" semigraphoids. For example, we can always let $w = y$; since the resulting triple must be disjoint, this implies $y = ∅$. Here is a formal proof of this fact:

```agda
    module WeakUnionDisjointness where
      WeakUnion′ : Set _
      WeakUnion′ = ∀ {x z y w}
        → I ⟨ x , z     , y ∪ w ⟩
        → I ⟨ x , z ∪ w , y     ⟩

      silly : ∀ {x z y}
        → WeakUnion′
        → I ⟨ x , z , y ⟩
        → y ≡ ∅
      silly {x} {z} {y} weak-union I⟨x,z,y⟩ = Empty-unique λ where
        (𝑦 ⸴ 𝑦∈y) →
          let w : Subset ∣U∣
              w = ⁅ 𝑦 ⁆

              y∪w≡y : y ∪ w ≡ y
              y∪w≡y = T⊆S⇒S∪T≡S λ x∈⁅𝑦⁆ → Eq.subst (_∈ _) (Eq.sym (x∈⁅y⁆⇒x≡y _ x∈⁅𝑦⁆)) 𝑦∈y

              I⟨x,z,y⟩⇒I⟨x,z∪w,y⟩ : I ⟨ x , z , y ⟩ → I ⟨ x , z ∪ w , y ⟩
              I⟨x,z,y⟩⇒I⟨x,z∪w,y⟩ =
                Eq.subst (λ ∙ → I ⟨ x , z , ∙ ⟩ → I ⟨ x , z ∪ w , y ⟩)
                  y∪w≡y
                  weak-union

              (_ ⸴ z∪⁅𝑦⁆⊥y ⸴ _) = I⟨x,z,y⟩⇒I⟨x,z∪w,y⟩ I⟨x,z,y⟩
          in contradiction (-, x∈p∩q⁺ (x∈p∪q⁺ (inj₂ (x∈⁅x⁆ _)) ⸴ 𝑦∈y)) z∪⁅𝑦⁆⊥y
```
</div>
</details>

```agda
    record IsSemiGraphoid : Set a where
      field
        symmetry      : Symmetry
        decomposition : Decomposition
        weak-union    : WeakUnion
        contraction   : Contraction


    record IsGraphoid : Set a where
      field
        semi-graphoid : IsSemiGraphoid
        intersection  : Intersection

      open IsSemiGraphoid semi-graphoid public


  record SemiGraphoid : Set (↑ a) where
    field
      I                : DependencyModel a
      is-semi-graphoid : IsSemiGraphoid I

    open IsSemiGraphoid is-semi-graphoid public


  record Graphoid : Set (↑ a) where
    field
      I           : DependencyModel a
      is-graphoid : IsGraphoid I

    open IsGraphoid is-graphoid public
```

We can generate a free semi-graphoid, which will be convenient when we construct example semi-graphoids.

```agda
  module FreeSemiGraphoid where
    module _ where
      private
        variable
          I       : List DisjointTriple
          x y z w : Subset ∣U∣
          x⊥y     : Disjoint x y
          x⊥z     : Disjoint x z
          x⊥w     : Disjoint x w
          y⊥x     : Disjoint y x
          y⊥z     : Disjoint y z
          z⊥x     : Disjoint z x
          z⊥y     : Disjoint z y
          x⊥y∪w   : Disjoint x (y ∪ w)
          x⊥z∪w   : Disjoint x (z ∪ w)
          x⊥z∪y   : Disjoint x (z ∪ y)
          z⊥y∪w   : Disjoint z (y ∪ w)
          z∪w⊥y   : Disjoint (z ∪ w) y
          z∪y⊥w   : Disjoint (z ∪ y) w

      private
        _∋_ : List DisjointTriple → DisjointTriple → Set
        _∋_ = flip _∈ˡ_

      data _⟨_⟩ᶠ : List DisjointTriple → DisjointTriple → Set where
        ⟨⟩-generator : ∀ {x,z,y}
          → I ∋ x,z,y
          → I ⟨ x,z,y ⟩ᶠ

        ⟨⟩-symmetry :
            I ⟨ x , z , y         ⨾ x⊥z   , z⊥y   , x⊥y ⟩ᶠ
          → I ⟨ y , z , x         ⨾ y⊥z   , z⊥x   , y⊥x ⟩ᶠ

        ⟨⟩-decomposition :
            I ⟨ x , z , y ∪ w     ⨾ x⊥z   , z⊥y∪w , x⊥y∪w ⟩ᶠ
          → I ⟨ x , z , y         ⨾ x⊥z   , z⊥y   , x⊥y   ⟩ᶠ

        ⟨⟩-weak-union :
            I ⟨ x , z     , y ∪ w ⨾ x⊥z   , z⊥y   , x⊥y∪w ⟩ᶠ
          → I ⟨ x , z ∪ w , y     ⨾ x⊥z∪w , z∪w⊥y , x⊥y   ⟩ᶠ

        ⟨⟩-contraction :
            I ⟨ x , z     , y     ⨾ x⊥z   , z⊥y   , x⊥y   ⟩ᶠ
          → I ⟨ x , z ∪ y ,     w ⨾ x⊥z∪y , z∪y⊥w , x⊥w   ⟩ᶠ
          → I ⟨ x , z     , y ∪ w ⨾ x⊥z   , z⊥y∪w , x⊥y∪w ⟩ᶠ


    generate : List DisjointTriple → SemiGraphoid
    generate G =
      record
        { I                = I
        ; is-semi-graphoid =
          record
            { symmetry      = symmetry
            ; decomposition = decomposition
            ; weak-union    = weak-union
            ; contraction   = contraction
            }
        }
      where
      I : DependencyModel _
      I = G ⟨_⟩ᶠ

      symmetry : Symmetry I
      symmetry (x⊥z ⸴ z⊥y ⸴ x⊥y ⸴ I⟨x,z,y⟩) =
          ⊥-sym z⊥y
        ⸴ ⊥-sym x⊥z
        ⸴ ⊥-sym x⊥y
        ⸴ ⟨⟩-symmetry I⟨x,z,y⟩

      decomposition : Decomposition I
      decomposition (x⊥z ⸴ z⊥y∪w ⸴ x⊥y∪w ⸴ I⟨x,z,y∪w⟩) =
          x⊥z
        ⸴ ⊥-sym (⊥-∪⁻ (⊥-sym z⊥y∪w))
        ⸴ ⊥-sym (⊥-∪⁻ (⊥-sym x⊥y∪w))
        ⸴ ⟨⟩-decomposition I⟨x,z,y∪w⟩

      weak-union : WeakUnion I
      weak-union y⊥w (x⊥z ⸴ z⊥y∪w ⸴ x⊥y∪w ⸴ I⟨x,z,y∪w⟩) =
          ⊥-∪⁺ x⊥z x⊥w
        ⸴ z∪w⊥y
        ⸴ ⊥-sym (⊥-∪⁻ (⊥-sym x⊥y∪w))
        ⸴ ⟨⟩-weak-union I⟨x,z,y∪w⟩
        where
        x⊥w = ⊥-sym (⊥-∪⁻ (Eq.subst (λ ∙ → Disjoint ∙ _) (∪-comm _ _) (⊥-sym x⊥y∪w)))

        z∪w⊥y = Eq.subst (λ ∙ → Disjoint ∙ _) (∪-comm _ _)
          (⊥-sym (⊥-swap y⊥w (⊥-sym z⊥y∪w)))

      contraction : Contraction I
      contraction (x⊥z ⸴ z⊥y ⸴ x⊥y ⸴ I⟨x,z,y⟩) (x⊥z∪y ⸴ z∪y⊥w ⸴ x⊥w ⸴ I⟨x,z∪y,w⟩) =
          x⊥z
        ⸴ ⊥-swap z⊥y z∪y⊥w
        ⸴ x⊥y∪w
        ⸴ ⟨⟩-contraction I⟨x,z,y⟩ I⟨x,z∪y,w⟩
        where
        x⊥y∪w = Eq.subst (λ ∙ → Disjoint _ ∙) (∪-comm _ _) (⊥-∪⁺ x⊥w x⊥y)
```
