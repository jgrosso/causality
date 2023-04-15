---
title: Causality.Data.Graph
---

Definitions and proofs about (directed, acyclic, simple, etc.) graphs.

```agda
{-# OPTIONS --without-K --safe #-}

module Causality.Data.Graph where

open import Data.Fin using (Fin)
open import Data.List using (List; filter)
open import Data.List.Relation.Unary.Linked using (Linked)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as Unique
open import Data.Nat using (ℕ)
open import Data.Product using (∃; _×_; _,_) renaming (proj₁ to _₁)
open import Data.Sum using (_⊎_)
open import Function using (_∘_; flip)
open import Relation.Unary using (Decidable)

record DirectedMultigraph : Set where
  field |V| : ℕ

  V : Set
  V = Fin |V|

  Edge : Set
  Edge = V × V

  field E : List Edge

  _∃⟶_ : (i j : V) → Set
  i ∃⟶ j = (i , j) ∈ E
    where open import Data.List.Membership.Propositional using (_∈_)

  _∃⟵_ : (i j : V) → Set
  _∃⟵_ = flip _∃⟶_

  _∃——_ : (i j : V) → Set
  i ∃—— j = i ∃⟶ j ⊎ j ∃⟶ i

  DirectedPath : List V → Set
  DirectedPath = Linked _∃⟶_

  UndirectedPath : List V → Set
  UndirectedPath = Linked _∃——_

  acyclic-path : ∃ DirectedPath → Set
  acyclic-path = Unique ∘ _₁

  FilterEdges : ∀ {p a} → Set a → Set _
  FilterEdges {p} Self = {P : Edge → Set p} → Decidable P → Self

  filter-edges : ∀ {p} → FilterEdges {p} _
  filter-edges P? = record
    { |V| = |V|
    ;  E  = filter P? E
    }


module _ {g : DirectedMultigraph} where

  open import Data.List.Relation.Unary.Any.Properties using (filter⁻)
  open DirectedMultigraph
  open Linked
  open import Relation.Unary using (_⊆_)

  filter-edges-removes-paths : ∀ {p} {P : Edge g → Set p} {P? : Decidable P}
    → DirectedPath (filter-edges g P?) ⊆ DirectedPath g
  filter-edges-removes-paths []       = []
  filter-edges-removes-paths [-]      = [-]
  filter-edges-removes-paths (p ∷ p′) = filter⁻ _ p ∷ filter-edges-removes-paths p′


record DirectedGraph : Set where
  field base : DirectedMultigraph
  open DirectedMultigraph base hiding (filter-edges) public

  field simple : Unique E

  filter-edges : ∀ {p} → FilterEdges {p} _
  filter-edges f = record
    { base   = DirectedMultigraph.filter-edges base f
    ; simple = Unique.filter⁺ f simple
    }


record DAG : Set where
  field base : DirectedGraph
  open DirectedGraph base hiding (base; filter-edges) public

  field acyclic : (p : ∃ DirectedPath) → acyclic-path p

  filter-edges : ∀ {p} → FilterEdges {p} _
  filter-edges f = record
    { base    = DirectedGraph.filter-edges base f
    ; acyclic = acyclic′
    }
    where
    acyclic′ : _
    acyclic′ (p , linked) = acyclic (p , filter-edges-removes-paths linked)
```
