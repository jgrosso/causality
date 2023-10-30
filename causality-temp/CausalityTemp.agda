open import Data.Bool using (Bool)
open import Data.Graph.Acyclic using (_[_]; successors) renaming (Graph to DAG; nodes to indexed-nodes) hiding (∅; head; node)
open import Data.List using (List; filter; head; last)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Membership.DecSetoid
import Data.List.Membership.Setoid
open import Data.Maybe using (just)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; ∃; ∃-syntax; ∄-syntax; _,_; _×_; proj₂)
open import Data.Tree.AVL.Sets using (⟨Set⟩; fromList; insert; singleton; toList; union)
open import Data.Unit using (⊤)
open import Data.Vec using (Vec) renaming (toList to Vec→List)
import Data.Vec.Membership.Setoid
open import Function using (_∘_)
open import Level using (Level)
open import Relation.Binary using (Setoid; StrictPartialOrder; StrictTotalOrder)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)



module Causality
  {a b ℓ₁ ℓ₂ : Level}
  (⟨Node⟩ : StrictTotalOrder a ℓ₁ ℓ₂)
  where


pairs : ∀ {A} → List A → List (A × A)
pairs = {!!}


module _ {a ℓ₁ ℓ₂} {A : StrictTotalOrder a ℓ₁ ℓ₂} where

  open Data.List.Membership.DecSetoid (StrictTotalOrder.decSetoid A) using (_∉?_)


  infix 4 _⊆_

  _⊆_ : ⟨Set⟩ A → ⟨Set⟩ A → Set _
  S ⊆ T = union _ S T ≡ T


  infix 5 _∖_

  _∖_ : ⟨Set⟩ A → ⟨Set⟩ A → ⟨Set⟩ A
  S ∖ T = fromList _ (filter (_∉? toList _ T) (toList _ S))


  Vec→⟨Set⟩ : ∀ {n} → Vec _ n → ⟨Set⟩ A
  Vec→⟨Set⟩ = fromList _ ∘ Vec→List


open module Node = Data.Tree.AVL.Sets (⟨Node⟩) using (empty)

open Data.Vec.Membership.Setoid (StrictTotalOrder.Eq.setoid ⟨Node⟩) using (_∈_)


Node : Set _
Node = StrictTotalOrder.Carrier ⟨Node⟩


CausalGraph : ℕ → Set _
CausalGraph = DAG Node ⊤


nodes : ∀ {n} → CausalGraph n → Vec Node n
nodes = Data.Vec.map proj₂ ∘ indexed-nodes


module Graph {n : ℕ} (G : CausalGraph n) where

  private
    V : ⟨Set⟩ ⟨Node⟩
    V = Vec→⟨Set⟩ (nodes G)

  private
    ⁅_,_⁆ : Node → Node → ⟨Set⟩ ⟨Node⟩
    ⁅ i , j ⁆ = insert _ j (singleton _ i)


  ConditioningSet : Node → Node → Set _
  ConditioningSet i j = ∃[ C ] C ⊆ V ∖ ⁅ i , j ⁆


  ∅ : ∀ {i j} → ConditioningSet i j
  ∅ = empty , refl


  module _ where

    open Data.List.Membership.Setoid (StrictTotalOrder.Eq.setoid ⟨Node⟩) using () renaming (_∈_ to _∈ˡ_)


    _∈-edges : (Node × Node) → Set _
    (i , j) ∈-edges = j ∈ˡ {!successors (G [ i ])!}


  _⟶_ : Node → Node → Set _
  from ⟶ to = ∃[ p ]
    All (_∈ nodes G) p ×
    head p ≡ just from ×
    last p ≡ just to ×
    All _∈-edges (pairs p)


  unblocked?_∣_ : ∀ {i j} → i ⟶ j → ConditioningSet i j → Set _
  unblocked? p ∣ C = {!!}


  _⫫_∣_ : (i j : Node) → ConditioningSet i j → Set _
  i ⫫ j ∣ C = ∄[ p ] unblocked? p ∣ C


  _⫫_ : Node → Node → Set _
  A ⫫ B = A ⫫ B ∣ ∅
