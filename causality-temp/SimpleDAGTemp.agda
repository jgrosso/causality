module Causality.SimpleDAGTemp where

open import Causality.Util using (uncurry₃; _+′_)
open import Data.Fin as Fin using (Fin; Fin′)
import Data.Fin.Properties as Fin
import Data.Graph.Acyclic as DAG′
import Data.List as List
import Data.List.Relation.Unary.All as List hiding (map)
open import Data.Nat using (ℕ)
import Data.Nat.Properties as ℕ
open import Data.Product using (_×_; _,_; ∃; proj₁; uncurry)
import Data.Vec.Relation.Unary.All as Vec
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)


module SimpleDAG {size : ℕ} where

  Node : Set
  Node = Fin size


  record Edge : Set where
    constructor _⟶_
    field from : Node
    field to   : Node


  module _ where
    open import Data.Fin using (_ℕ-ℕ_; suc)
    open import Data.Nat using (_+_; _∸_)

    valid-edge : (from : Node) → Edge → Fin (size ℕ-ℕ suc from) → Set
    valid-edge from (from′ ⟶ to′) to =
      from′ ≡ from       ×
      to′   ≡ from +′ to


  record DAG : Set where
    field graph : DAG′.Graph Node Edge size

    field
      node-labels-correct :
        Vec.All (uncurry _≡_) (DAG′.nodes graph)

    field
      edge-labels-correct :
        List.All (uncurry₃ valid-edge) (DAG′.edges graph)

  module _ where
    open DAG′
    open import Data.Fin using (inject≤; suc; zero)

    build : ∀ {a b} {N : Set a} {E : Set b} {n}
      → Graph N E n
      → Graph Node Edge n
    build {N = N} {E} =
      foldr (Graph Node Edge)
            (λ c g → cmap (λ _ → inject≤ zero ?) id c & map (cmap suc (List.map (λ{ (to , i) → inject≤ (label c) ? ⟶ inject≤ (suc to) ? , i }))) g)
            ∅

    -- build : ∀ {a b} {N : Set a} {E : Set b} → DAG′.Graph N E size → DAG′.Graph Node Edge size
    -- build {E = E} =
    --   DAG′.map label-edges ∘
    --   DAG′.nmap proj₁ ∘ DAG′.number
    --   where
    --     label-edges : ∀ {n} → DAG′.Context Node E n → DAG′.Context Node Edge n
    --     label-edges c =
    --       let from : Node
    --           from = DAG′.label c

    --           label-edge : ∀ {n} → E × Fin n → Edge × Fin n
    --           label-edge = λ{ (_ , to) → (from ⟶ (inject≤ (from + to) {!!}) , to) }
    --       in DAG′.context
    --             from
    --             (List.map label-edge (DAG′.successors c))


  simple : DAG → Set
  simple = {!!}


  SimpleDAG : Set
  SimpleDAG = ∃ simple
