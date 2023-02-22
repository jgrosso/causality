module Causality.Data.Fin.Subset where

open import Data.Fin using (Fin)
open import Data.Fin.Subset using (Subset; _∩_; _∪_; _⊆_; ⊤; ⁅_⁆; Empty) renaming (_─_ to _∖_)
open import Data.Product using (_×_; _,_)

Disjoint : ∀ {n} → Subset n → Subset n → Set
Disjoint S T = Empty (S ∩ T)

_⊆∖_ : ∀ {n} → Subset n → Subset n → Set
S ⊆∖ T = S ⊆ (⊤ ∖ T)

⁅_⁆₂ : ∀ {n} → Fin n × Fin n → Subset n
⁅ i , j ⁆₂ = ⁅ i ⁆ ∪ ⁅ j ⁆
