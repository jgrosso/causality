module Causality where

open import Data.Bool using (Bool)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin as Fin using (Fin; Fin′; toℕ)
open import Data.Fin.Properties as Fin using ()
open import Data.Fin.Subset using (Subset; ⁅_⁆; _∪_; _⊆_) renaming (_─_ to _∖_; ⊤ to complete-Subset; ⊥ to empty-Subset)
open import Data.Fin.Subset.Properties using (⊥⊆)
open import Data.List using ([]; _∷_; _∷ʳ_; List; filter; head; last; map; zip)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.All as List
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.List.Relation.Unary.Linked using (Linked)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe using (just; nothing)
open import Data.Nat as ℕ using (ℕ; _∸_; suc)
open import Data.Nat.Properties as ℕ using ()
open import Data.Product using (Σ; ∃; ∃-syntax; ∄-syntax; _,_; -,_; _×_; uncurry)
import Data.Vec.Relation.Unary.All as Vec
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Function using (_∘_; case_of_; flip)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; no; yes)




triples : ∀ {a} {A : Set a} → List A → List (A × A × A)
triples []               = []
triples (_ ∷ [])         = []
triples (_ ∷ _ ∷ [])     = []
triples (x ∷ xs@(y ∷ z ∷ _)) = (x , y , z) ∷ triples xs


⁅_⁆₂ : ∀ {n} → Fin n × Fin n → Subset n
⁅ i , j ⁆₂ = ⁅ i ⁆ ∪ ⁅ j ⁆


inject< : ∀ {n} {j : Fin n} (i : Fin n) → i Fin.< j → Fin′ j
inject< = Fin.inject≤ ∘ Fin.strengthen


toℕ-inject< : ∀ {n} {j : Fin n} i (i<j : i Fin.< j)
  → Fin.toℕ (inject< i i<j) ≡ Fin.toℕ i
toℕ-inject< i i<j
  rewrite Fin.toℕ-inject≤ (Fin.strengthen i) i<j
        | Fin.toℕ-strengthen i
  = refl
module Causality where
