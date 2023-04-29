---
title: Causality.Function
---

Definitions and proofs about functions.

```agda
{-# OPTIONS --without-K --safe #-}

module Causality.Function where

open import Algebra.Bundles using (Magma; Monoid; Semigroup)
open import Data.Product using (_,_)
open import Function using (_∘_; _↠_; _↣_; _↩_; const; Injection; Injective; LeftInverse; mk↠; Surjection)
open import Level using (Level)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; _→-setoid_)

private
  variable
    a b c ℓ : Level

module _ where
  private
    variable
      A : Set a
      B : Set b
      C : Set c

  module _ (↣ : B ↣ C) where
    open Injection ↣ using () renaming (injective to f-injective; to to f)

    ↣-monic : {g h : A → B}
      → f ∘ g ≗ f ∘ h
      → g ≗ h
    ↣-monic = f-injective ∘_


  module _ (↠ : A ↠ B) where
    open Surjection ↠ using () renaming (surjective to f-surjective; to to f; to⁻ to f⁻¹)

    ↠-epic : {g h : B → C}
      → g ∘ f ≗ h ∘ f
      → g ≗ h
    ↠-epic gf≡hf x
      with (f⁻¹[x] , Eq.refl) ← f-surjective x
      = gf≡hf f⁻¹[x]


  module _ (↩ : A ↩ B) where
    open LeftInverse ↩ using () renaming (to to f; from to f⁻¹; inverseˡ to f-inverseˡ)

    ↩-epic : {g h : B → C}
      → g ∘ f ≗ h ∘ f
      → g ≗ h
    ↩-epic = ↠-epic (mk↠ λ y → f⁻¹ y , f-inverseˡ y)


module Pointwise {A : Set a} {B : Set b} (_≈_ : Rel B ℓ) where
  _≈̊_ : Rel (A → B) _
  f ≈̊ g = ∀ x → f x ≈ g x


module _ {A : Set a} (B-magma : Magma b ℓ) where
  open Magma B-magma using (_≈_; _∙_; ∙-cong; refl; sym; trans) renaming (Carrier to B)

  open Pointwise {A = A} _≈_

  ←-magma : Magma _ _
  ←-magma =
    record
      { Carrier = A → B
      ; _≈_     = _≈̊_
      ; _∙_     = λ f g x → f x ∙ g x
      ; isMagma =
        record
          { isEquivalence =
            record
              { refl  = λ _ → refl
              ; sym   = sym ∘_
              ; trans = λ f≈̊g g≈̊h x → trans (f≈̊g x) (g≈̊h x)
              }
          ; ∙-cong = λ f≈̊g g≈̊h x → ∙-cong (f≈̊g x) (g≈̊h x)
          }
      }


module _ {A : Set a} (B-semigroup : Semigroup b ℓ) where
  open Semigroup B-semigroup using (_≈_; _∙_; assoc; magma) renaming (Carrier to B)

  ←-semigroup : Semigroup _ _
  ←-semigroup =
    record
      { isSemigroup =
        record
          { isMagma = Magma.isMagma (←-magma {A = A} magma)
          ; assoc   = λ f g h x → assoc (f x) (g x) (h x)
          }
      }


module _ {A : Set a} (B-monoid : Monoid b ℓ) where
  open Monoid B-monoid using (_≈_; _∙_; ε; identityˡ; identityʳ; semigroup) renaming (Carrier to B)

  ←-monoid : Monoid _ _
  ←-monoid =
    record
      { ε = const ε
      ; isMonoid =
        record
          { isSemigroup = Semigroup.isSemigroup (←-semigroup {A = A} semigroup)
          ; identity    = (identityˡ ∘_) , (identityʳ ∘_)
          }
      }
```
