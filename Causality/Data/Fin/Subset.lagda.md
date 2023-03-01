---
title: Causality.Data.Fin.Subset
---

Definitions and proofs about subsets of finite sets.

```agda
module Causality.Data.Fin.Subset where

open import Causality.Data.Vec
open import Data.Bool.Properties using (_≟_)
open import Data.Fin using (Fin; #_)
open import Data.Fin.Subset using (Subset; _∩_; _∪_; _⊂_; _⊆_; _∈_; _∉_; ⊤; ⁅_⁆; ∣_∣; Empty; inside; outside) renaming (_─_ to _∖_; ⊥ to ∅)
open import Data.Fin.Subset.Properties using (∩-comm; ∩-zeroˡ; ∩-zeroʳ; ∉⊥; ∣⊥∣≡0; Empty-unique; p⊂q⇒∣p∣<∣q∣)
open import Data.Fin.Subset.Induction using (⊂-wellFounded)
open import Data.Nat using (ℕ; _<_; _>_; pred; suc; zero)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (>⇒≢)
open import Data.Product using (Σ; ∃; ∃-syntax; _×_; _,_) renaming (proj₂ to _₂)
open import Data.Vec using (Vec; []; _∷_; _[_]=_; allFin; count; filter; there)
open import Data.Vec.Bounded using (Vec≤)
open import Function using (_∘_; case_of_; id; _on_)
open import Induction.WellFounded as Wf using (WellFounded)
open import Relation.Binary.Construct.On using (wellFounded)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; step-≡; _∎)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation.Core using (contradiction)
open import Relation.Unary using (Universal)

private
  variable
    n : ℕ

Disjoint : Subset n → Subset n → Set
Disjoint S T = Empty (S ∩ T)

Disjoint-as-≡ : {S T : Subset n}
  → Disjoint S T
  → S ∩ T ≡ ∅
Disjoint-as-≡ = Empty-unique

Disjoint-comm : {S T : Subset n}
  → Disjoint S T
  → Disjoint T S
Disjoint-comm {S = S} {T} disjoint rewrite ∩-comm S T = disjoint

Disjoint-∅ʳ : (S : Subset n) →
  Disjoint S ∅
Disjoint-∅ʳ S Nonempty-S∩∅ rewrite ∩-zeroʳ S = ∉⊥ (Nonempty-S∩∅ ₂)

Disjoint-∅ˡ : (S : Subset n) →
  Disjoint ∅ S
Disjoint-∅ˡ S Nonempty-∅∩S rewrite ∩-zeroˡ S = ∉⊥ (Nonempty-∅∩S ₂)

∉-∩-Disjoint : ∀ {S T : Subset n} {x}
  → Disjoint S T
  → x ∉ S ∩ T
∉-∩-Disjoint Disjoint-S-T x∈S∩T = Disjoint-S-T (_ , x∈S∩T)

_⊆∖_ : Subset n → Subset n → Set
S ⊆∖ T = S ⊆ (⊤ ∖ T)

⁅_⁆₂ : Fin n × Fin n → Subset n
⁅ i , j ⁆₂ = ⁅ i ⁆ ∪ ⁅ j ⁆

∣S∣≡0⇒Empty-S : {S : Subset n}
  → ∣ S ∣ ≡ 0
  → Empty S
∣S∣≡0⇒Empty-S ∣S∣≡0 (_ , there {y = inside}  _)                                       = case ∣S∣≡0 of λ()
∣S∣≡0⇒Empty-S ∣S∣≡0 (_ , there {y = outside} {xs = []}          ())
∣S∣≡0⇒Empty-S ∣S∣≡0 (_ , there {y = outside} {xs = inside ∷ _}  _)                    = case ∣S∣≡0 of λ()
∣S∣≡0⇒Empty-S ∣S∣≡0 (_ , there {y = outside} {xs = outside ∷ xs} (there xs[]=inside)) = >⇒≢ count≟inside>0 ∣S∣≡0
  where
  count≟inside>0 : count (_≟ inside) xs > 0
  count≟inside>0 = count≟->0 _≟_ (xs[]=x⇒x∈xs xs[]=inside)

∣S∣≡0⇒S≡∅ : {S : Subset n}
  → ∣ S ∣ ≡ 0
  → S ≡ ∅
∣S∣≡0⇒S≡∅ = Empty-unique ∘ ∣S∣≡0⇒Empty-S
```

We define isomorphisms of finite subsets.

```agda
record _≅_ {n} (S : Subset n) (T : Subset n) : Set where
  S′ : Set
  S′ = ∃ (_∈ S)

  T′ : Set
  T′ = ∃ (_∈ T)

  field f   : S′ → T′
  field f⁻¹ : T′ → S′

  field f⁻¹∘f : (s : S′) → f⁻¹ (f s) ≡ s
  field f∘f⁻¹ : (t : T′) → f (f⁻¹ t) ≡ t


≅-reflexive : Reflexive (_≅_ {n})
≅-reflexive =
  record
    { f     = id
    ; f⁻¹   = id
    ; f⁻¹∘f = λ _ → refl
    ; f∘f⁻¹ = λ _ → refl
    }

≅-symmetric : Symmetric (_≅_ {n})
≅-symmetric S≅T =
  record
    { f     = f⁻¹
    ; f⁻¹   = f
    ; f⁻¹∘f = f∘f⁻¹
    ; f∘f⁻¹ = f⁻¹∘f
    }
  where open _≅_ S≅T

≅-transitive : Transitive (_≅_ {n})
≅-transitive S≅T T≅U =
  record
    { f     = f T≅U ∘ f S≅T
    ; f⁻¹   = f⁻¹ S≅T ∘ f⁻¹ T≅U
    ; f⁻¹∘f = f⁻¹∘f′
    ; f∘f⁻¹ = f∘f⁻¹′
    }
  where
  open _≅_

  f⁻¹∘f′ : ∀ s → f⁻¹ S≅T (f⁻¹ T≅U (f T≅U (f S≅T s))) ≡ s
  f⁻¹∘f′ s rewrite f⁻¹∘f T≅U (f S≅T s) | f⁻¹∘f S≅T s = refl

  f∘f⁻¹′ : ∀ u → f T≅U (f S≅T (f⁻¹ S≅T (f⁻¹ T≅U u))) ≡ u
  f∘f⁻¹′ u rewrite f∘f⁻¹ S≅T (f⁻¹ T≅U u) | f∘f⁻¹ T≅U u = refl

S≅∅⇒S≡∅ : ∀ {S : Subset n} → S ≅ ∅ → S ≡ ∅
S≅∅⇒S≡∅ S≅∅ = Empty-unique λ s → contradiction (f s ₂) ∉⊥
  where open _≅_ S≅∅

∣∣<∣∣-well-founded : WellFounded {A = Subset n} (_<_ on ∣_∣)
∣∣<∣∣-well-founded = wellFounded ∣_∣ <-wellFounded

module _ {n} where
  open Wf.All (∣∣<∣∣-well-founded {n}) using (wfRec)

  private
    step : Wf.WfRec (_<_ on ∣_∣)
          (λ S₁ → (T₁ : Subset n) → S₁ ≅ T₁ → ∣ S₁ ∣ ≡ ∣ T₁ ∣)
          Relation.Unary.⊆′
          (λ S₁ → (T₁ : Subset n) → S₁ ≅ T₁ → ∣ S₁ ∣ ≡ ∣ T₁ ∣)
    step S ind T S≅T
      with ∣ S ∣ in ∣S∣
    ...  | zero = begin
          0         ≡⟨ Eq.sym (∣⊥∣≡0 n) ⟩
          ∣ ∅ {n} ∣  ≡⟨ Eq.cong ∣_∣ (Eq.sym (S≅∅⇒S≡∅ T≅∅)) ⟩
          ∣ T ∣      ∎
          where
          T≅∅ : T ≅ ∅
          T≅∅ = ≅-symmetric (Eq.subst (_≅ T) (∣S∣≡0⇒S≡∅ ∣S∣) S≅T)

    ...  | suc ∣S∣-1
          with count≡length∘filter (_≟ inside) S
    ...       | count = {!!}

  S≅T⇒∣S∣≡∣T∣ : ∀ {S : Subset n} {T : Subset n} → S ≅ T → ∣ S ∣ ≡ ∣ T ∣
  S≅T⇒∣S∣≡∣T∣ {S} {T} = wfRec _ (λ S → ∀ T → S ≅ T → ∣ S ∣ ≡ ∣ T ∣) step S T
```

```agda
reify : (S : Subset n) → Vec (Fin n) ∣ S ∣
reify {n} S = Eq.subst (Vec (Fin n)) length-S′≡∣S∣ (Vec≤.vec S′)
  where
  open import Data.Fin.Subset.Properties using (_∈?_)

  S′ : Vec≤ (Fin n) n
  S′ = filter (_∈? S) (allFin n)

  length-S′≡length-filter-≟inside-S :
    Vec≤.length S′ ≡ Vec≤.length (filter (_≟ inside) S)
  length-S′≡length-filter-≟inside-S = {!!}

  length-S′≡∣S∣ : Vec≤.length S′ ≡ ∣ S ∣
  length-S′≡∣S∣ =
    Eq.trans length-S′≡length-filter-≟inside-S
             (count≡length∘filter (_≟ inside) S)

∣S∣≡1⇒S≡⁅⁆ : {S : Subset n}
  → ∣ S ∣ ≡ 1
  → ∃[ i ] S ≡ ⁅ i ⁆
∣S∣≡1⇒S≡⁅⁆ {S = S} ∣S∣≡1 = {!!} , {!!}
```
