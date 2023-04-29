---
title: Causality.Data.Fin.Subset
---

Definitions and proofs about subsets of finite sets.

```agda
{-# OPTIONS --without-K --safe #-}

module Causality.Data.Fin.Subset where

open import Causality.Data.List
open import Causality.Data.Nat
open import Causality.Data.Product
open import Causality.Data.Vec
open import Causality.Data.Vec.Bounded as Vec≤ hiding (length)
open import Causality.Function
open import Causality.Relation.Binary.PropositionalEquality
open import Causality.Relation.Binary.PropositionalEquality.≡-Reasoning
import Data.Bool.Properties
open import Data.Fin using (Fin; #_; inject₁; inject≤; suc; zero)
open import Data.Fin.Subset using (Subset; _∩_; _∪_; _⊂_; _⊆_; _∈_; _∉_; ⊤; ⁅_⁆; ∣_∣; _-_; Empty; inside; Nonempty; outside) renaming (_─_ to _∖_; ⊥ to ∅)
open import Data.Fin.Subset.Properties using (_∈?_; ⊆-antisym; ∪-assoc; ∪-comm; ∩-comm; ∩-idem; ∩-zeroˡ; ∩-zeroʳ; ∉⊥; ∣⊥∣≡0; ∪-identityˡ; ∪-identityʳ; drop-not-there; Empty-unique; nonempty?; p─q⊆p; p⊂q⇒∣p∣<∣q∣; p─⊥≡p; p∩q≢∅⇒p─q⊂p; p⊆p∪q; q⊆p∪q; x∈p∪q⁻; x∈p∪q⁺; x∈p∩q⁺; x∈⁅x⁆; x∈⁅y⁆⇒x≡y; x∈p⇒p-x⊂p; x∈p∧x∉q⇒x∈p─q; x∈p∧x≢y⇒x∈p-y; x≢y⇒x∉⁅y⁆; x∈p∩q⁻; ∣⁅x⁆∣≡1)
open import Data.Fin.Subset.Induction using (⊂-wellFounded)
open import Data.List using (List; allFin; filter; length; []; _∷_)
open import Data.List.Properties using (filter-none; filter-some)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (All¬⇒¬Any)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using (lookup-result)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Nat using (ℕ; _+_; _∸_; _<_; _≤_; _>_; _≥_; pred; s≤s; suc; zero; z≤n)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (>⇒≢; 0<1+n; +-assoc; +-cancelˡ-≡; +-comm; +-identityʳ; ≤-antisym; ≤-reflexive; m∸n≡0⇒m≤n; m∸n≢0⇒n<m)
open import Data.Product using (Σ; ∃; ∃-syntax; ∃₂; _×_; _,_; -,_; map₂; uncurry) renaming (proj₁ to _₁; proj₂ to _₂)
open import Data.Product.Properties using (,-injectiveˡ; Σ-≡,≡→≡)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_; [_]; _∷ʳ_; count; here; there)
open import Data.Vec.Bounded as Vec≤ using (Vec≤; _,_)
open import Data.Vec.Properties using ([]=⇒lookup; lookup-replicate)
open import Function using (_↔_; _⇔_; _↣_; _∘_; _$-; id; Injection; Injective; Inverse; Inverseᵇ; Inverseˡ; Inverseʳ; mk↔; mk⇔; mk↣; _on_)
open import Function.Properties.Inverse using (↔-sym; ↔⇒↣)
open import Induction.WellFounded as Wf using (WellFounded)
open import Level using (Level)
open import Relation.Binary.Construct.On using (wellFounded)
open import Relation.Binary.Definitions using (Irrelevant; Reflexive; Symmetric; Transitive)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; _≗_; refl)
open import Relation.Nullary using (¬_; _×-dec_; no; yes)
open import Relation.Nullary.Decidable using (decidable-stable)
open import Relation.Nullary.Negation.Core using (contradiction)
open import Relation.Unary using (_≐_; Pred; Universal) renaming (_⊆_ to _⊆ᴾ_)

private
  variable
    a       : Level
    m n     : ℕ
    S T U   : Subset n
    i j x y : Fin n
    xs      : List (Fin n)
```

Extensionally equal subsets are definitionally equal:

```agda
extensionality :
    ((_∈ S) ≐ (_∈ T))
  →      S  ≡     T
extensionality = uncurry ⊆-antisym
```

We define disjointness of sets:

```agda
Disjoint : Subset n → Subset n → Set
Disjoint S T = Empty (S ∩ T)

Disjoint-as-≡ : Disjoint S T → S ∩ T ≡ ∅
Disjoint-as-≡ = Empty-unique

Disjoint-sym : Disjoint S T → Disjoint T S
Disjoint-sym {S = S} {T} disjoint rewrite ∩-comm S T = disjoint

Disjoint-∅ʳ : (S : Subset n) → Disjoint S ∅
Disjoint-∅ʳ S Nonempty-S∩∅ rewrite ∩-zeroʳ S = ∉⊥ (Nonempty-S∩∅ ₂)

Disjoint-∅ˡ : (S : Subset n) → Disjoint ∅ S
Disjoint-∅ˡ S Nonempty-∅∩S rewrite ∩-zeroˡ S = ∉⊥ (Nonempty-∅∩S ₂)

Disjoint-∪ˡ : Disjoint (S ∪ T) U → Disjoint S U
Disjoint-∪ˡ {S = S} {T} {U} Disjoint-S∪T-U (x , x∈S∩U)
  with (x∈S , x∈U) ← x∈p∩q⁻ _ _ x∈S∩U
  = Disjoint-S∪T-U (-, x∈[S∪T]∩U)
  where
  x∈[S∪T]∩U : x ∈ (S ∪ T) ∩ U
  x∈[S∪T]∩U = x∈p∩q⁺ (x∈p∪q⁺ (inj₁ x∈S) , x∈U)

Disjoint-swap :
    Disjoint S T
  → Disjoint (S ∪ T) U
  → Disjoint T (S ∪ U)
Disjoint-swap {S = S} {T} {U} Disjoint-S-T Disjoint-S∪T-U (x , x∈T∩[S∪U])
  with (x∈T , x∈S∪U) ← x∈p∩q⁻ _ _ x∈T∩[S∪U]
  with x∈p∪q⁻ _ _ x∈S∪U
...  | inj₁ x∈S = Disjoint-S-T (-, x∈p∩q⁺ (x∈S , x∈T))
...  | inj₂ x∈U = Disjoint-S∪T-U (x , x∈p∩q⁺ (x∈p∪q⁺ (inj₂ x∈T) , x∈U))

∉-∩-Disjoint : Disjoint S T → x ∉ S ∩ T
∉-∩-Disjoint Disjoint-S-T x∈S∩T = Disjoint-S-T (-, x∈S∩T)
```

Auxiliary definitions that will be convenient later:

```agda
_⊆∖_ : Subset n → Subset n → Set
S ⊆∖ T = S ⊆ (⊤ ∖ T)

⁅_⁆₂ : Fin n × Fin n → Subset n
⁅ i , j ⁆₂ = ⁅ i ⁆ ∪ ⁅ j ⁆

i∈⁅i,j⁆ : (i j : Fin n) → i ∈ ⁅ i , j ⁆₂
i∈⁅i,j⁆ _ _ = x∈p∪q⁺ (inj₁ (x∈⁅x⁆ _))

j∈⁅i,j⁆ : (i j : Fin n) → j ∈ ⁅ i , j ⁆₂
j∈⁅i,j⁆ _ _ = x∈p∪q⁺ (inj₂ (x∈⁅x⁆ _))

∣⁅i,j⁆∣≤2 : (i j : Fin n) → ∣ ⁅ i , j ⁆₂ ∣ ≤ 2
∣⁅i,j⁆∣≤2 {suc n} zero    zero    rewrite ∪-identityˡ (∅ {n}) | ∣⊥∣≡0 n = s≤s z≤n
∣⁅i,j⁆∣≤2         zero    (suc j) rewrite ∪-identityˡ ⁅ j ⁆ = s≤s (≤-reflexive (∣⁅x⁆∣≡1 j))
∣⁅i,j⁆∣≤2         (suc i) zero    rewrite ∪-identityʳ ⁅ i ⁆ = s≤s (≤-reflexive (∣⁅x⁆∣≡1 i))
∣⁅i,j⁆∣≤2         (suc i) (suc j) = ∣⁅i,j⁆∣≤2 i j

i≢j⇒∣⁅i,j⁆∣≡2 : i ≢ j → ∣ ⁅ i , j ⁆₂ ∣ ≡ 2
i≢j⇒∣⁅i,j⁆∣≡2 {i = i} {j} i≢j = ≤-antisym (∣⁅i,j⁆∣≤2 i j) (i≢j⇒∣⁅i,j⁆∣≥2 i≢j)
  where
  i≢j⇒∣⁅i,j⁆∣≥2 : {i j : Fin n}
    → i ≢ j
    → ∣ ⁅ i , j ⁆₂ ∣ ≥ 2
  i≢j⇒∣⁅i,j⁆∣≥2 {i = zero}  {zero}  = contradiction refl
  i≢j⇒∣⁅i,j⁆∣≥2 {i = zero}  {suc j} _ rewrite ∪-identityˡ ⁅ j ⁆ = s≤s (≤-reflexive (Eq.sym (∣⁅x⁆∣≡1 j)))
  i≢j⇒∣⁅i,j⁆∣≥2 {i = suc i} {zero}  _ rewrite ∪-identityʳ ⁅ i ⁆ = s≤s (≤-reflexive (Eq.sym (∣⁅x⁆∣≡1 i)))
  i≢j⇒∣⁅i,j⁆∣≥2 {i = suc i} {suc j} 1+i≢1+j = i≢j⇒∣⁅i,j⁆∣≥2 (1+i≢1+j ∘ Eq.cong suc)
```

```agda
∣S∣≡0⇒Empty-S : ∣ S ∣ ≡ 0 → Empty S
∣S∣≡0⇒Empty-S ∣S∣≡0 (_ , there {y = inside}  _)                                       = contradiction ∣S∣≡0 λ()
∣S∣≡0⇒Empty-S ∣S∣≡0 (_ , there {y = outside} {xs = []}           ())
∣S∣≡0⇒Empty-S ∣S∣≡0 (_ , there {y = outside} {xs = inside  ∷ _}  _)                   = contradiction ∣S∣≡0 λ()
∣S∣≡0⇒Empty-S ∣S∣≡0 (_ , there {y = outside} {xs = outside ∷ xs} (there xs[]=inside)) = >⇒≢ count≟inside>0 ∣S∣≡0
  where
  open Data.Bool.Properties using (_≟_)

  count≟inside>0 : count (_≟ inside) xs > 0
  count≟inside>0 = ∈⇒count≟>0 _≟_ (xs[]=x⇒x∈xs xs[]=inside)

∣S∣≡0⇒S≡∅ : ∣ S ∣ ≡ 0 → S ≡ ∅
∣S∣≡0⇒S≡∅ = Empty-unique ∘ ∣S∣≡0⇒Empty-S

∣S∣>0⇒∃∈S : ∣ S ∣ > 0 → ∃ (_∈ S)
∣S∣>0⇒∃∈S {S = inside  ∷ S} ∣S∣>0 = # 0 , here
∣S∣>0⇒∃∈S {S = outside ∷ S} ∣∷S∣>0
  with ∣S∣>0⇒∃∈S ∣∷S∣>0
...  | s , s∈S = suc s , there s∈S

x∈S⇒⁅x⁆∪[S-x]≡S : ∀ {x}
  → x ∈ S
  → ⁅ x ⁆ ∪ (S - x) ≡ S
x∈S⇒⁅x⁆∪[S-x]≡S {S = S} {x} x∈S = extensionality (⁅x⁆∪[S-x]⊆S , S⊆⁅x⁆∪[S-x])
  where
  open Data.Fin using (_≟_)

  ⁅x⁆∪[S-x]⊆S : ⁅ x ⁆ ∪ (S - x) ⊆ S
  ⁅x⁆∪[S-x]⊆S y∈⁅x⁆∪[S-x]
    with x∈p∪q⁻ _ _ y∈⁅x⁆∪[S-x]
  ...  | inj₁ y∈⁅x⁆ rewrite x∈⁅y⁆⇒x≡y _ y∈⁅x⁆ = x∈S
  ...  | inj₂ y∈S-x = p─q⊆p _ _ y∈S-x

  S⊆⁅x⁆∪[S-x] : S ⊆ ⁅ x ⁆ ∪ (S - x)
  S⊆⁅x⁆∪[S-x] {x = y} y∈S
    with y ≟ x
  ...  | no  y≢x  = x∈p∪q⁺ (inj₂ (x∈p∧x∉q⇒x∈p─q y∈S (x≢y⇒x∉⁅y⁆ y≢x)))
  ...  | yes refl = x∈p∪q⁺ (inj₁ (x∈⁅x⁆ _))

x∈S∖T⇒x∈S∧x∉T : (_∈ S ∖ T) ⊆ᴾ (_∉ T)
x∈S∖T⇒x∈S∧x∉T {S = _ ∷ _} (there x∈S∖T) (there x∈T) = contradiction x∈T (x∈S∖T⇒x∈S∧x∉T x∈S∖T)

x∉S-x : ∀ (S : Subset n) x → x ∉ S - x
x∉S-x S x x∈S-x
  with x ∈? S
...  | no  x∉S = contradiction (p─q⊆p _ _ x∈S-x) x∉S
...  | yes x∈S = contradiction (x∈⁅x⁆ _) (x∈S∖T⇒x∈S∧x∉T x∈S-x)

x∈S-y⇒x∈S×x≢y : x ∈ S - y → x ∈ S × x ≢ y
x∈S-y⇒x∈S×x≢y x∈S-y = p─q⊆p _ _ x∈S-y , λ{ refl → contradiction x∈S-y (x∉S-x _ _) }

[⁅x⁆∪S]-x≡S-x : ∀ (S : Subset n) x → (⁅ x ⁆ ∪ S) - x ≡ S - x
[⁅x⁆∪S]-x≡S-x S x = extensionality ([⁅x⁆∪S]-x⊆S-x , S-x⊆[⁅x⁆∪S]-x)
  where
  [⁅x⁆∪S]-x⊆S-x : (⁅ x ⁆ ∪ S) - x ⊆ S - x
  [⁅x⁆∪S]-x⊆S-x y∈[⁅x⁆∪S]-x
    with (y∈⁅x⁆∪S , y≢x) ← x∈S-y⇒x∈S×x≢y y∈[⁅x⁆∪S]-x
    with x∈p∪q⁻ _ _ y∈⁅x⁆∪S
  ...  | inj₁ y∈⁅x⁆ = contradiction (x∈⁅y⁆⇒x≡y _ y∈⁅x⁆) y≢x
  ...  | inj₂ y∈S   = x∈p∧x≢y⇒x∈p-y y∈S y≢x

  S-x⊆[⁅x⁆∪S]-x : S - x ⊆ (⁅ x ⁆ ∪ S) - x
  S-x⊆[⁅x⁆∪S]-x y∈S-x
    with (x∈S , x≢y) ← x∈S-y⇒x∈S×x≢y y∈S-x
    = x∈p∧x≢y⇒x∈p-y (x∈p∪q⁺ (inj₂ x∈S)) x≢y

x∉S⇒S-x≡S : x ∉ S → S - x ≡ S
x∉S⇒S-x≡S {x = x} {S = S} x∉S = extensionality (S-x⊆S , S⊆S-x)
  where
  S-x⊆S : S - x ⊆ S
  S-x⊆S = _₁ ∘ x∈S-y⇒x∈S×x≢y

  S⊆S-x : S ⊆ S - x
  S⊆S-x y∈S = x∈p∧x≢y⇒x∈p-y y∈S λ{ refl → contradiction y∈S x∉S }
```

We define a more ergonomic form of strong induction:

```agda
module _ {P : Pred (Subset n) a}
  (P-∅ : P ∅)
  (P-ind : ∀ {S} → Nonempty S → (_⊂ S) ⊆ᴾ P → P S)
  where
  open Wf.All (⊂-wellFounded {n}) using (wfRec)
  open Relation.Unary using (_⊆′_)

  private
    step : Wf.WfRec _⊂_ P ⊆′ P
    step S P-ind-⊂
      with nonempty? S
    ...  | no  Empty-S rewrite Eq.sym (Empty-unique Empty-S) = P-∅
    ...  | yes Nonempty-S = P-ind Nonempty-S (P-ind-⊂ $-)

  strong-induction : Π[ P ]
  strong-induction = wfRec _ _ step
```

For convenience, we define a version of strong induction that provides an explicit element of the set:

```agda
module _ {P : Pred (Subset n) a}
  (P-∅ : P ∅)
  (P-ind : ∀ {S x} → (_⊂ (⁅ x ⁆ ∪ S)) ⊆ᴾ P → x ∉ S → P (⁅ x ⁆ ∪ S))
  where
  open Wf.All (⊂-wellFounded {n}) using (wfRec)
  open Relation.Unary using (_⊆′_)

  private
    step : Wf.WfRec _⊂_ P ⊆′ P
    step S P-ind-⊂S
      with nonempty? S
    ...  | no  Empty-S rewrite Eq.sym (Empty-unique Empty-S) = P-∅
    ...  | yes (x , x∈S)
           rewrite Eq.sym (x∈S⇒⁅x⁆∪[S-x]≡S x∈S)
           = P-ind (P-ind-⊂S _) (x∉S-x _ _)

  pointed-strong-induction : Π[ P ]
  pointed-strong-induction = wfRec _ _ step
```

We define induction on the elements of a subset:

```agda
module _ {P : Pred (Subset n) a}
  (P-∅ : P ∅)
  (P-ind : ∀ {S x} → x ∉ S → P S → P (⁅ x ⁆ ∪ S))
  where
  open Wf.All (⊂-wellFounded {n}) using (wfRec)

  private
    inductive-step :
        (_⊂ (⁅ x ⁆ ∪ S)) ⊆ᴾ P
      → x ∉ S
      → P (⁅ x ⁆ ∪ S)
    inductive-step {x = x} {S = S} P-ind-⊂S x∉S =
      P-ind x∉S (P-ind-⊂S S⊂⁅x⁆∪S)
      where
      S⊂⁅x⁆∪S : S ⊂ ⁅ x ⁆ ∪ S
      S⊂⁅x⁆∪S = q⊆p∪q _ _ , (x , (x∈p∪q⁺ (inj₁ (x∈⁅x⁆ _)) , x∉S))

  induction-on-elements : Π[ P ]
  induction-on-elements = pointed-strong-induction P-∅ inductive-step
```

```agda
x∉⇒Disjoint⁅x⁆ : (x ∉_) ⊆ᴾ Disjoint ⁅ x ⁆
x∉⇒Disjoint⁅x⁆ x∉S (y , y∈S∩x)
  with (y∈⁅x⁆ , y∈S) ← x∈p∩q⁻ _ _ y∈S∩x
  rewrite x∈⁅y⁆⇒x≡y _ y∈⁅x⁆
  = x∉S y∈S

Disjoint⁅x⁆⇒x∉ : Disjoint ⁅ x ⁆ ⊆ᴾ (x ∉_)
Disjoint⁅x⁆⇒x∉ Disjoint-⁅x⁆-S x∈S = Disjoint-⁅x⁆-S (-, x∈p∩q⁺ (x∈⁅x⁆ _ , x∈S))

Disjoint⁅x⁆⇔x∉ : Disjoint {n = n} ⁅ x ⁆ ≐ (x ∉_)
Disjoint⁅x⁆⇔x∉ = Disjoint⁅x⁆⇒x∉ , x∉⇒Disjoint⁅x⁆

∣S∣≡1⇒S≡⁅x⁆ : ∣ S ∣ ≡ 1 → ∃[ i ] S ≡ ⁅ i ⁆
∣S∣≡1⇒S≡⁅x⁆ {S = inside  ∷ S} ∣S∣≡1
  rewrite ∣S∣≡0⇒S≡∅ {S = S} (+-cancelˡ-≡ 1 _ _ ∣S∣≡1)
  = # 0 , refl
∣S∣≡1⇒S≡⁅x⁆ {S = outside ∷ S} ∣S∣≡1
  with (i , refl) ← ∣S∣≡1⇒S≡⁅x⁆ {S = S} ∣S∣≡1
  = suc i , refl

x∉S⇒∣⁅x⁆∪S∣≡1+∣S∣ :
    x ∉ S
  → ∣ ⁅ x ⁆ ∪ S ∣ ≡ 1 + ∣ S ∣
x∉S⇒∣⁅x⁆∪S∣≡1+∣S∣ {suc n} {x = zero}  {S = outside ∷ S} x∉S rewrite ∪-identityˡ S = refl
x∉S⇒∣⁅x⁆∪S∣≡1+∣S∣ {suc n} {x = suc x} {S = outside ∷ S} x∉S = x∉S⇒∣⁅x⁆∪S∣≡1+∣S∣ (drop-not-there x∉S)
x∉S⇒∣⁅x⁆∪S∣≡1+∣S∣ {suc n} {x = zero}  {S = inside  ∷ S} x∉S = contradiction here x∉S
x∉S⇒∣⁅x⁆∪S∣≡1+∣S∣ {suc n} {x = suc x} {S = inside  ∷ S} x∉S = Eq.cong suc (x∉S⇒∣⁅x⁆∪S∣≡1+∣S∣ (drop-not-there x∉S))

∈-irrelevant : Irrelevant (_∈_ {n})
∈-irrelevant here        here         = refl
∈-irrelevant (there x∈S) (there x∈S′) = Eq.cong there (∈-irrelevant x∈S x∈S′)

module _ {n} where
  private
    P : Pred (Subset n) _
    P S = ∀ T → Disjoint S T → ∣ S ∪ T ∣ ≡ ∣ S ∣ + ∣ T ∣

    P-∅ : P (∅ {n})
    P-∅ T _ rewrite ∣⊥∣≡0 n | ∪-identityˡ T = refl

    inductive-step :
        x ∉ S
      → P S
      → P (⁅ x ⁆ ∪ S)
    inductive-step {x = x} {S} x∉S P-S T Disjoint-⁅x⁆∪S-T =
      begin
        ∣ (⁅ x ⁆ ∪ S) ∪ T ∣     ≡⟨ ∪-comm ⁅ x ⁆ _ ⟩⟨ Eq.cong (λ ∙ → ∣ ∙ ∪ T ∣) ⟩
        ∣ (S ∪ ⁅ x ⁆) ∪ T ∣     ≡⟨ ∪-assoc S _ _ ⟩⟨ Eq.cong ∣_∣ ⟩
        ∣ S ∪ (⁅ x ⁆ ∪ T) ∣     ≡⟨ P-S _ Disjoint-S-⁅x⁆∪T ⟩
        ∣ S ∣ + ∣ ⁅ x ⁆ ∪ T ∣    ≡⟨ x∉S⇒∣⁅x⁆∪S∣≡1+∣S∣ x∉T ⟩⟨ Eq.cong (∣ S ∣ +_) ⟩
        ∣ S ∣ + suc ∣ T ∣        ≡⟨ +-assoc ∣ S ∣ _ _ ⟩⟨ Eq.sym ⟩
        (∣ S ∣ + 1) + ∣ T ∣      ≡⟨ +-comm ∣ S ∣ _ ⟩⟨ Eq.cong (_+ ∣ T ∣) ⟩
        suc ∣ S ∣ + ∣ T ∣        ≡⟨ x∉S⇒∣⁅x⁆∪S∣≡1+∣S∣ x∉S ⟩⟨ Eq.cong (_+ ∣ T ∣) ∘ Eq.sym ⟩
        ∣ ⁅ x ⁆ ∪ S ∣ + ∣ T ∣
      ∎
      where
      x∉T : x ∉ T
      x∉T = Disjoint⁅x⁆⇒x∉ (Disjoint-∪ˡ Disjoint-⁅x⁆∪S-T)

      Disjoint-S-⁅x⁆∪T : Disjoint S (⁅ x ⁆ ∪ T)
      Disjoint-S-⁅x⁆∪T = Disjoint-swap (x∉⇒Disjoint⁅x⁆ x∉S) Disjoint-⁅x⁆∪S-T

  Disjoint-S-T⇒∣S∪T|≡∣S∣+∣T∣ : Π[ P ]
  Disjoint-S-T⇒∣S∪T|≡∣S∣+∣T∣ = induction-on-elements P-∅ inductive-step
```

We define isomorphisms of finite subsets:

```agda
_≅_ : Subset m → Subset n → Set _
S ≅ T = ∃ (_∈ S) ↔ ∃ (_∈ T)
```

`mk≅` is just a specialized version of `mk↔`, to help with type inference:

```agda
mk≅ : {to : ∃ (_∈ S) → ∃ (_∈ T)} {from : ∃ (_∈ T) → ∃ (_∈ S)}
  → Inverseᵇ _≡_ _≡_ to from
  → S ≅ T
mk≅ {to = to} {from = from} = mk↔ {to = to} {from = from}
```

```agda
≡-∃∈ : {x y : ∃ (_∈ S)}
  → x ₁ ≡ y ₁
  → x ≡ y
≡-∃∈ = Σ-≡,≡→≡ ∘ (_, ∈-irrelevant _ _)

S≅∅⇒S≡∅ : S ≅ ∅ {n} → S ≡ ∅
S≅∅⇒S≡∅ S≅∅ = Empty-unique λ s → contradiction (to s ₂) ∉⊥
  where open Inverse S≅∅

module _ (S≅T : S ≅ T) where
  open Inverse S≅T

  to₁-injective : {x y : ∃ (_∈ S)}
    → to x ₁ ≡ to y ₁
    → x ≡ y
  to₁-injective = Injection.injective (↔⇒↣ S≅T) ∘ ≡-∃∈


module _  where
  private
    module _ {S : Subset n} {x} where
      ι : ∃ (_∈ S - x) → ∃ (_∈ S)
      ι = map₂ (p─q⊆p _ _)

      ₁∘ι≡₁ : _₁ ∘ ι ≗ _₁
      ₁∘ι≡₁ _ = refl

      ι-injective : Injective _≡_ _≡_ ι
      ι-injective = ≡-∃∈ ∘ ,-injectiveˡ

      ι-↣ : ∃ (_∈ S - x) ↣ ∃ (_∈ S)
      ι-↣ = mk↣ ι-injective


  module _ (S≅T : S ≅ T) where
    open Inverse S≅T

    to-remove : {x : ∃ (_∈ S)}
      → ∃ (_∈ S - x ₁)
      → ∃ (_∈ T - to x ₁)
    to-remove {x = x} x′ =
      let (y , y∈T) = to (ι x′)
        in y , x∈p∧x≢y⇒x∈p-y y∈T to₁-x′≢to₁-x
      where
      x′≢x : ι x′ ≢ x
      x′≢x refl = contradiction (x′ ₂) (x∉S-x _ _)

      to₁-x′≢to₁-x : to (ι x′) ₁ ≢ to x ₁
      to₁-x′≢to₁-x to₁-x′≡to₁-x =
        contradiction (to₁-injective S≅T to₁-x′≡to₁-x) x′≢x

    to-remove-correct : ∀ {x} → ι ∘ to-remove {x} ≗ to ∘ ι
    to-remove-correct _ = ≡-∃∈ refl


  module _ (S≅T : S ≅ T) where
    open Inverse S≅T

    from-remove : {x : ∃ (_∈ S)}
      → ∃ (_∈ T - to x ₁)
      → ∃ (_∈ S - x ₁)
    from-remove {x = x}
      = map₂ (Eq.subst (λ ∙ → _ ∈ S - ∙ ₁) (inverseʳ _)) ∘
        to-remove (↔-sym S≅T)

    from-remove-correct : ∀ {x} → ι ∘ from-remove {x} ≗ from ∘ ι
    from-remove-correct _ = ≡-∃∈ refl


  module _ (S≅T : S ≅ T) where
    open Inverse S≅T

    from-to-remove-inv : ∀ {x}
      → Inverseˡ _≡_ _≡_ (to-remove S≅T {x}) (from-remove S≅T)
    from-to-remove-inv {x = x} = ↣-monic ι-↣ ι∘to-remove∘from-remove≡ι
      where
      ι∘to-remove∘from-remove≡ι : ι ∘ to-remove S≅T {x} ∘ from-remove S≅T ≗ ι
      ι∘to-remove∘from-remove≡ι y′
        rewrite to-remove-correct S≅T {x} (from-remove S≅T y′)
              | from-remove-correct S≅T y′
        = inverseˡ _

    to-from-remove-inv : ∀ {x}
      → Inverseʳ _≡_ _≡_ (to-remove S≅T {x}) (from-remove S≅T)
    to-from-remove-inv {x = x} = ↣-monic ι-↣ ι∘from-remove∘to-remove≡ι
      where
      ι∘from-remove∘to-remove≡ι : ι ∘ from-remove S≅T ∘ to-remove S≅T {x} ≗ ι
      ι∘from-remove∘to-remove≡ι x′
        rewrite from-remove-correct S≅T (to-remove S≅T {x} x′)
              | to-remove-correct S≅T {x} x′
        = inverseʳ _

    ≅-remove : (x : ∃ (_∈ S))
      → (S - x ₁) ≅ (T - to x ₁)
    ≅-remove x =
      mk≅ {to = to-remove S≅T} {from = from-remove S≅T}
        (from-to-remove-inv , to-from-remove-inv)


module _ {n} where
  private
    P : Pred (Subset n) _
    P S = (T : Subset n) → S ≅ T → ∣ S ∣ ≡ ∣ T ∣

    P-∅ : P (∅ {n})
    P-∅ T ∅≅T rewrite S≅∅⇒S≡∅ (↔-sym ∅≅T) = refl

    inductive-step :
        x ∉ S
      → P S
      → P (⁅ x ⁆ ∪ S)
    inductive-step {x = x} {S} x∉S P-S T ⁅x⁆∪S≅T
      = begin
        ∣ ⁅ x ⁆ ∪ S ∣                    ≡⟨ x∉S⇒∣⁅x⁆∪S∣≡1+∣S∣ x∉S ⟩
        suc ∣ S ∣                        ≡⟨ P-S _ S≅T-[to-x] ⟩⟨ Eq.cong suc ⟩
        suc ∣ T - to-x ₁ ∣               ≡⟨ x∉S⇒∣⁅x⁆∪S∣≡1+∣S∣ (x∉S-x T _) ⟩⟨ Eq.sym ⟩
        ∣ ⁅ to-x ₁ ⁆ ∪ (T - to-x ₁) ∣    ≡⟨ x∈S⇒⁅x⁆∪[S-x]≡S (to-x ₂) ⟩⟨ Eq.cong ∣_∣ ⟩
        ∣ T ∣
      ∎
      where
      Σx : ∃ (_∈ ⁅ x ⁆ ∪ S)
      Σx = x , p⊆p∪q _ (x∈⁅x⁆ x)

      to-x : ∃ (_∈ T)
      to-x = Inverse.to ⁅x⁆∪S≅T Σx

      [⁅x⁆∪S]-x≡S : (⁅ x ⁆ ∪ S) - x ≡ S
      [⁅x⁆∪S]-x≡S rewrite [⁅x⁆∪S]-x≡S-x S x | x∉S⇒S-x≡S x∉S = refl

      [⁅x⁆∪S]-x≅T-[to-x] : ((⁅ x ⁆ ∪ S) - x) ≅ (T - to-x ₁)
      [⁅x⁆∪S]-x≅T-[to-x] = ≅-remove ⁅x⁆∪S≅T Σx

      S≅T-[to-x] : S ≅ (T - to-x ₁)
      S≅T-[to-x] = Eq.subst (_≅ (T - to-x ₁)) [⁅x⁆∪S]-x≡S [⁅x⁆∪S]-x≅T-[to-x]

  S≅T⇒∣S∣≡∣T∣ : Π[ P ]
  S≅T⇒∣S∣≡∣T∣ = induction-on-elements P-∅ inductive-step
```

```agda
from-List : List (Fin n) → Subset n
from-List []       = ∅
from-List (x ∷ xs) = ⁅ x ⁆ ∪ from-List xs

module _ {n} where
  open Data.Bool.Properties using () renaming (_≟_ to _≟ᵇ_)
  open Data.Fin using (_≟_)
  open Data.Fin.Subset.Properties using (_∈?_)
  open import Data.List.Membership.DecPropositional (_≟_ {n}) using () renaming (_∈_ to _∈ˡ_; _∈?_ to _∈ˡ?_)
  open Causality.Data.List.DecEq (_≟_ {n})

  ∈from-List-xs⇒∈xs : (_∈ from-List xs) ⊆ᴾ (_∈ˡ xs)
  ∈from-List-xs⇒∈xs {xs = []}    (there {i = i} x∈from-List-xs) =
    contra (lookup-replicate i outside)
           ([]=⇒lookup x∈from-List-xs) λ()
  ∈from-List-xs⇒∈xs {xs = _ ∷ _} x∈ˡy∷xs
    with x∈p∪q⁻ _ _ x∈ˡy∷xs
  ... | inj₁ x∈⁅y⁆  = here  (x∈⁅y⁆⇒x≡y _ x∈⁅y⁆)
  ... | inj₂ x∈y∷xs = there (∈from-List-xs⇒∈xs x∈y∷xs)

  ∈xs⇒∈from-List-xs : (_∈ˡ xs) ⊆ᴾ (_∈ from-List xs)
  ∈xs⇒∈from-List-xs (here  refl) = x∈p∪q⁺ (inj₁ (x∈⁅x⁆ _))
  ∈xs⇒∈from-List-xs (there x∈xs) = x∈p∪q⁺ (inj₂ (∈xs⇒∈from-List-xs x∈xs))


module _ {n} where
  open Data.Fin using (_≟_)
  open Causality.Data.List.DecEq (_≟_ {n})

  open Data.Bool.Properties using () renaming (_≟_ to _≟ᵇ_)
  open import Data.List.Membership.DecPropositional (_≟_ {n}) using () renaming (_∈_ to _∈ˡ_; _∈?_ to _∈ˡ?_)
  open import Data.List.Membership.Propositional.Properties using (∈-allFin; ∈-filter⁺)
  open import Data.List.Relation.Unary.Unique.Propositional.Properties using (allFin⁺; filter⁺)

  ∣from-List∣≡length :
      Unique xs
    → ∣ from-List xs ∣ ≡ length xs
  ∣from-List∣≡length {n} [] rewrite ∣⊥∣≡0 n = refl
  ∣from-List∣≡length (x∉xs ∷ xs-unique)
    rewrite Eq.sym (∣from-List∣≡length xs-unique)
    = x∉S⇒∣⁅x⁆∪S∣≡1+∣S∣ (All¬⇒¬Any x∉xs ∘ ∈from-List-xs⇒∈xs)

  to-List : Subset n → List (Fin n)
  to-List S = filter (_∈? S) (allFin n)

  to-List-Unique : (S : Subset n) → Unique (to-List S)
  to-List-Unique S = filter⁺ (_∈? S) (allFin⁺ _)

  ∈to-List-S⇒∈S : (_∈ˡ to-List S) ⊆ᴾ (_∈ S)
  ∈to-List-S⇒∈S x∈ˡS
    with lookup-result (Any-filter⇒Any-× (_ ≟_) (_∈? _) {l = allFin n} x∈ˡS)
  ...  | x≡ , x∈S rewrite Eq.sym x≡ = x∈S

  ∈S⇒∈to-List-S : (_∈ S) ⊆ᴾ (_∈ˡ to-List S)
  ∈S⇒∈to-List-S = ∈-filter⁺ (_∈? _) (∈-allFin _)

  from-to-List : (S : Subset n) → from-List (to-List S) ≡ S
  from-to-List S = extensionality (∈from-to-S⇒∈S , ∈S⇒∈from-to-S)
    where
    ∈from-to-S⇒∈S : from-List (to-List S) ⊆ S
    ∈from-to-S⇒∈S = ∈to-List-S⇒∈S ∘ ∈from-List-xs⇒∈xs

    ∈S⇒∈from-to-S : S ⊆ from-List (to-List S)
    ∈S⇒∈from-to-S = ∈xs⇒∈from-List-xs ∘ ∈S⇒∈to-List-S

  length-to-List : (S : Subset n)
    → length (to-List S) ≡ ∣ S ∣
  length-to-List S =
    begin
      length (to-List S)           ≡⟨ ∣from-List∣≡length (to-List-Unique _) ⟩⟨ Eq.sym ⟩
      ∣ from-List (to-List S) ∣    ≡⟨ from-to-List S ⟩⟨ Eq.cong ∣_∣ ⟩
      ∣ S ∣
    ∎
```
