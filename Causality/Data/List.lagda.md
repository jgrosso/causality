---
title: Causality.Data.List
---

Definitions and proofs about finite lists.

```agda
{-# OPTIONS --without-K --safe #-}

module Causality.Data.List where

open import Causality.Data.Product
open import Causality.Function
open import Causality.Relation.Nullary
open import Causality.Relation.Unary
open import Data.Fin using (Fin; suc)
open import Data.List using (List; _∷_; []; [_]; _++_; allFin; filter; head; last; length; lookup)
import Data.List.Membership.DecPropositional
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Properties using (filter-none; length-filter; map-tabulate)
open import Data.List.Relation.Binary.Subset.Propositional using (_⊆_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁻ˡ; ++⁻ʳ; All¬⇒¬Any; ¬Any⇒All¬)
open import Data.List.Relation.Unary.Any using (Any; any?; here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁻; ++⁺ˡ; ++⁺ʳ; lookup-result; tabulate⁺)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (_∸_; _<_; _≤_; pred; s≤s; suc; z≤n; zero)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (0∸n≡0; ≤-pred; ≤-trans; suc-pred)
open import Data.Product using (∃; ∃-syntax; _×_; _,_) renaming (proj₁ to _₁; proj₂ to _₂)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_; _↔_; _⇔_; Equivalence; λ-; case_of_; const; id; Inverse; mk⇔; _on_)
open import Induction using (Recursor)
open import Induction.WellFounded as Wf using (WellFounded)
open import Level using (Level)
open import Relation.Binary using (DecidableEquality; IsEquivalence)
open import Relation.Binary.Construct.On using (wellFounded)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; ≡-≟-identity; inspect; refl)
open import Relation.Nullary using (¬_; no; yes)
open import Relation.Nullary.Decidable using (dec-false; dec-true; _×-dec_)
open import Relation.Nullary.Negation.Core using (contradiction)
open import Relation.Unary using (_≐_; Decidable; Universal)

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

triples : List A → List (A × A × A)
triples []               = []
triples (_ ∷ [])         = []
triples (_ ∷ _ ∷ [])     = []
triples (x ∷ xs@(y ∷ z ∷ _)) = (x , y , z) ∷ triples xs

last≡nothing⇒[] : {l : List A}
  → last l ≡ nothing
  → l ≡ []
last≡nothing⇒[] {l = []}            _            = refl
last≡nothing⇒[] {l = _ ∷ []}        ()
last≡nothing⇒[] {l = _ ∷ l@(_ ∷ _)} last≡nothing =
  contradiction (last≡nothing⇒[] {l = l} last≡nothing) λ()

last-of-nonempty : {l : List A}
  → l ≢ []
  → ∃[ x ] last l ≡ just x
last-of-nonempty {l = []}        l≢[] = contradiction refl l≢[]
last-of-nonempty {l = l@(_ ∷ _)} l≢[]
  with last l in last≡
...  | nothing = contradiction (last≡nothing⇒[] last≡) l≢[]
...  | just x  = x , refl

head-of-nonempty : {l : List A}
  → l ≢ []
  → ∃[ x ] head l ≡ just x
head-of-nonempty {l = []}    l≢[] = contradiction refl l≢[]
head-of-nonempty {l = x ∷ _} l≢[] = x , refl

∈-++-comm : ∀ {xs ys : List A} {x}
  → x ∈ (xs ++ ys)
  → x ∈ (ys ++ xs)
∈-++-comm {xs = xs} {ys} x∈xs++ys
  with ∈-++⁻ xs x∈xs++ys
...  | inj₁ x∈xs = ∈-++⁺ʳ _ x∈xs
...  | inj₂ x∈ys = ∈-++⁺ˡ   x∈ys

All′ : ∀ {p} → (A → Set p) → List A → Set _
All′ P xs = ∀ {x} → x ∈ xs → P x

module _ where
  open Relation.Binary using (_⇒_) renaming (_⇔_ to _⇔₂_)

  All→All′ : ∀ {p} → All {_} {p} {A} ⇒ All′
  All→All′ (Px ∷ All-P-xs) (here  refl) = Px
  All→All′ (Px ∷ All-P-xs) (there x∈xs) = All→All′ All-P-xs x∈xs

  All′→All : ∀ {p} → All′ ⇒ All {_} {p} {A}
  All′→All {x = P} {y = []}     All-P-xs = []
  All′→All {x = P} {y = x ∷ xs} All-P-xs = All-P-xs (here refl) ∷ All′→All (All-P-xs ∘ there)

  All⇔All′ : ∀ {p} → All {_} {p} {A} ⇔₂ All′
  All⇔All′ = All→All′ , All′→All


⊆-∷⁻ʳ : ∀ {xs ys : List A} {y}
  → y ∉ xs
  → xs ⊆ y ∷ ys
  → xs ⊆ ys
⊆-∷⁻ʳ y∉ys xs⊆y∷ys x∈xs
  with xs⊆y∷ys x∈xs
...  | here  refl = contradiction x∈xs y∉ys
...  | there x∈ys = x∈ys

⊆-∷⁻ˡ : ∀ {xs ys : List A} {x}
  → x ∷ xs ⊆ ys
  → xs ⊆ ys
⊆-∷⁻ˡ = _∘ there

module _ where
  private
    variable
      p q : Level
      P : A → Set p
      Q : A → Set q

  All-→-under-∈ : ∀ {l}
    → (∀ {x} → x ∈ l → P x → Q x)
    → All P l
    → All Q l
  All-→-under-∈ _   []           = []
  All-→-under-∈ P→Q (Px ∷ All-P) =
    let Qx = P→Q (here refl) Px
        All-Q = All-→-under-∈ (P→Q ∘ there) All-P
     in Qx ∷ All-Q

  All-⇔-under-∈ : ∀ {l}
    → (∀ {x} → x ∈ l → P x ⇔ Q x)
    → All P l ⇔ All Q l
  All-⇔-under-∈ P⇔Q =
    mk⇔
      (All-→-under-∈ λ x → to (P⇔Q x))
      (All-→-under-∈ λ x → from (P⇔Q x))
    where open Equivalence

  All-→ : ∀ {l}
    → (∀ x → P x → Q x)
    → All P l
    → All Q l
  All-→ P→Q = All-→-under-∈ (const (P→Q _))

  All-⇔ : ∀ {l}
    → (∀ x → P x ⇔ Q x)
    → All P l ⇔ All Q l
  All-⇔ P⇔Q = All-⇔-under-∈ (const (P⇔Q _))

  Any⁺ : ∀ {l : List A} {x}
    → P x
    → x ∈ l
    → Any P l
  Any⁺ Px (here refl) = here Px
  Any⁺ Px (there x∈l) = there (Any⁺ Px x∈l)

  Any-≡⁻ : ∀ {l : List A} {x}
    → Any (x ≡_) l
    → x ∈ l
  Any-≡⁻ (here  refl)   = here  refl
  Any-≡⁻ (there Any-x≡) = there Any-x≡

  Any-≡⁺ : ∀ {l : List A} {x}
    → x ∈ l
    → Any (x ≡_) l
  Any-≡⁺ (here refl) = here refl
  Any-≡⁺ (there x∈l) = there x∈l


module _ {p} {P : A → Set p} (P? : Decidable P) {q} {Q : A → Set q} (Q? : Decidable Q) where
  Any-filter⇒Any-× : {l : List A}
    → Any P (filter Q? l)
    → Any (P -×- Q) l
  Any-filter⇒Any-× {x ∷ l} Any-filter
    with Q? x   | P? x
  ...  | no ¬Qx | _      = there (Any-filter⇒Any-× Any-filter)
  ...  | yes Qx | yes Px = here (Px , Qx)
  ...  | yes Qx | no ¬Px
          with Any-filter
  ...        | here  Px         = here (Px , Qx)
  ...        | there Any-filter = there (Any-filter⇒Any-× Any-filter)

  Any-×⇒Any-filter : {l : List A}
    → Any (P -×- Q) l
    → Any P (filter Q? l)
  Any-×⇒Any-filter {x ∷ l} (here (Px , Qx))
    with Q? x
  ...  | no ¬Qx = contradiction Qx ¬Qx
  ...  | yes Qx = here Px
  Any-×⇒Any-filter {x ∷ l} (there Any-P×Q)
    with Q? x
  ...  | no ¬Qx = Any-×⇒Any-filter Any-P×Q
  ...  | yes Qx
          with P? x
  ...        | no ¬Px = there (Any-×⇒Any-filter Any-P×Q)
  ...        | yes Px = here Px

  module _ where
    open Eq using ([_])

    filter-× : (l : List A)
      → filter (P? -×-dec- Q?) l ≡ filter P? (filter Q? l)
    filter-× [] = refl
    filter-× (x ∷ l)
      with Q? x   | inspect Q? x | P? x   | inspect P? x
    ...  | no ¬Qx | [ Qx≡ ]      | no ¬Px | [ Px≡ ] rewrite Qx≡ | Px≡ | filter-× l = refl
    ...  | no ¬Qx | [ Qx≡ ]      | yes Px | [ Px≡ ] rewrite Qx≡ | Px≡ | filter-× l = refl
    ...  | yes Qx | [ Qx≡ ]      | no ¬Px | [ Px≡ ] rewrite Qx≡ | Px≡ | filter-× l = refl
    ...  | yes Qx | [ Qx≡ ]      | yes Px | [ Px≡ ] rewrite Qx≡ | Px≡ | filter-× l = refl


  filter-⇔-under-∈ : ∀ {l}
    → (∀ {x} → x ∈ l → P x ⇔ Q x)
    → filter P? l ≡ filter Q? l
  filter-⇔-under-∈ {[]}    P⇔Q = refl
  filter-⇔-under-∈ {x ∷ l} P⇔Q
    with P? x
  ...  | no ¬Px rewrite dec-false (Q? x) (Equivalence.to (¬-distr-⇔ (P⇔Q (here refl))) ¬Px) | filter-⇔-under-∈ (P⇔Q ∘ there) = refl
  ...  | yes Px rewrite dec-true  (Q? x) (Equivalence.to            (P⇔Q (here refl))   Px) | filter-⇔-under-∈ (P⇔Q ∘ there) = refl

  filter-≐ : (l : List A)
    → P ≐ Q
    → filter P? l ≡ filter Q? l
  filter-≐ l P≐Q = filter-⇔-under-∈ {l = l} (const (mk⇔ (P≐Q ₁) (P≐Q ₂)))


strong-induction-on-length : ∀ {p} (P : List A → Set p)
  → P []
  → (∀ {xs} {∣xs∣-1} → length xs ≡ suc ∣xs∣-1 → (∀ ys → length ys ≤ ∣xs∣-1 → P ys) → P xs)
  → Π[ P ]
strong-induction-on-length P base step = wfRec _ P λ where
    []       P-ind → base
    (x ∷ xs) P-ind → step refl λ ys → P-ind ys ∘ s≤s
  where open Wf.All (wellFounded length <-wellFounded) using (wfRec)

_−_ : ∀ {x} (xs : List A) → x ∈ xs → List A
(_ ∷ xs) − here  refl = xs
(x ∷ xs) − there y∈xs = x ∷ (xs − y∈xs)

length∘−x≡pred∘length : ∀ {xs : List A} {x} (x∈xs : x ∈ xs) → length (xs − x∈xs) ≡ pred (length xs)
length∘−x≡pred∘length                       (here  refl)           = refl
length∘−x≡pred∘length {xs = _ ∷     _ ∷ _}  (there (here refl))    = refl
length∘−x≡pred∘length {xs = _ ∷ xs@(_ ∷ _)} (there x∈xs@(there _))
  rewrite length∘−x≡pred∘length x∈xs
        = suc-pred (length xs)

module DecEq (_≟_ : DecidableEquality A) where
  open Data.List.Membership.DecPropositional _≟_ using (_∈?_; _∉?_)
  open Data.List.Membership.Propositional.Properties using (∈-allFin; ∈-filter⁻; ∈-filter⁺; ∈-lookup; ∈-map⁺)

  module _ {p} {P : A → Set p} (P? : Decidable P) where
    filter-with-∈ : (l : List A)
      → filter P? l ≡ filter ((_∈? l) -×-dec- P?) l
    filter-with-∈ [] = refl
    filter-with-∈ (x ∷ l) rewrite ≡-≟-identity _≟_ {x = x} refl
      with P? x
    ...  | no ¬Px rewrite filter-with-∈ l
           = filter-≐ ((_∈? l) -×-dec- P?) ((_∈? x ∷ l) -×-dec- P?) l
               ( (λ{ (y∈l , Py) → there y∈l , Py })
               , (λ{ (here refl , Px) → contradiction Px ¬Px
                   ; (there y∈l , Py) → y∈l , Py
                   })
               )
    ...  | yes Px rewrite filter-with-∈ l
           = Eq.cong (x ∷_)
               (filter-⇔-under-∈ ((_∈? l) -×-dec- P?) ((_∈? x ∷ l) -×-dec- P?) {l = l} λ y∈l →
                  mk⇔
                    (λ{ (y∈l   , Py) → there y∈l , Py })
                    (λ{ (y∈x∷l , Py) →       y∈l , Py }))

    indices-where : (l : List A) → List (Fin (length l))
    indices-where l = filter (P? ∘ lookup l) (allFin (length l))

    module _ where
      open Causality.Relation.Nullary

      indices-where-correct : ∀ {l : List A} {i}
        → P (lookup l i) ⇔ (i ∈ indices-where l)
      indices-where-correct {l} {i} = mk⇔ ⟶ ⟵
        where
        ⟶ : P (lookup l i) → i ∈ indices-where l
        ⟶ = ∈-filter⁺ (P? ∘ lookup l) (∈-allFin i)

        ⟵ : i ∈ indices-where l → P (lookup l i)
        ⟵ i∈iw-l = ∈-filter⁻ (P? ∘ lookup l) {xs = allFin _} i∈iw-l ₂

      filter-∈filter : (l : List A)
        → filter (_∈? (filter P? l)) l ≡ filter P? l
      filter-∈filter [] = refl
      filter-∈filter (x ∷ l)
        with P? x
      ...  | no ¬Px
            with any? (x ≟_) (filter P? l)
      ...       | no  x∉ = filter-∈filter l
      ...       | yes x∈ = contradiction (∈-filter⁻ P? {xs = l} (Any-≡⁻ x∈) ₂) ¬Px
      filter-∈filter (x ∷ l)
          | yes Px rewrite ≡-≟-identity _≟_ (refl {x = x})
            = Eq.cong (x ∷_)
                (filter-⇔-under-∈ (λ _ → any? (_ ≟_) _) P? lemma)
            where
            lemma : ∀ {y} → y ∈ l → (y ∈ x ∷ filter P? l) ⇔ P y
            lemma y∈l =
              mk⇔
                (λ{ (here  refl)     → Px
                  ; (there y∈filter) → ∈-filter⁻ P? {xs = l} (Any-≡⁻ y∈filter) ₂
                  })
                (λ Py → there (∈-filter⁺ P? y∈l Py))


  module _ where
    open Causality.Relation.Nullary

    find-indices : (l : List A) → A → List (Fin (length l))
    find-indices l x = indices-where (x ≟_) l

    find-indices-correct : ∀ {l : List A} {x} {i : Fin (length l)}
      → (x ≡ lookup l i) ⇔ (i ∈ find-indices l x)
    find-indices-correct {l} = indices-where-correct (_ ≟_) {l = l}
```
