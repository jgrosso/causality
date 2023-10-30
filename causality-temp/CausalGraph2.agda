module CausalGraph where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
import Data.Fin.Properties as Fin
open import Data.Fin.Subset using (Subset; _⊆_; ⁅_⁆; _∪_; _∩_; ⋃; Empty) renaming (_─_ to _∖_)
import Data.Fin.Subset as Fin
import Data.Fin.Subset.Properties as Fin
open import Data.List using (List; _∷_; []; all; filter; head; last; map)
import Data.List as List
import Data.List.Membership.DecPropositional
open import Data.List.Relation.Unary.Linked using (Linked)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; _≥_; s≤s)
open import Data.Product using (∃; ∃-syntax; Σ; Σ-syntax; _×_; _,_; proj₁)
import Data.Product.Properties as Σ
open import Data.Sum using (_⊎_)
open import Function using (_∘_; _∘₂_; _-⟨_⟩-_; case_of_; flip)
open import Level using (_⊔_; suc)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; Dec)
open import Relation.Nullary.Decidable.Core using (True)
open import Relation.Nullary.Sum using (_⊎-dec_)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Unary using (Decidable)

triples : ∀ {a} {A : Set a} → List A → List (A × A × A)
triples []               = []
triples (_ ∷ [])         = []
triples (_ ∷ _ ∷ [])     = []
triples (x ∷ xs@(y ∷ z ∷ _)) = (x , y , z) ∷ triples xs

⁅_⁆₂ : ∀ {n} → Fin n × Fin n → Subset n
⁅ i , j ⁆₂ = ⁅ i ⁆ ∪ ⁅ j ⁆

disjoint : ∀ {n} → Subset n → Subset n → Set
disjoint S T = Empty (S ∩ T)

_⊆∖_ : ∀ {n} → Subset n → Subset n → Set
S ⊆∖ T = S ⊆ (Fin.⊤ ∖ T)

_-×-_ : ∀ {a b c} {A : Set a} → (A → Set b) → (A → Set c) → (A → Set _)
P -×- Q = λ x → P x × Q x

_-⊎-_ : ∀ {a b c} {A : Set a} → (A → Set b) → (A → Set c) → (A → Set _)
P -⊎- Q = λ x → P x ⊎ Q x

last≡nothing⇒[] : ∀ {a} {A : Set a} {l : List A}
  → last l ≡ nothing
  → l ≡ []
last≡nothing⇒[] {l = []}         _  = refl
last≡nothing⇒[] {l = _ ∷ []}     ()
last≡nothing⇒[] {l = _ ∷ l@(_ ∷ _)} last≡nothing
  with last≡nothing⇒[] {l = l} last≡nothing
...  | ()

last-of-nonempty : ∀ {a} {A : Set a} {l : List A}
  → l ≢ []
  → ∃[ x ] last l ≡ just x
last-of-nonempty {l = []} l≢[] = ⊥-elim (l≢[] refl)
last-of-nonempty {l = l@(_ ∷ _)} l≢[]
  with last l in last≡
...  | nothing = ⊥-elim (l≢[] (last≡nothing⇒[] last≡))
...  | just x  = x , refl

head-of-nonempty : ∀ {a} {A : Set a} {l : List A}
  → l ≢ []
  → ∃[ x ] head l ≡ just x
head-of-nonempty {l = []} l≢[] = ⊥-elim (l≢[] refl)
head-of-nonempty {l = x ∷ _} l≢[] = x , refl

All : ∀ {a n} (P : Fin n → Set a) (S : Subset n) → Set _
All P S = ∀ x → x ∈ S → P x
  where open Data.Fin.Subset using (_∈_)

Any : ∀ {a n} (P : Fin n → Set a) (S : Subset n) → Set _
Any P S = ∃[ x ] x ∈ S × P x
  where open Data.Fin.Subset using (_∈_)

_-⊎-dec-_ : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q}
  → Decidable P
  → Decidable Q
  → Decidable (P -⊎- Q)
p -⊎-dec- q = λ x → p x ⊎-dec q x

record DirectedMultigraph : Set where
  field |V| : ℕ

  V : Set
  V = Fin |V|

  Edge : Set
  Edge = V × V

  ≟-Edge : DecidableEquality Edge
  ≟-Edge = Σ.≡-dec Fin._≟_ Fin._≟_

  field E : List Edge

  _∃⟶_ : (i j : V) → Dec _
  i ∃⟶ j = (i , j) ∈? E
    where open Data.List.Membership.DecPropositional ≟-Edge using (_∈?_)

  _∃⟵_ : (i j : V) → Dec _
  _∃⟵_ = flip _∃⟶_

  _∃——_ : (i j : V) → Dec _
  i ∃—— j = i ∃⟶ j ⊎-dec j ∃⟶ i

  DirectedPath : Set
  DirectedPath = Σ (List V) (Linked (True ∘₂ _∃⟶_))

  acyclic-path : DirectedPath → Set
  acyclic-path = Unique ∘ proj₁

record DirectedGraph : Set where
  field base : DirectedMultigraph
  open DirectedMultigraph base public

  field simple : Unique E

record DAG : Set where
  field base : DirectedGraph
  open DirectedGraph base public

  field acyclic : (p : DirectedPath) → acyclic-path p

module CausalGraph (G : DAG) where
  open DAG G

  record Path : Set where
    field nodes              : List V
    field distinct-endpoints : List.length nodes ≥ 2
    field linked             : Linked (True ∘₂ _∃——_) nodes
    field acyclic            : Unique nodes

    nonempty : nodes ≢ []
    nonempty nodes≡[]
      with nodes | distinct-endpoints
    ...  | []    | ()
    ...  | _ ∷ _ | s≤s _ = case nodes≡[] of λ()

    start : V
    start = proj₁ (head-of-nonempty nonempty)

    end : V
    end = proj₁ (last-of-nonempty nonempty)

  open Path

  _—↠_ : V → V → Set
  from —↠ to = ∃[ p ] start p ≡ from × end p ≡ to

  triples-along : Path → List (V × V × V)
  triples-along = triples ∘ nodes

  _visits_ : (p : Path) → (v : V) → Dec _
  p visits v = v ∈? nodes p
    where open Data.List.Membership.DecPropositional Fin._≟_ using (_∈?_)

  ConditioningSet : V → V → Set _
  ConditioningSet i j = Σ (Subset |V|) (_⊆∖ ⁅ i , j ⁆₂)

  ∅ : ∀ {i j} → ConditioningSet i j
  ∅ = Fin.⊥ , Fin.⊥⊆

  module Pattern where
    record Pattern {a} : Set (suc a) where
      field predicate  : V × V × V → Set a
      field _matches?_ : Decidable predicate

    open Pattern

    module Notation where
      _·_ : ∀ {a b} {P : Set a} {Q : Set b} → (V → V → Dec P) → (V → V → Dec Q) → Pattern
      _·_ {P = P} {Q = Q} _l-x_ _x-r_ = record
        { predicate  = λ{ (l , x , r) → !!} }
        ; _matches?_ = λ{ (l , x , r) → {!Fin.decFinSubset !} }
        }

      ⟶ = _∃⟶_

      ⟵ = _∃⟵_

      _or_ : ∀ {a b} → Pattern {a} → Pattern {b} → Pattern {a ⊔ b}
      pat₁ or pat₂ = record
        { predicate  = predicate pat₁ -⊎- predicate pat₂
        ; _matches?_ = (pat₁ matches?_) -⊎-dec- (pat₂ matches?_)
        }

    open Notation

    collider common-cause mediator : Pattern
    collider     = ⟶ · ⟵
    common-cause = ⟵ · ⟶
    mediator     = ⟶ · ⟶

    noncollider : Pattern
    noncollider = common-cause or mediator

    colliders     = collider
    common-causes = common-cause
    mediators     = mediator
    noncolliders  = noncollider

    _along_ : ∀ {a} → Pattern {a} → Path → Subset |V|
    pat along p =
      let matches : List (V × V × V)
          matches = filter (pat matches?_) (triples-along p)

          nodes : List (Subset |V|)
          nodes = map (λ{ (_ , x , _) → ⁅ x ⁆ }) matches
       in ⋃ nodes

  open Pattern

  descendants : V → Subset |V|
  descendants i = {!!}

  unblocked_∣_ : ∀ {i j} → i —↠ j → ConditioningSet i j → Set
  unblocked (p , _) ∣ (C , _) =
    disjoint (noncolliders along p) C ×
    All (λ i → i ∈ C ⊎ Any (_∈ C) (descendants i))
        (colliders along p)
    where open Data.Fin.Subset using (_∈_)

  blocked_∣_ : ∀ {i j} → i —↠ j → ConditioningSet i j → Set
  blocked p ∣ C = ¬ unblocked p ∣ C

  _⫫_∣_ : (i j : V) → ConditioningSet i j → Set
  i ⫫ j ∣ C = ∀ p → blocked p ∣ C

  _⫫̸_∣_ : (i j : V) → ConditioningSet i j → Set
  i ⫫̸ j ∣ C = ¬ i ⫫ j ∣ C

  _⫫_ : V → V → Set
  i ⫫ j = i ⫫ j ∣ ∅

  _⫫̸_ : V → V → Set
  i ⫫̸ j = i ⫫̸ j ∣ ∅
