simple : ∀ {a b} {N : Set a} {E : Set b} {n} → DAG N E n → Set
simple g = {!!}

module Graph {n : ℕ} (G : CausalGraph n) where

  Node : Set
  Node = Fin n


  V : Subset n
  V = complete-Subset


  ConditioningSet : Node → Node → Set
  ConditioningSet i j = ∃[ C ] C ⊆ V ∖ ⁅ i , j ⁆₂


  ∅ : ∀ {i j} → ConditioningSet i j
  ∅ = empty-Subset , ⊥⊆


  _∃⟶_ : Node → Node → Set
  i ∃⟶ j
    with i Fin.<? j
  ...  | no  _ = ⊥
  ...  | yes i<j =
         (_ , Fin.cast {!!} (Fin.fromℕ (toℕ j ∸ suc (toℕ i)))) ∈ sucs (Σ.proj₁ G) i
  --  Fin.cast {!!} (j Fin.- inject< (Fin.suc i) (ℕ.s≤s i<j))


  ∃⟶-irrefl : ∀ {i} → ¬ i ∃⟶ i
  ∃⟶-irrefl {Fin.zero} x = {!!}
  ∃⟶-irrefl {Fin.suc i} x = {!!}


  record _⟶_ (start : Node) (end : Node) : Set where

    field open-path : start ≢ end


    field intermediates : List Node


    path : List Node
    path = start ∷ intermediates ∷ʳ end


    field linked : Linked _∃⟶_ path


    tail :
      case intermediates of λ where
        []          → ⊤
        (start ∷ _) → start ⟶ end
    tail with intermediates
    ... | []                    = _
    ... | start ∷ intermediates = record { open-path = {!!} ; intermediates = {!!} ; linked = {!!} }

  open _⟶_


  _is-on_ : ∀ {i j} → Node → i ⟶ j → Set
  x is-on p = x ∈ path p


  _is-collider-along_ : ∀ {i j} → Node → i ⟶ j → Set
  x is-collider-along p = Any is-collider (triples (path p))
    where
    is-collider : Node × Node × Node → Set
    is-collider (l , x′ , r) =
      x ≡ x′ × l ∃⟶ x × r ∃⟶ x


  _is-common-cause-along_ : ∀ {i j} → Node → i ⟶ j → Set
  x is-common-cause-along p = Any is-common-cause (triples (path p))
    where
    is-common-cause : Node × Node × Node → Set
    is-common-cause (l , x′ , r) =
      x ≡ x′ × x ∃⟶ l × x ∃⟶ r


  _is-mediator-along_ : ∀ {i j} → Node → i ⟶ j → Set
  x is-mediator-along p = Any is-mediator (triples (path p))
    where
    is-mediator : Node × Node × Node → Set
    is-mediator (l , x′ , r) =
      x ≡ x′ × l ∃⟶ x × x ∃⟶ r


  _is-noncollider-along_ : ∀ {i j} → Node → i ⟶ j → Set
  x is-noncollider-along p =
    x is-common-cause-along p ⊎ x is-mediator-along p


  unblocked?_∣_ : ∀ {i j} → i ⟶ j → ConditioningSet i j → Set
  unblocked? p ∣ C = {!!}


  _⫫_∣_ : (i j : Node) → ConditioningSet i j → Set
  i ⫫ j ∣ C = ∄[ p ] unblocked? p ∣ C


  _⫫_ : Node → Node → Set
  A ⫫ B = A ⫫ B ∣ ∅


  module Properties where

    nodes-unique : ∀ {i j} (p : i ⟶ j)
      → Unique (path p)
    nodes-unique p
      with path p
    ...  | []     = []
    ...  | x ∷ xs = {!!} ∷ {!nodes-unique!}


    classify-node-along-path : ∀ {i j} (p : i ⟶ j) x
      → x is-on p
      → x ≡ i                    ⊎
        x ≡ j                    ⊎
        x is-collider-along    p ⊎
        x is-noncollider-along p
    classify-node-along-path p = {!!}
