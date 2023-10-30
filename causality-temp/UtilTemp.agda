module Causality.Util where


module _ where
  open import Data.Product using (Σ-syntax; _,_)

  uncurry₃ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} {D : {x : A} → {y : B x} → C y → Set d}
    → ((x : A) → (y : B x) → (z : C y) → D z)
    → ((x , y , z) : Σ[ x ∈ A ] Σ[ y ∈ B x ] C y)
    → D z
  uncurry₃ f (x , y , z) = f x y z


module _ where
  open import Data.Nat using (_<_; _≤_; s≤s; suc)

  -- From https://agda.github.io/agda-stdlib/Data.Nat.Properties.html#12927.
  m<1+n⇒m≤n : ∀ {m n} → m < suc n → m ≤ n
  m<1+n⇒m≤n (s≤s m≤n) = m≤n


module _ where
  open import Data.Fin using (_ℕ-_; _ℕ-ℕ_; suc; toℕ; zero)
  open import Data.Fin.Properties using (toℕ-fromℕ)
  open import Data.Nat using (suc; zero)
  open import Relation.Binary.PropositionalEquality using (_≡_; sym)

  -- From https://agda.github.io/agda-stdlib/Data.Fin.Properties.html#28468.
  ℕ-ℕ≡toℕ‿ℕ- : ∀ n i → n ℕ-ℕ i ≡ toℕ (n ℕ- i)
  ℕ-ℕ≡toℕ‿ℕ- n       zero    = sym (toℕ-fromℕ n)
  ℕ-ℕ≡toℕ‿ℕ- (suc n) (suc i) = ℕ-ℕ≡toℕ‿ℕ- n i


module _ where
  open import Data.Fin using (_+_; _ℕ-_; _ℕ-ℕ_; Fin; inject≤; suc; toℕ)
  open import Data.Fin.Properties using (toℕ<n; toℕ‿ℕ-)
  open import Data.Nat as ℕ using (_∸_; _≤_)
  open import Data.Nat.Properties using (m+[n∸m]≡n; n≤1+n)
  open Data.Nat.Properties.≤-Reasoning using (begin_; step-≡; _≡⟨⟩_; step-≤; _∎)
  import Relation.Binary.PropositionalEquality as Eq

  _+′_ : ∀ {n} (i : Fin n) → Fin (n ℕ-ℕ suc i) → Fin n
  _+′_ {n} i j =
    inject≤ (i + j)
      (begin
          toℕ i ℕ.+ (n ℕ-ℕ suc i)
        ≤⟨ n≤1+n _ ⟩
          toℕ (suc i) ℕ.+ (n ℕ-ℕ suc i)
        ≡⟨ Eq.cong (toℕ (suc i) ℕ.+_) (ℕ-ℕ≡toℕ‿ℕ- n (suc i)) ⟩
          toℕ (suc i) ℕ.+ toℕ (n ℕ- suc i)
        ≡⟨ Eq.cong (toℕ (suc i) ℕ.+_) (toℕ‿ℕ- n (suc i)) ⟩
          toℕ (suc i) ℕ.+ (n ∸ toℕ (Fin.suc i))
        ≡⟨⟩
          toℕ (suc i) ℕ.+ (n ∸ ℕ.suc (toℕ i))
        ≡⟨ m+[n∸m]≡n (toℕ<n i) ⟩
          n
        ∎)
