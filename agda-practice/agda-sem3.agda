module agda-sem3 where

{-
data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x

-- J elimination rule
≡-elim : {X : Set}
     → (A : (x y : X) → x ≡ y → Set)
     → ((x : X) → A x x (refl))
     → (x y : X) → (p : x ≡ y) → A x y p
≡-elim A f x x (refl) = f x

-- cong, sym, trans derived from J
-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)

open import Agda.Primitive

-- X : Set
-- Y : Set 
-- X → Y : Set
-- WRONG Set : Set -- Girard's paradox (Russel's paradox)
-- Type Levels
-- Int; Bool; X → Y : Set₀
-- Set₀ : Set₁ : Set₂ : Set₃ : ...
-- https://agda.readthedocs.io/en/latest/language/sort-system.html#introduction-to-universes

record Group {ℓ : Level} : Set (lsuc ℓ) where
  infixl 40 _⊕_
  field
    Carrier : Set ℓ
    _⊕_ : Carrier → Carrier → Carrier
    ε : Carrier
    inv : Carrier → Carrier

    assoc : (x y z : Carrier) → x ⊕ (y ⊕ z) ≡ (x ⊕ y) ⊕ z 
    left-id : (x : Carrier) → ε ⊕ x ≡ x
    right-id : (x : Carrier) → x ⊕ ε ≡ x
    left-inv : (x : Carrier) → (inv x) ⊕ x ≡ ε
    right-inv : (x : Carrier) → x ⊕ (inv x) ≡ ε

module GroupProps {ℓ : Level} (G : Group {ℓ}) where
  open Group G public

  -- there is exactly one ε
  unique-identity : (e' : Carrier)
                  → (left-id' : (x : Carrier) → e' ⊕ x ≡ x)
                  → (right-id' : (x : Carrier) → x ⊕ e' ≡ x)
                  → e' ≡ ε
  -- ε = e' + ε = e'
  unique-identity e' left-id' right-id' = h where
    p₁ : e' ⊕ ε ≡ ε
    p₁ = left-id' ε
    p₂ : e' ⊕ ε ≡ e'
    p₂ = right-id e'
    p₃ : e' ≡ e' ⊕ ε
    p₃ = sym p₂
    h = trans p₃ p₁

  unique-inv : (a : Carrier) → (a' : Carrier)
             → (a' ⊕ a ≡ ε) → (a ⊕ a' ≡ ε)
             → a' ≡ inv a
  -- a' = a' ⊕ ε = a' ⊕ a ⊕ inv a = ε ⊕ inv a = inv a
  unique-inv a a' left-inv' right-inv' = p where
    step₁ : a' ≡ a' ⊕ ε
    step₁ = sym (right-id a')
    step₂ : a' ⊕ ε ≡ a' ⊕ (a ⊕ inv a)
    step₂ = cong (a' ⊕_) (sym (right-inv a))
    step₃ : a' ⊕ (a ⊕ inv a) ≡ (a' ⊕ a) ⊕ inv a
    step₃ = assoc a' a (inv a)
    step₄ : (a' ⊕ a) ⊕ inv a ≡ ε ⊕ inv a
    step₄ = cong (_⊕ inv a) left-inv'
    step₅ : ε ⊕ inv a ≡ inv a
    step₅ = left-id (inv a)
    p = trans step₁ (trans step₂ (trans step₃ (trans step₄ step₅)))

  -- ≡-Reasoning
  unique-inv' : (a : Carrier) → (a' : Carrier)
              → (a' ⊕ a ≡ ε) → (a ⊕ a' ≡ ε)
              → a' ≡ inv a
  unique-inv' a a' left-inv' right-inv' =
    begin
      a'
    ≡⟨ sym (right-id a') ⟩
      a' ⊕ ε
    ≡⟨ cong (a' ⊕_) (sym (right-inv a)) ⟩
      a' ⊕ (a ⊕ inv a)
    ≡⟨ assoc a' a (inv a) ⟩
      (a' ⊕ a) ⊕ inv a
    ≡⟨ cong (_⊕ inv a) left-inv' ⟩
      ε ⊕ inv a
    ≡⟨ left-id (inv a) ⟩
      inv a
    ∎

  inv-id : inv ε ≡ ε
  inv-id =
    begin
      inv ε
    ≡⟨ sym (right-id (inv ε)) ⟩
      inv ε ⊕ ε
    ≡⟨ left-inv ε ⟩
      ε
    ∎

  -- (inv b + inv a) + (a + b) = ε
  -- (a + b) + (inv b + inv a) = ε
  inv-plus : (a b : Carrier)
           → inv (a ⊕ b) ≡ inv b ⊕ inv a
  inv-plus a b = p where
    left-inv' : (inv b ⊕ inv a) ⊕ (a ⊕ b) ≡ ε
    left-inv' =
      begin
        (inv b ⊕ inv a) ⊕ (a ⊕ b)
      ≡⟨ assoc (inv b ⊕ inv a) a b ⟩
        ((inv b ⊕ inv a) ⊕ a) ⊕ b
      ≡⟨ cong (_⊕ b) (sym (assoc (inv b) (inv a) a)) ⟩
        inv b ⊕ (inv a ⊕ a) ⊕ b
      ≡⟨ cong (λ x → inv b ⊕ x ⊕ b) (left-inv a) ⟩
        inv b ⊕ ε ⊕ b
      ≡⟨ cong (_⊕ b) (right-id (inv b)) ⟩
        inv b ⊕ b
      ≡⟨ left-inv b ⟩
        ε
      ∎
    right-inv' : (a ⊕ b) ⊕ (inv b ⊕ inv a) ≡ ε
    right-inv' = 
      begin
        (a ⊕ b) ⊕ (inv b ⊕ inv a)
      ≡⟨ assoc (a ⊕ b) (inv b) (inv a) ⟩
        ((a ⊕ b) ⊕ inv b) ⊕ inv a
      ≡⟨ cong (_⊕ inv a) (sym (assoc a b (inv b))) ⟩
        (a ⊕ (b ⊕ inv b)) ⊕ inv a
      ≡⟨ cong (λ x → (a ⊕ x) ⊕ inv a) (right-inv b) ⟩
        (a ⊕ ε) ⊕ inv a
      ≡⟨ cong (_⊕ inv a) (right-id a) ⟩
        a ⊕ inv a
      ≡⟨ right-inv a ⟩
        ε
      ∎
    h : inv b ⊕ inv a ≡ inv (a ⊕ b)
    h = unique-inv (a ⊕ b) (inv b ⊕ inv a) left-inv' right-inv'
    p = sym h

  -- rewrite
  -- Goal : x ≡ y
  -- p : x ≡ z
  -- rewrite p
  -- New goal : z ≡ y
  inv-plus' : (a b : Carrier)
            → inv (a ⊕ b) ≡ inv b ⊕ inv a
  inv-plus' a b = p where
    right-inv' : (a ⊕ b) ⊕ (inv b ⊕ inv a) ≡ ε
    right-inv' rewrite assoc (a ⊕ b) (inv b) (inv a)
                     | sym (assoc a b (inv b))      -- a ⊕ b ⊕ inv b ≡ a ⊕ (b ⊕ inv b)
                     | right-inv b
                     | right-id a
                     | right-inv a
                     = refl
    left-inv' : (inv b ⊕ inv a) ⊕ (a ⊕ b) ≡ ε
    left-inv' rewrite assoc (inv b ⊕ inv a) a b
                    | sym (assoc (inv b) (inv a) a)
                    | left-inv a
                    | right-id (inv b)
                    | left-inv b
                    = refl
    p = sym (unique-inv (a ⊕ b) (inv b ⊕ inv a) left-inv' right-inv')

  leftMul : Carrier → Carrier → Carrier
  leftMul g x = g ⊕ x

  -- Note: Actually, levels here should be choosen more precise, but for current setup it is ok
  _∘_ : {ℓ : Level} {A B : Set ℓ} {C : B → Set ℓ} 
      → (g : (x : B) → C x)
      → (f : A → B)
      → (x : A) → C (f x)
  (g ∘ f) x = g (f x)
  infixl 0 _∘_

  id : {ℓ : Level} → {A : Set ℓ} → A → A
  id x = x

  -- inv (leftMul g) = leftMul (inv g)
  -- (leftMul g) ∘ (leftMul (inv g)) ≡ id
  -- Pointwise equality
  -- ∀ x → f x ≡ g x
  -- ~ - homotopy
  _~_ : {ℓ : Level} {A : Set ℓ} → {B : A → Set ℓ}
      → (f : (x : A) → B x)
      → (g : (x : A) → B x)
      → Set ℓ
  f ~ g = ∀ x → f x ≡ g x
  -- we can show that ~-sym, ~-trans, ~-refl holds
  -- but we can't make Group from it
  -- since for group we must show that ≡ holds

  -- function extensionality is axiom for MLTT which allows to lift homotopy to ≡
  postulate
    funext : {ℓ : Level} {A : Set ℓ} {B : A → Set ℓ} {f g : (x : A) → B x} → f ~ g → f ≡ g

  -- In HoTT funext is not an axiom but a consenquence of the Univalence Axiom!
  -- In Cubical type theory (computational HoTT) funext also computable and can be proven

