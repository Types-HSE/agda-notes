module agda_sem2 where


-- MLTT (Martin-Lof type theory)
-- inductive types
-- Curry-Howard correspondence
-- ⊥ = \bot
data ⊥ : Set where

-- eliminator (induction)
-- Dependent type A indexed by ℕ - A : ℕ → Set -- A 0, A 1, A 2, A 3, ...
⊥-elim : {A : ⊥ → Set} (x : ⊥) → A x
⊥-elim ()

-- recursor is independent version of eliminator
⊥-rec : {A : Set} (x : ⊥) → A
⊥-rec {A} = ⊥-elim {λ _ → A}

-- \lnot
¬_ : Set → Set
¬ A = A → ⊥

infix 1000 ¬_

is-empty : Set → Set
is-empty A = A → ⊥

-- Unit type
data ⊤ : Set where
  tt : ⊤

non-empty-⊤ : ¬ is-empty ⊤
non-empty-⊤ = λ { f → f tt }

-- dependent type B : A → Set . a : A  B a
-- B : A → Set       - predicate
-- for a : A  -  B a - proposition
-- B a true if not empty
-- Π-type = Dependent function = ∀ x
⊤-elim : {A : ⊤ → Set}   -- ∀ A - predicate on ⊤
       → A tt            -- If A holds on tt
       → ∀ (x : ⊤) → A x -- then ∀ x : ⊤, A x holds
⊤-elim a tt = a


-- Bool (𝟚 \b2)
data 𝟚 : Set where
  𝟎 𝟏 : 𝟚 -- \B0 \B1

𝟚-elim : {A : 𝟚 → Set}  -- ∀ A - predicate on 𝟚
       → A 𝟎            -- if A holds on 𝟎
       → A 𝟏            -- and A holds on 𝟏
       → (x : 𝟚) → A x  -- then ∀ x : 𝟚, A x holds
𝟚-elim a₀ a₁ 𝟎 = a₀
𝟚-elim a₀ a₁ 𝟏 = a₁

not : 𝟚 → 𝟚
not b = 
  𝟚-elim
    {λ _ → 𝟚}          -- A : 𝟚 → Set
    𝟏                  -- A 𝟎
    𝟎                  -- A 𝟏
    b

𝟚-rec : {A : Set} → A → A → (𝟚 → A)
𝟚-rec {A} = 𝟚-elim {λ _ → A}

not' : 𝟚 → 𝟚
not' b = 𝟚-rec 𝟏 𝟎 b

-- Sigma type (Dependent pairs)
-- Σ = \Sigma
-- B : A → Set
-- Σ {A} (λ a : A → B a)
-- Σ x ꞉ A , B x
-- ∃ x : A , B x
record Σ {A : Set} (B : A → Set) : Set where
  constructor
    _,_
  field
    pr₁ : A
    pr₂ : B pr₁

Sigma : (A : Set) → (B : A → Set) → Set
Sigma A B = Σ {A} B

--                            \: since simply : reserved by agda
syntax Sigma A (λ x → b) = Σ x ꞉ A , b
infix -1 Sigma

open import agda_sem1 using (ℕ ; suc ; zero)

D : 𝟚 → Set
D 𝟎 = ℕ
D 𝟏 = 𝟚

ex₁ ex₂ : Σ b ꞉ 𝟚 , D b
ex₁ = (𝟎 , 23)
ex₂ = (𝟏 , 𝟎)

-- A0 → A1 → ... → An → C == (A0 × A1 × A2 ... × An) → C
-- Σ-elim is curry
Σ-elim : {A : Set} {B : A → Set}
       → {C : (Σ x ꞉ A , B x) → Set}
       → ((x : A) → (y : B x) → C(x , y)) -- f
       → (z : Σ x ꞉ A , B x) → C z
Σ-elim f (x , y) = f x y

-- × = \x
-- A × B = A ∧ B
_×_ : Set → Set → Set
A × B = Σ x ꞉ A , B

-- ∔ = \.+
-- A ∔ B = A ∨ B
data _∔_ (A B : Set) : Set where
  inl : A → A ∔ B
  inr : B → A ∔ B


-- To show that for any z : A ∔ B, C z holds we must show that
-- for any x : A we can prove (transform evidence) C (inl x)
-- and for any y : B we can prove C (inr y)
∔-elim : {A B : Set} {C : A ∔ B → Set}
       → ((x : A) → C (inl x)) -- f
       → ((y : B) → C (inr y)) -- g
       → (z : A ∔ B) → C z
∔-elim f g (inl x) = f x
∔-elim f g (inr y) = g y

-- induction principle for ℕ
ℕ-elim : {A : ℕ → Set}
       → A 0                           -- base case
       → ((n : ℕ) → A n → A (suc n))   -- step
       → (n : ℕ) → A n
ℕ-elim a₀ f zero = a₀
ℕ-elim a₀ f (suc n) = f n (ℕ-elim a₀ f n)


_+_ : ℕ → ℕ → ℕ
m + n =
  ℕ-elim 
    {λ _ → ℕ}               -- type A
    n                       -- base case
    (λ _ res → suc res)     -- induction step
    m

-- identity type
-- G : Type
-- X carrier
-- _+_
-- e
-- ∀ x : X → e + x = x + e = x
-- ∀ e₁ : X if x + e₁ = e₁ + x = x → e₁ = e
-- intensionial equality
-- Identity type 
-- ≡ = \==
-- (x ≡ y) = ∅ if x ≠ y
--         = * if x = y
data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a

infix 0 _≡_

sym : {A : Set} → {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans p (refl) = p -- x ≡ y → y ≡ y (refl) → x ≡ y

ap : {A B : Set} → (f : A → B) → {x y : A} → x ≡ y → (f x) ≡ (f y)
ap {A} {B} f {x} {x} (refl {x}) = refl {B} {f x}


