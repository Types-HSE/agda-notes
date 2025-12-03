-- Cornelis commands used:
-- :CornelisLoad - load and type-check buffer
-- :CornelisGive - fill goal with normalized hole content
-- :CornelisMakeCase - case split
-- :CornelisTypeContextInfer - show goal type, context and inferred type of hole contents
-- :CornelisNormalize - compute normal form
-- :CornelisRefine - Refine goal
-- :CornelisQuestionToMeta - Expand ?-holes to {!!}
--
-- Agda docs: https://agda.readthedocs.io/en/latest/overview.html
-- Cornelis reference: https://github.com/agda/cornelis/tree/master?tab=readme-ov-file

module agda-sem1 where

-- Bool (Set = Type)
-- Bool : Type
-- true : Bool
-- false : Bool
data Bool : Set where
  true false : Bool

-- not, and, or
-- → (\to)
-- case-analysis :CornelisMakeCase
not : Bool → Bool
not true = false
not false = true

_&&_ : Bool → Bool → Bool
true && b = b
false && b = false

_&&'_ : Bool → Bool → Bool
true &&' true = true
true &&' false = false
false &&' true = false
false &&' false = false

_||_ : Bool → Bool → Bool
true || b = true
false || b = b


idBool : Bool → Bool
idBool x = x

-- λ = \Gl, \lambda, \lamda
idBool' : Bool → Bool
idBool' = λ (x : Bool) → x
-- :CornelisSolve C-c C-s

-- polymorphic id
id'' : (X : Set) → X → X
id'' X x = x

t = id'' Bool true

-- implicit polymorphic id 
id' : {X : Set} → X → X
id' {X} x = x

-- Implict 
id : {X : Set} → X → X
id x = x


-- Naturals, ℕ = \bN, \nat
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

two : ℕ
two = suc (suc zero)

{-# BUILTIN NATURAL ℕ #-}
-- 0 = zero, 1 = suc (zero),

two' : ℕ
two' = 2

_+_ : ℕ → ℕ → ℕ
zero + m = m
suc n + m = suc (n + m)

max : ℕ → ℕ → ℕ
max zero zero = zero
max zero (suc m) = suc m
max (suc n) zero = suc n
max (suc n) (suc m) = suc (max n m)

-- List Int, List Bool
data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A

infixr 10 _::_


l1 : List ℕ
l1 = 1 :: 2 :: 3 :: []

-- kinds: * -> *
-- List is a functor
functor : Set → Set
functor = List

length : {X : Set} → List X → ℕ
length [] = zero
length (x :: xs) = suc (length xs)

-- map ((+ 1), [1, 2, 3]) = [2, 3, 4]
map : {X Y : Set} → (X → Y) → List X → List Y
map f [] = []
map f (x :: xs) = f x :: map f xs

-- map id xs = xs
-- map (f ∘ g) xs = map f (map g xs)

-- mixfix
if_then_else_ : {X : Set} → Bool → X → X → X
if true then x else y = x
if false then x else y = y

e2 = if true then 3 else 5

-- filter
filter : {X : Set} → (X → Bool) → List X → List X
filter p [] = []
-- filter p (x :: xs) = (if p x then x else {! !}) :: filter p xs -- Bad strategy
filter p (x :: xs) = if p x then x :: filtered else filtered where
  filtered = filter p xs


-- Propositions as types
-- Curry-Howard correspondence
-- P, Q - Types = Propositions
-- p : P - Term = Evidence that proposition P holds
-- P → Q = P ⇒ Q
--
-- If P holds then Q ⇒ P also holds
hyp : {P Q : Set} → P → (Q → P)
hyp {P} {Q} p = f where
  f : Q → P
  f _ = p

open import Data.Product using (_×_; _,_)

-- If P and Q holds then also Q and P
sym' : {P Q : Set} → P × Q → Q × P
sym' (fst , snd) = snd , fst


-- Dependent types

D : Bool → Set
D true = Bool
D false = ℕ


-- D false is a type
e3 : D false
e3 = 3

-- But also D is a type itself
if[_]_then_else_ : (D : Bool → Set)
                 → (b : Bool)
                 → D true
                 → D false
                 → D b
if[ X ] true then x else y = x
if[ X ] false then x else y = y

-- Not possible before
dep : (b : Bool) → D b
dep b = if[ D ] b then true else 3




