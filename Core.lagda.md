
# Category Theory Core
This module contains definitions for basic category theory concepts.

```

{-# OPTIONS --without-K #-}

module Category.Core where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; sym; refl; cong)
open import Level
open import Data.Product using (_×_; Σ-syntax; _,_)

private
  variable
    𝒸 𝓁 : Level
    A B C : Set 𝓁

record Category : Set (suc (𝒸 ⊔ 𝓁)) where
  infixr 30 _∘_
  field
    Obj : Set 𝓁
    _⟶_ : Obj → Obj → Set 𝒸

    _∘_ : ∀ {x y z : Obj} → (y ⟶ z) → (x ⟶ y) → (x ⟶ z)

    id_ : ∀ (x : Obj) → (x ⟶ x)
    lunit : ∀ {x y : Obj} {f : x ⟶ y} → f ∘ (id x) ≡ f
    runit : ∀ {x y : Obj} {f : x ⟶ y} → (id y) ∘ f ≡ f

    assoc : ∀ {x y z w : Obj} {f : z ⟶ w} {g : y ⟶ z} {h : x ⟶ y}
          → f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h
```

## Opposite
We can define an opposite category with the same objects but with its arrows flipped

```
flip : (A → B → C) → (B → A → C)
flip f b a = f a b

_ᵒ : Category {𝒸} {𝓁} → Category {𝒸} {𝓁}
record { Obj = Obj ; _⟶_ = _⟶_ ; _∘_ = _∘_ ; id_ = id_ ; lunit = lunit ; runit = runit ; assoc = assoc } ᵒ =
  record
    { Obj = Obj
    ; _⟶_ = _⟶'_
    ; _∘_ = flip _∘_
    ; id_ = id_
    ; lunit = runit
    ; runit = lunit
    ; assoc = sym assoc
    }
  where
    _⟶'_ = flip _⟶_

-- TODO: define equality

cyclic-sym : ∀ {A : Set 𝓁} {a b : A} {p : a ≡ b} → sym (sym p) ≡ p
cyclic-sym {p = refl} = refl

postulate
  cyclicᵒ : ∀ {C : Category {𝒸} {𝓁}} → (C ᵒ) ᵒ ≡ C
-- cyclicᵒ {C = record { Obj = Obj ; _⟶_ = _⟶_ ; _∘_ = _∘_ ; id_ = id_ ; lunit = lunit ; runit = runit ; assoc = assoc }} =
--   cong (λ ass → record { Obj = Obj ; _⟶_ = _⟶_ ; _∘_ = _∘_ ; id_ = id_ ; lunit = lunit ; runit = runit ; assoc = {!!} }) (cyclic-sym {p = assoc})

```


## Just playing with stuff
```

record Pair (A B : Set) : Set where
  field
    l : A
    r : B

pair-eq : ∀ {A B : Set} {a a' : A} {b b' : B} → a ≡ a' → b ≡ b' → (record { l = a ; r = b } ≡ record { l = a' ; r = b' } )
pair-eq refl refl = refl

```
