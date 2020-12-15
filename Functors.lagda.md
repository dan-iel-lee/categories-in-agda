# Functors

```

{-# OPTIONS --without-K #-}

module Category.Functors where

open import Category.Core
open import Category.Morphisms
open MorphTypes renaming (_⁻ to Inv)
open import Category.Agd

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong; sym; trans)
open Eq.≡-Reasoning
open import Level
open import Data.Product using (_×_; Σ-syntax; _,_)


private
  variable
    𝒸 𝓁 : Level

record Functor (C D : Category {𝒸} {𝓁}): Set (suc (𝒸 ⊔ 𝓁)) where
  open Category renaming (_⟶_ to Morph; _∘_ to Comp)
  infix 40 _₊
  -- some helpful aliases
  _⟶ᶜ_ : Obj C → Obj C → Set 𝒸
  _⟶ᶜ_ = Morph C

  _⟶ᴰ_ : Obj D → Obj D → Set 𝒸
  _⟶ᴰ_ = Morph D

  _∘ᶜ_ : ∀ {x y z : Obj C} → (y ⟶ᶜ z) → (x ⟶ᶜ y) → (x ⟶ᶜ z)
  _∘ᶜ_ = Comp C

  _∘ᴰ_ : ∀ {x y z : Obj D} → (y ⟶ᴰ z) → (x ⟶ᴰ y) → (x ⟶ᴰ z)
  _∘ᴰ_ = Comp D

  field

    -- action on objects
    F : Obj C → Obj D
    -- action on morphisms
    _₊ : ∀ {x y : Obj C} → (x ⟶ᶜ y) → ((F x) ⟶ᴰ (F y))

    -- properties
    -- ids are mapped to ids
    f-id : ∀ {x : Obj C} → (id C x)₊ ≡ id D (F x)
    -- composition is preserved
    f-comp : ∀ {x y z : Obj C} {f : x ⟶ᶜ y} → {g : y ⟶ᶜ z} → (g ∘ᶜ f)₊ ≡ g ₊ ∘ᴰ f ₊
```
## Properties

```
module FuncProps (C D : Category {𝒸} {𝓁}) (F : Functor C D) where
  open Category renaming (_⟶_ to Morph; _∘_ to Comp)
  open Functor F renaming (F to F*)

  -- functors preserve isomorphisms
  f-iso : ∀ {x y : Obj C} {f : x ⟶ᶜ y} → IsIso C f → IsIso D (f ₊)
  f-iso {x} {y} {f = f} (g , ru , lu) = (g ₊) , ru' , lu'
    where
      -- right unit
      ru' : (g ₊) ∘ᴰ (f ₊) ≡ id D (F* x)
      ru' =
        begin
          (g ₊) ∘ᴰ (f ₊)
        ≡⟨ sym f-comp ⟩
          (g ∘ᶜ f) ₊
        ≡⟨ cong _₊ ru ⟩
          (id C x) ₊
        ≡⟨ f-id ⟩
          id D (F* x)
        ∎

      -- left unit
      lu' : (f ₊) ∘ᴰ (g ₊) ≡ id D (F* y)
      lu' =
        begin
        (f ₊) ∘ᴰ (g ₊)
        ≡⟨ sym f-comp ⟩
        (f ∘ᶜ g) ₊
        ≡⟨ cong _₊ lu ⟩
        (id C y) ₊
        ≡⟨ f-id ⟩
        id D (F* y)
        ∎

```

# Hom functors

```
postulate
  funExt : ∀ {A B : Set 𝓁} {f g : A → B}→ (∀ (x : A) → f x ≡ g x) → f ≡ g
module RepFunc (C : Category {𝓁} {suc 𝓁}) where
  open Category C

  -- functor which takes x ↦ C(c, x)
  C⟨_,-⟩ : Obj → Functor C §et
  C⟨ c ,-⟩ = record { F = λ d → c ⟶ d ; _₊ = λ f a → f ∘ a ; f-id = funExt (λ x → runit) ; f-comp = funExt (λ x → sym assoc) }

  -- dual notion
  C⟨-,_⟩ : Category.Obj (C ᵒ) → Functor C §et
  C⟨-, c ⟩ = record { F = λ d → c ⟶ d ; _₊ = λ f a → f ∘ a ; f-id = funExt (λ x → runit) ; f-comp = funExt (λ x → sym assoc) }
```
