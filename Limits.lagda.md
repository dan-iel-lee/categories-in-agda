# Limits and Universal Properties


```
module Category.Limits where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; sym; refl; cong)
open import Level
open import Data.Product using (_×_; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

open import Category.Core

private
  variable
    𝒸 𝓁 : Level

-- unique existance
Σ! : (A : Set 𝒸) → (A → Set 𝓁) → Set (𝒸 ⊔ 𝓁)
Σ! A P = Σ[ a ∈ A ] (P a) × ∀ (b : A) → P b → a ≡ b

Σ!-syntax : (A : Set 𝒸) → (A → Set 𝓁) → Set (𝒸 ⊔ 𝓁)
Σ!-syntax = Σ!

infix 3 Σ!-syntax
syntax Σ!-syntax A (λ x → B) = Σ![ x ∈ A ] B

infix 2 ∃!_
∃!_ : (A : Set 𝒸) → Set 𝒸
∃! A = Σ![ x ∈ A ] ⊤

```
# Initiality and Finality

We start off with the definition underlying universality: that of an initial object.
(Plus its dual).
```


module Terminality (C : Category {𝒸} {𝓁}) where
  open Category C

  -- an object is initial iff it has a unique arrow
  -- to every other object
  IsInitial : (∅ : Obj) → Set (𝒸 ⊔ 𝓁)
  IsInitial ∅ = ∀ (x : Obj) → ∃! (∅ ⟶ x)

  -- the dual to initiality
  IsFinal : (𝟙 : Obj) → Set (𝒸 ⊔ 𝓁)
  IsFinal 𝟙 = ∀ (x : Obj) → ∃! (x ⟶ 𝟙)


module TermProps (C : Category {𝒸} {𝓁}) where
  open Category C
  open Terminality C
  -- some properties

  -- initiality and finality are dual
  init~fin : ∀ {x : Obj} → IsInitial x → Terminality.IsFinal (C ᵒ) x
  init~fin i = i

```
