# Limits and Universal Properties


```
module Category.Limits where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; sym; refl; cong; trans)
open import Level
open import Data.Product using (_×_; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

open import Category.Core
open import Category.Morphisms

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
∃! A = Σ[ a ∈ A ] (∀ (b : A) → a ≡ b)

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
  open MorphTypes C


  private
    variable
      x y z : Obj
  -- some properties

  -- initiality and finality are dual
  init~fin : IsInitial x → Terminality.IsFinal (C ᵒ) x
  init~fin i = i

  -- initial objects are isomorphic
  init-iso : IsInitial x → IsInitial y → AreIso x y
  init-iso {x} {y} i1 i2 with i1 y | i2 x
  ... | f , u1 | g , u2 = f , g , left , right
    where
      left : g ∘ f ≡ id x
      left with i1 x
      ... | gf , ugf = trans gfgf gfid
        where
          gfgf : g ∘ f ≡ gf
          gfgf = sym (ugf (g ∘ f))

          gfid : gf ≡ id x
          gfid = ugf (id x)

      right : f ∘ g ≡ id y
      right with i2 y
      ... | fg , ufg = trans fgfg fgid
        where
          fgfg : f ∘ g ≡ fg
          fgfg = sym (ufg (f ∘ g))

          fgid : fg ≡ id y
          fgid = ufg (id y)

```
