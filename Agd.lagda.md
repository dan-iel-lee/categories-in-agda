# Agd

Exploring Agda as a Category.

```
{-# OPTIONS --without-K #-}

module Category.Agd where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; sym; refl; cong)
open import Level
open import Category.Core
open import Data.Product using (_×_; Σ-syntax; _,_)

Agd : Category
Agd = record
        { Obj = Set
        ; _⟶_ = λ A B → (A → B)
        ; _∘_ = λ f g x → f (g x)
        ; id = λ _ x → x
        ; lunit = refl
        ; runit = refl
        ; assoc = refl
        }

§et : ∀ {𝓁 : Level} → Category {𝓁} {suc 𝓁}
§et {𝓁} = record
        { Obj = Set 𝓁
        ; _⟶_ = λ A B → (A → B)
        ; _∘_ = λ f g x → f (g x)
        ; id = λ _ x → x
        ; lunit = refl
        ; runit = refl
        ; assoc = refl
        }

```
