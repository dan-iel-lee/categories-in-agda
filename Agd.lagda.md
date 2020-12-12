# Agd

Exploring Agda as a Category.

```
{-# OPTIONS --without-K #-}

module Category.Agd where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; sym; refl; cong)
open import Level
open import Category.Core

Agd : Category
Agd = record
        { Obj = Set
        ; _⟶_ = λ A B → (A → B)
        ; _∘_ = λ f g x → f (g x)
        ; id_ = λ _ x → x
        ; lunit = refl
        ; runit = refl
        ; assoc = refl
        }

```
