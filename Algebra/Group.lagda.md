# Groups

The goal of this module is to build up group theory from category theory.
The idea also is that this definition of Group, viewed through the
homotopy type theory lense, is actually the definition of the fundamental
group of a path connected space.

```
module Category.Algebra.Group where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Level
open import Data.Product using (_×_; Σ-syntax; _,_)

open import Category.Core
open import Category.Groupoid
open import Category.Morphisms
-- open Category

private
  variable
    𝒸 𝓁 : Level

record Group : Set (suc (𝒸 ⊔ 𝓁)) where
  field
    BG : Groupoid {𝒸} {𝓁}
  open Groupoid BG
  open Category GC
  open MorphTypes GC

  field
    -- the single object in the category
    O : Obj
  -- the morphisms (i.e. elements) of the group
  G = O ⟶ O

  field
    -- O is unique (up to homotopy)
    uniqueness : ∀ (x : Obj) → x ≡ O
```

Note that group properties follow from the definitions of a Category and a Groupoid.
- Identity follows from identity in a Category
- Associativity follows from the same in a Category
- Invertibility follw from invertibility in a Groupoid

```
_⊆_ : Group {𝒸} {𝓁} → Group {𝒸} {𝓁} → Set (𝒸 ⊔ 𝓁)
-- TODO

```
