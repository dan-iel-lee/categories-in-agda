
```
module Category.Groupoid where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Level

open import Category.Core
open import Category.Morphisms

private
  variable
    𝒸 𝓁 : Level

record Groupoid : Set (suc (𝒸 ⊔ 𝓁)) where
  field
    GC : Category {𝒸} {𝓁}
  open Category GC
  open MorphTypes GC

  field
    -- every element has an inverse
    inv : ∀ {x y : Obj} → (x ⟶ y) → (y ⟶ x)
    isInv : ∀ {x y : Obj} → (f : x ⟶ y) → AreInv f (inv f)

```
