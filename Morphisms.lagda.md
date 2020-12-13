# Morphisms and there properties

## Mono, Epi, Iso

A morphism is monic if it 

```

open import Level
open import Category.Core
module Category.Morphisms where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong; sym; trans)
open Eq.≡-Reasoning
open import Data.Product using (_×_; Σ-syntax; _,_)

private
  variable
    𝒸 𝓁 : Level

module MorphTypes (C : Category {𝒸} {𝓁}) where
  open Category C
  private
    variable
      x y z w : Obj

  IsMonic : (x ⟶ y) → Set (𝒸 ⊔ 𝓁)
  IsMonic {x} {y} f = ∀ {z : Obj} {a a' : z ⟶ x}
    → (f ∘ a ≡ f ∘ a') → (a ≡ a')

  IsEpic : (x ⟶ y) → Set (𝒸 ⊔ 𝓁)
  IsEpic {x} {y} g = ∀ {z : Obj} {b b' : y ⟶ z}
    → (b ∘ g ≡ b' ∘ g) → (b ≡ b')

  -- A morphism is split monic if it has a *retraction*
  IsSplitMon : (x ⟶ y) → Set 𝒸
  IsSplitMon {x} {y} f = Σ[ r ∈ y ⟶ x ] r ∘ f ≡ id x

  -- A morphism is split epic if it has a *section*
  IsSplitEpi : (x ⟶ y) → Set 𝒸
  IsSplitEpi {x} {y} g = Σ[ s ∈ y ⟶ x ] g ∘ s ≡ id y

  AreInv : (f : x ⟶ y) → (g : y ⟶ x) → Set 𝒸
  AreInv {x} {y} f g = (g ∘ f ≡ id x) × (f ∘ g ≡ id y)

  IsIso : (f : x ⟶ y) → Set 𝒸
  IsIso {x} {y} f = Σ[ g ∈ y ⟶ x ] AreInv f g

  _⁻ : (f : x ⟶ y) → {IsIso f} → (y ⟶ x)
  (f ⁻) {g , _} = g

```

## Basic properties of mono and epimorphisms

```
module MorphProps (C : Category {𝒸} {𝓁}) where

  open Category C
  open MorphTypes C
  -- import MorphTypes as MT

  private
    variable
      x y : Obj

  -- split monic implies monic
  splitMon=>Mon : ∀ (f : x ⟶ y) → IsSplitMon f → IsMonic f
  splitMon=>Mon {x} {y} f (r , 𝓅) {z = z} {a} {a'} = λ eq →
    begin
      a
    ≡⟨ sym runit ⟩
      ((id x) ∘ a)
    ≡⟨ cong (_∘ a) (sym 𝓅) ⟩
      ((r ∘ f) ∘ a)
    ≡⟨ sym assoc ⟩
      (r ∘ (f ∘ a))
    ≡⟨ cong (r ∘_) eq ⟩
      (r ∘ (f ∘ a'))
    ≡⟨ assoc ⟩
      ((r ∘ f) ∘ a')
    ≡⟨ cong (_∘ a') 𝓅 ⟩
      ((id x) ∘ a')
    ≡⟨ runit ⟩
      a'
    ∎

  postulate
    splitEpi=>Epi : ∀ (f : x ⟶ y) → IsSplitEpi f → IsEpic f
```
## Isomorphisms

```

  -- section/retraction uniqueness
  sect-retr : ∀ {f : x ⟶ y} {r s : y ⟶ x}
            → r ∘ f ≡ id x
            → f ∘ s ≡ id y
            → r ≡ s
  sect-retr {x} {y} {f} {r} {s} eq1 eq2 = sym (mon (trans left right))
    where
      mon : (f ∘ s ≡ f ∘ r) → s ≡ r
      mon = splitMon=>Mon f (r , eq1)

      left : f ∘ s ≡ f ∘ r ∘ f ∘ s
      left =
        begin
          (f ∘ s)
        ≡⟨ cong (f ∘_) (sym runit) ⟩
          (f ∘ (id x) ∘ s)
        ≡⟨ cong (λ g → (f ∘ g ∘ s)) (sym eq1) ⟩
          (f ∘ (r ∘ f) ∘ s)
        ≡⟨ cong (f ∘_) (sym assoc) ⟩
          (f ∘ r ∘ f ∘ s)
        ∎

      right : f ∘ r ∘ f ∘ s ≡ f ∘ r
      right =
        begin
          f ∘ r ∘ f ∘ s
        ≡⟨ cong (λ g → f ∘ r ∘ g) eq2 ⟩
          (f ∘ r ∘ (id y))
        ≡⟨ assoc ⟩
          (f ∘ r) ∘ (id y)
        ≡⟨ lunit ⟩
          f ∘ r
        ∎

  -- the identity is its own inverse
  id-iso : IsIso (id x)
  id-iso {x = x} = (id x) , (lunit , lunit)

  -- inverse is iso
  inv-iso : ∀ (f : x ⟶ y) → (i : IsIso f) → IsIso ((f ⁻) {i})
  inv-iso f (_ , ru , lu) = f , (lu , ru)

-- TODO: Monic and Split Epic => Isomorphic


```
## Duality
Mono and epi are dual to each other (as are their split counterparts). This
is in the sense that a morphism being monic in C means it is epic in
the opposite category.
Happily, and perhaps not all too surprisingly, this fact follows definitionaly.

```
  Cᵒ : Category {𝒸} {𝓁}
  Cᵒ = C ᵒ

  -- WOAH it follows through definitionaly
  mon=>epiᵒ : ∀ {f : x ⟶ y} → IsMonic f → MorphTypes.IsEpic Cᵒ f
  mon=>epiᵒ mo = mo -- λ b b' eq → mo b b' eq

  epi=>monᵒ : ∀ {f : x ⟶ y} → IsEpic f → MorphTypes.IsMonic Cᵒ f
  epi=>monᵒ ep = ep

  smon=>sepiᵒ : ∀ {f : x ⟶ y} → IsSplitMon f → MorphTypes.IsSplitEpi Cᵒ f
  smon=>sepiᵒ mo = mo -- λ b b' eq → mo b b' eq

  sepi=>monᵒ : ∀ {f : x ⟶ y} → IsSplitEpi f → MorphTypes.IsSplitMon Cᵒ f
  sepi=>monᵒ mo = mo -- λ b b' eq → mo b b' eq

```


