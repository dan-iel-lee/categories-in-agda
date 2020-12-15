
```

{-# OPTIONS --without-K #-}

open import Category.Core renaming (Category to Cat)
open import Category.Functors
open import Level

module Category.Examples.Comma {𝒸 𝓁 : Level} {C D E : Cat {𝒸} {𝓁}} (F : Functor D C) (G : Functor E C) (s : LocallySmall C) where


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong; sym; refl)
open Eq.≡-Reasoning
open import Data.Product using (_×_; Σ-syntax; _,_)


open Functor F renaming (F to F*; _⟶ᶜ_ to _⟶ᴰ_; _⟶ᴰ_ to _⟶ᶜ_; _₊ to ℱ; _∘ᶜ_ to _∘ᴰ_; _∘ᴰ_ to _∘ᶜ_; f-comp to F-comp; f-id to F-id)
open Functor G renaming (F to G*; _⟶ᶜ_ to _⟶ᴱ_; _⟶ᴰ_ to asdf; _₊ to 𝒢; _∘ᶜ_ to _∘ᴱ_; _∘ᴰ_ to asdf'; f-comp to G-comp; f-id to G-id)
open Cat C

private
  variable
    e : Level

transp : ∀ {A : Set e} {P : A → Set e} {a b : A}
       → (p : a ≡ b)
       → P a → P b
transp refl x = x

-- packs component wise equality into equality of dependent pairs
pack : ∀ {A : Set e} {P : A → Set e} {x x' : A} {y : P x} {y' : P x'}
     (p : x ≡ x') → (transp p y ≡ y') → ((x , y) ≡ (x' , y'))
pack refl refl = refl

-- same as above, but for non-dependent pairs
pack' : ∀ {A B : Set e} {x x' : A} {y y' : B}
     (p : x ≡ x') → (y ≡ y') → ((x , y) ≡ (x' , y'))
pack' refl refl = refl

CommaCat : Cat
CommaCat = record
             -- objects are (d, e, f) tuples where f : F d ⟶ G e
             { Obj = Σ[ d ∈ Cat.Obj D ] Σ[ e ∈ Cat.Obj E ] (F* d) ⟶ (G* e)
             -- morphisms are (h, k) tuples where h : d ⟶ d' and k : e ⟶ e'
             -- which must commute naturally
             ; _⟶_ = λ { (d , e , f) (d' , e' , f') → Σ[ (h , k) ∈ d ⟶ᴰ d' × e ⟶ᴱ e' ] f' ∘ (ℱ h) ≡ (𝒢 k) ∘ f }
             -- arrows compose by piecwise composition
             ; _∘_ = λ { {(d , e , f)} {(d' , e' , f')} {(d'' , e'' , f'')} ((h' , k') , eq') ((h , k) , eq) → ((h' ∘ᴰ h) , (k' ∘ᴱ k)) ,
               (begin
                 (f'' ∘ ℱ (h' ∘ᴰ h))
               ≡⟨ cong (f'' ∘_) F-comp ⟩
                (f'' ∘ (ℱ h') ∘ (ℱ h))
               ≡⟨ assoc ⟩
                ((f'' ∘ (ℱ h')) ∘ (ℱ h))
               ≡⟨ cong (_∘ (ℱ h)) eq' ⟩
                (((𝒢 k') ∘ f') ∘ (ℱ h))
               ≡⟨ sym assoc ⟩
                ((𝒢 k') ∘ f' ∘ (ℱ h))
               ≡⟨ cong ((𝒢 k' ∘_)) eq ⟩
                ((𝒢 k') ∘ (𝒢 k) ∘ f)
               ≡⟨ assoc ⟩
                (((𝒢 k') ∘ (𝒢 k)) ∘ f)
               ≡⟨ cong (_∘ f) (sym G-comp) ⟩
                ((𝒢 (k' ∘ᴱ k)) ∘ f)
               ∎)}
             -- the identity arrow is composed of the components' identity arrows
             ; id = λ { (d , e , f) → (Cat.id D d , Cat.id E e) ,
                  (begin
                    (f ∘ (ℱ (Cat.id D d)))
                  ≡⟨ cong (f ∘_) F-id ⟩
                    (f ∘ id (F* d))
                  ≡⟨ lunit ⟩
                    f
                  ≡⟨ sym runit ⟩
                    (id (G* e) ∘ f)
                  ≡⟨ cong (_∘ f) (sym G-id) ⟩
                    ((𝒢 (Cat.id E e) ∘ f))
                  ∎) }
             -- properties follow from the same properties in the components
             -- with some proof irrelevance hackery :(
             ; lunit = λ { {(d , e , f)} {(d' , e' , f')} {((h , k) , eq)} →
                     pack
                       (begin
                         (h ∘ᴰ Cat.id D d , k ∘ᴱ Cat.id E e)
                       ≡⟨ pack' (Cat.lunit D) (Cat.lunit E) ⟩
                         (h , k)
                       ∎)
                       s }
             ; runit = λ { {(d , e , f)} {(d' , e' , f')} {((h , k) , eq)} →
                     pack
                       (begin
                         (Cat.id D d' ∘ᴰ h , Cat.id E e' ∘ᴱ k)
                       ≡⟨ pack' (Cat.runit D) (Cat.runit E) ⟩
                         (h , k)
                       ∎)
                       s }
             ; assoc = λ { {d1 , e1 , f1} {d2 , e2 , f2} {d3 , e3 , f3} {d4 , e4 , f4}
                           {(h1 , k1) , _} {(h2 , k2) , _} {(h3 , k3) , _}
                          → pack
                            (begin
                              h1 ∘ᴰ (h2 ∘ᴰ h3) , (k1 ∘ᴱ (k2 ∘ᴱ k3))
                            ≡⟨ pack' (Cat.assoc D) (Cat.assoc E) ⟩
                              (h1 ∘ᴰ h2) ∘ᴰ h3 , ((k1 ∘ᴱ k2) ∘ᴱ k3)
                            ∎) s}
                           }

```
