
```

open import Category.Core renaming (Category to Cat)
open import Category.Functors
open import Level

module Category.Examples.Comma {𝒸 𝓁 : Level} {C D E : Cat {𝒸} {𝓁}} (F : Functor D C) (G : Functor E C) where


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong; sym; refl)
open Eq.≡-Reasoning
open import Data.Product using (_×_; Σ-syntax; _,_)

open Functor F renaming (F to F*; _⟶ᶜ_ to _⟶ᴰ_; _⟶ᴰ_ to _⟶ᶜ_; _₊ to ℱ; _∘ᶜ_ to _∘ᴰ_; _∘ᴰ_ to _∘ᶜ_; f-comp to F-comp; f-id to F-id)
open Functor G renaming (F to G*; _⟶ᶜ_ to _⟶ᴱ_; _⟶ᴰ_ to asdf; _₊ to 𝒢; _∘ᶜ_ to _∘ᴱ_; _∘ᴰ_ to asdf'; f-comp to G-comp; f-id to G-id)
open Cat C


CommaCat : Cat
CommaCat = record
             -- objects are (d, e, f) tuples where f : F d ⟶ G e
             { Obj = Σ[ d ∈ Cat.Obj D ] Σ[ e ∈ Cat.Obj E ] (F* d) ⟶ (G* e)
             -- morphisms are (h, k) tuples where h : d ⟶ d' and k : e ⟶ e'
             -- which must commute naturally
             ; _⟶_ = λ { (d , e , f) (d' , e' , f') → Σ[ h ∈ d ⟶ᴰ d' ] Σ[ k ∈ e ⟶ᴱ e' ] f' ∘ (ℱ h) ≡ (𝒢 k) ∘ f }
             ; _∘_ = λ { {(d , e , f)} {(d' , e' , f')} {(d'' , e'' , f'')} (h' , k' , eq') (h , k , eq) → (h' ∘ᴰ h) , (k' ∘ᴱ k) ,
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
             ; id = λ { (d , e , f) → Cat.id D d , Cat.id E e ,
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
             ; lunit = λ { {(d , e , f)} {(d' , e' , f')} {(h , k , eq)} →
                     begin
                       (h ∘ᴰ (Cat.id D d)) , ((k ∘ᴱ (Cat.id E e)) , {!!})
                     ≡⟨ {!!} ⟩
                       {!!}
                     ∎ }
             ; runit = {!!}
             ; assoc = {!!}
             }

```
