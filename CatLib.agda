{-# OPTIONS --allow-unsolved-metas #-}

-- Taken from https://github.com/agda/agda-categories
module CatLib where 
    open import Cubical.Core.Everything using (_≡_)
    open import Data.Nat using (ℕ;suc)
    open import Agda.Primitive using (Level; lsuc ; _⊔_)


    record is-contr {ℓ} (A : Set ℓ) : Set ℓ where
        constructor contr 
        field 
            centre : A 
            paths : (x : A) → centre ≡ x
    open is-contr public

    is-prop : ∀{ℓ} → Set ℓ → Set _ 
    is-prop A = (x y : A) → x ≡ y  

    is-hlevel : ∀{ℓ} → Set ℓ → ℕ → Set _ 
    is-hlevel A 0 = is-contr A
    is-hlevel A 1 = is-prop A
    is-hlevel A (suc n) = (x y : A) → is-hlevel (x ≡ y) n

    is-set : ∀{ℓ} → Set ℓ → Set ℓ 
    is-set A = is-hlevel A 2

    record Category (o h : Level) : Set (lsuc (o ⊔ h)) where 
        field 
            Ob : Set o
            _⇒_ : Ob → Ob → Set h
            id : ∀ {x} → x ⇒ x
            _∘_ : ∀{x y z} → y ⇒ z → x ⇒ y → x ⇒ z

            idr : ∀{x y}{f : x ⇒ y} → (f ∘ id) ≡ f 
            idl : ∀{x y}{f : x ⇒ y} → id ∘ f ≡ f
            assoc : ∀{w x y z} {f : y ⇒ z}{g : x ⇒ y}{h : w ⇒ x} → f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h


        infixr 40 _∘_

    module ObjectProduct{o ℓ : Level} (𝒞 : Category o ℓ) where
        open Category 𝒞

        private 
            variable
                A B C D : Ob 
                h i j : A ⇒ B

        record Product (A B : Ob) : Set (o ⊔ ℓ) where
            infix 10 ⟨_,_⟩

            field
                A×B   : Ob
                π₁    : A×B ⇒ A
                π₂    : A×B ⇒ B
                ⟨_,_⟩ : C ⇒ A → C ⇒ B → C ⇒ A×B

                project₁ : π₁ ∘ ⟨ h , i ⟩ ≡ h
                project₂ : π₂ ∘ ⟨ h , i ⟩ ≡ i
                unique   : π₁ ∘ h ≡ i → π₂ ∘ h ≡ j → ⟨ i , j ⟩ ≡ h 

        
        module Morphisms where 

            open Product
            infix 10 [_]⟨_,_⟩ [_⇒_]_×_
            infix 12 [[_]] [_]π₁ [_]π₂

            [[_]] : Product A B → Ob 
            [[ p ]] = p .A×B

            [_]⟨_,_⟩ : ∀(p : Product B C) → A ⇒ B → A ⇒ C → A ⇒ [[ p ]]
            [ p ]⟨ f , g ⟩ = ⟨_,_⟩ p f g

            [_]π₁ : ∀(p : Product A B) → [[ p ]] ⇒ A 
            [ p ]π₁ = π₁ p

            [_]π₂ : ∀(p : Product A B) → [[ p ]] ⇒ B
            [ p ]π₂ = π₂ p

            [_⇒_]_×_ : ∀(p₁ : Product A C)(p₂ : Product B D) → (A ⇒ B) → (C ⇒ D) → ([[ p₁ ]] ⇒ [[ p₂ ]])
            [ p₁ ⇒ p₂ ] f × g = [ p₂ ]⟨ f ∘ [ p₁ ]π₁ , g ∘ [ p₁ ]π₂ ⟩ 



            
                

    module BinaryProducts {o h} (𝒞 : Category o h) where
        open ObjectProduct 𝒞
        open Category 𝒞
        open import Level using (levelOfTerm)
        private 
            variable
                A B C D : Ob 

        record BinaryProductsT : Set (levelOfTerm 𝒞) where
            infixr 7 _×_

            field
                product : ∀ {A B : Ob} → Product A B

            _×_ : Ob → Ob → Ob
            A × B = Product.A×B (product {A} {B})


            
            --_⁂_ : A ⇒ B → C ⇒ D → A × C ⇒ B × D
            --f ⁂ g = [ product ⇒ product ] f × g

    module Terminal {o h} (𝒞 : Category o h) where
        open Category 𝒞
        
        record IsTerminal(⊤ : Ob) : Set (o ⊔ h) where
            field
                ! : {A : Ob} → (A ⇒ ⊤)
                !-unique : ∀{A : Ob} → (f : A ⇒ ⊤) → ! ≡ f

        record TerminalT : Set (o ⊔ h) where 
            field 
                ⊤ : Ob 
                ⊤-is-terminal : IsTerminal ⊤

    module Cartesian {o h} (𝒞 : Category o h) where 
        open import Level using (levelOfTerm)
        open Terminal 𝒞 using (TerminalT)
        open BinaryProducts 𝒞 using (BinaryProductsT)

        record CartesianT : Set (levelOfTerm 𝒞) where 
            field 
                terminal : TerminalT
                products : BinaryProductsT
                

    module Equalizer {o ℓ} (𝒞 : Category o ℓ) where 
        open Category 𝒞

        private 
            variable
                A B X : Ob 
                h i l : A ⇒ B

        record IsEqualizer {E : Ob} (arr : E ⇒ A) (f g : A ⇒ B) : Set (o ⊔ ℓ) where  
            field 
                equality : f ∘ arr ≡ g ∘ arr 
                equalize : ∀{h : X ⇒ A} → f ∘ h ≡ g ∘ h → X ⇒ E
                universal : ∀{eq : f ∘ h ≡ g ∘ h} → h ≡ arr ∘ equalize eq
                unique : ∀{eq : f ∘ h ≡ g ∘ h} → h ≡ arr ∘ i → i ≡ equalize eq

        record EqualizerT (f g : A ⇒ B) : Set (o ⊔ ℓ) where 
            field 
                {obj} : Ob 
                arr : obj ⇒ A 
                isEqualizer : IsEqualizer arr f g

    module Pullback {o ℓ}(𝒞 : Category o ℓ) where
        open Category 𝒞 
        private
            variable
                A B X Y Z  : Ob
                h₁ h₂ i f g : A ⇒ B 

        record IsPullback {P : Ob} (p₁ : P ⇒ X) (p₂ : P ⇒ Y)(f : X ⇒ Z)(g : Y ⇒ Z) : Set (o ⊔ ℓ) where 
            field
                commute : f ∘ p₁ ≡ g ∘ p₂
                universal : ∀{h₁ : A ⇒ X}{h₂ : A ⇒ Y} → f ∘ h₁ ≡ g ∘ h₂ → A ⇒ P 
                unique : ∀{eq : f ∘ h₁ ≡ g ∘ h₂} → 
                            p₁ ∘ i ≡ h₁ → p₂ ∘ i ≡ h₂ → 
                            i ≡ universal eq
                p₁∘universal≈h₁  : ∀ {eq : f ∘ h₁ ≡ g ∘ h₂} →
                         p₁ ∘ universal eq ≡ h₁
                p₂∘universal≈h₂  : ∀ {eq : f ∘ h₁ ≡ g ∘ h₂} →
                         p₂ ∘ universal eq ≡ h₂

        record PullbackT (f : X ⇒ Z) (g : Y ⇒ Z) : Set (o ⊔ ℓ) where 
            field 
                {P} : Ob 
                p₁ : P ⇒ X 
                p₂ : P ⇒ Y 
                isPullback : IsPullback p₁ p₂ f g 



        open ObjectProduct 𝒞 
        open Equalizer 𝒞 
        -- do this proof later
        Product×Equalizer⇒Pullback : (p : Product A B) → EqualizerT (f ∘ Product.π₁ p) (g ∘ Product.π₂ p) → PullbackT f g
        Product×Equalizer⇒Pullback = {!   !}

    module Finitely {o ℓ} (𝒞 : Category o ℓ) where 
        open import Level using (levelOfTerm)

        open Category 𝒞 
        open BinaryProducts 𝒞 using (BinaryProductsT)
        open Cartesian 𝒞 using (CartesianT)
        open Equalizer 𝒞 using (EqualizerT)
        open Pullback 𝒞 using (PullbackT; Product×Equalizer⇒Pullback)

        record FinitelyComplete : Set (levelOfTerm 𝒞) where 
            field 
                cartesian : CartesianT
                equalizer : ∀ {A B : Ob} → (f g : A ⇒ B) → EqualizerT f g

            pullback : ∀{X Y Z : Ob} → (f : X ⇒ Z) → (g : Y ⇒ Z) → PullbackT f g  
            pullback f g = Product×Equalizer⇒Pullback (BinaryProductsT.product (CartesianT.products cartesian)) (equalizer _ _)

    module Functor {o ℓ}(𝒞 𝒟 : Category o ℓ) where
        open import Level using (levelOfTerm)

        open Category 𝒞 renaming (Ob to Obᶜ; _⇒_ to _⇒ᶜ_; id to idᶜ; _∘_ to _∘ᶜ_)
        open Category 𝒟 renaming (Ob to Obᵈ; _⇒_ to _⇒ᵈ_; id to idᵈ; _∘_ to _∘ᵈ_)

        record FunctorT : Set (levelOfTerm 𝒞) where 
            field
                F₀ : Obᶜ → Obᵈ
                F₁ : {A B : Obᶜ} → (f : A ⇒ᶜ B) → F₀ A ⇒ᵈ F₀ B

                Fid : {A : Obᶜ} → F₁ (idᶜ {A}) ≡ idᵈ { F₀ A }
                Fcomp : {A B C : Obᶜ}{f : A ⇒ᶜ B}{g : B ⇒ᶜ C} → F₁ (g ∘ᶜ f) ≡ (F₁ g ∘ᵈ F₁ f)


    -- covariant in both args

    module BiFunctor {o ℓ}(𝒞 𝒟 ℬ : Category o ℓ) where
        open import Level using (levelOfTerm)

        open Category ℬ renaming (Ob to Obᵇ; _⇒_ to _⇒ᵇ_; id to idᵇ; _∘_ to _∘ᵇ_)
        open Category 𝒞 renaming (Ob to Obᶜ; _⇒_ to _⇒ᶜ_; id to idᶜ; _∘_ to _∘ᶜ_)
        open Category 𝒟 renaming (Ob to Obᵈ; _⇒_ to _⇒ᵈ_; id to idᵈ; _∘_ to _∘ᵈ_)

        record BiFunctorT : Set (levelOfTerm 𝒞) where 
            field
                F₀ : Obᵇ → Obᶜ → Obᵈ
                F₁ : {A B : Obᵇ}{C D : Obᶜ} → (f : A ⇒ᵇ B)(g : C ⇒ᶜ D) → F₀ A C ⇒ᵈ F₀ B D

                Fid : {A : Obᵇ}{C : Obᶜ} → F₁ (idᵇ {A}) (idᶜ {C}) ≡ idᵈ { F₀ A C }
                Fcomp : {A B C : Obᵇ}{f  : A ⇒ᵇ B}{g  : B ⇒ᵇ C}
                        {X Y Z : Obᶜ}{f' : X ⇒ᶜ Y}{g' : Y ⇒ᶜ Z}
                    → F₁ (g ∘ᵇ f) (g' ∘ᶜ f') ≡ (F₁ g  g' ∘ᵈ F₁ f f')

    module Iso{o ℓ} (𝒞 : Category o ℓ) where 
        open Category 𝒞

        infix 4 _≅_
        record _≅_ (A B : Ob) : Set (ℓ ⊔ o) where
            field
                from : A ⇒ B
                to   : B ⇒ A
                isoˡ : to ∘ from ≡ id
                isoʳ : from ∘ to ≡ id


    module Commutation {o ℓ}(𝓒 : Category o ℓ) where
        open Category 𝓒

        infix 1 [_⇒_]⟨_≡_⟩
        [_⇒_]⟨_≡_⟩ : ∀ (A B : Ob) → A ⇒ B → A ⇒ B → Set _
        [ A ⇒ B ]⟨ f ≡ g ⟩ = f ≡ g

        infixl 2 connect
        connect : ∀ {A C : Ob} (B : Ob) → A ⇒ B → B ⇒ C → A ⇒ C
        connect B f g = g ∘ f

        syntax connect B f g = f ⇒⟨ B ⟩ g
        
    module Monoidal {o ℓ}(𝒞 : Category o ℓ) where
        open import Level using (levelOfTerm)
        open BiFunctor using (BiFunctorT)
        open Iso 𝒞 
        open _≅_

        open Category 𝒞
        open Commutation 𝒞
        
        record MonoidalT : Set (levelOfTerm 𝒞) where 
            field 
                ⊗ : BiFunctorT 𝒞 𝒞 𝒞
                unit : Ob
                

            open BiFunctorT ⊗ 
            infixr 10 _⊗₀_ _⊗₁_ 

            _⊗₀_ : Ob → Ob → Ob
            _⊗₀_ = F₀

            _⊗₁_ : {X Y Z W : Ob} → X ⇒ Y → Z ⇒ W → (X ⊗₀ Z) ⇒ (Y ⊗₀ W)
            _⊗₁_ = F₁          

            field 
                unitorˡ : {X : Ob} → unit ⊗₀ X ≅ X
                unitorʳ : {X : Ob} → X ⊗₀ unit ≅ X
                associator : {X Y Z : Ob} → (X ⊗₀ Y) ⊗₀ Z ≅ X ⊗₀ (Y ⊗₀ Z)

            private 
                λ⇒ : {X : Ob} → (unit ⊗₀ X) ⇒ X
                λ⇒ {X} = (unitorˡ {X}) .from  

                λ⇐ : {X : Ob} →  X ⇒ (unit ⊗₀ X)
                λ⇐ {X} = (unitorˡ {X}) .to

                ρ⇒ : {X : Ob} → (X ⊗₀ unit) ⇒ X
                ρ⇒ {X} = (unitorʳ {X}) .from  
                 
                ρ⇐ : {X : Ob} →  X ⇒ (X ⊗₀ unit)
                ρ⇐ {X} = (unitorʳ {X}) .to

                α⇒ : {X Y Z : Ob} → ((X ⊗₀ Y) ⊗₀ Z) ⇒ (X ⊗₀ (Y ⊗₀ Z))
                α⇒ {X}{Y}{Z} = associator {X} {Y} {Z} .from

                α⇐ : {X Y Z : Ob} → (X ⊗₀ (Y ⊗₀ Z)) ⇒ (((X ⊗₀ Y) ⊗₀ Z))
                α⇐ {X}{Y}{Z} = associator {X} {Y} {Z} .to
            field
                pentagon : { X Y Z W : Ob } → [ (((X ⊗₀ Y) ⊗₀ Z) ⊗₀ W) ⇒ (X ⊗₀ Y ⊗₀ Z ⊗₀ W) ]⟨
                                                    α⇒ ⊗₁ id ⇒⟨ ((X ⊗₀ Y ⊗₀ Z) ⊗₀ W) ⟩ 
                                                    α⇒       ⇒⟨ (X ⊗₀ (Y ⊗₀ Z) ⊗₀ W) ⟩ 
                                                    id ⊗₁ α⇒ 
                                                ≡ 
                                                    α⇒ ⇒⟨ ((X ⊗₀ Y) ⊗₀ Z ⊗₀ W) ⟩ 
                                                    α⇒ ⟩
    module NaturalTransformation where 
        open Functor
        record NaturalTransformation {o ℓ : Level}{C : Category o ℓ}
                             {D : Category o ℓ}
                             (F G : FunctorT C D) : Set (o ⊔ ℓ ) where
            eta-equality
            private
                module F = FunctorT F
                module G = FunctorT G
            open F using (F₀; F₁)
            open Category D 

            field
                η           : {!   !} --∀ X → D [ F₀ X , G.F₀ X ]
                commute     : {!   !} --∀ {X Y} (f : C [ X , Y ]) → η Y ∘ F₁ f ≈ G.F₁ f ∘ η X
    module Adjoint where 
        open import Level using (levelOfTerm)
        open import Categories.NaturalTransformation 
        _ : NaturalTransformation {!   !} {!   !} 
        _ = {!   !}
{-        open Functor
        record AdjointT {C D : Category}(L : FunctorT C D) (R : FunctorT D C) : Set (levelOfTerm L ⊔ levelOfTerm R) where
            private
                module C = Category C
                module D = Category D
                module L = Functor L
                module R = Functor R

            field
                unit   : NaturalTransformation idF (R ∘F L)
                counit : NaturalTransformation (L ∘F R) idF

            module unit = NaturalTransformation unit
            module counit = NaturalTransformation counit

            field
                zig : ∀ {A : C.Obj} → counit.η (L.F₀ A) D.∘ L.F₁ (unit.η A) D.≈ D.id
                zag : ∀ {B : D.Obj} → R.F₁ (counit.η B) C.∘ unit.η (R.F₀ B) C.≈ C.id
                    -}