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

    record PreCat (o h : Level) : Set (lsuc (o ⊔ h)) where 
        field 
            Ob : Set o
            _⇒_ : Ob → Ob → Set h
           -- Hom-set : (x y : Ob) → is-set (x ⇒ y) -- if p : x ≡ y, q : x ≡ y, then p ≡ q
            id : ∀ {x} → x ⇒ x
            -- how to ensure this behaves correctly?
            --_≣_ : ∀{A B}→ (f g : A ⇒ B) → Set h
            _∘_ : ∀{x y z} → y ⇒ z → x ⇒ y → x ⇒ z

            idr : ∀{x y}{f : x ⇒ y} → (f ∘ id) ≡ f 
            idl : ∀{x y}{f : x ⇒ y} → id ∘ f ≡ f
            assoc : ∀{w x y z} {f : y ⇒ z}{g : x ⇒ y}{h : w ⇒ x} → f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h
        infixr 40 _∘_

    module ObjectProduct{o ℓ : Level} (𝒞 : PreCat o ℓ) where
        open PreCat 𝒞

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



            
                

    module BinaryProducts {o h} (𝒞 : PreCat o h) where
        open ObjectProduct 𝒞
        open PreCat 𝒞
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

    module Terminal {o h} (𝒞 : PreCat o h) where
        open PreCat 𝒞
        
        record IsTerminal(⊤ : Ob) : Set (o ⊔ h) where
            field
                ! : {A : Ob} → (A ⇒ ⊤)
                !-unique : ∀{A : Ob} → (f : A ⇒ ⊤) → ! ≡ f

        record TerminalT : Set (o ⊔ h) where 
            field 
                ⊤ : Ob 
                ⊤-is-terminal : IsTerminal ⊤

    module Cartesian {o h} (𝒞 : PreCat o h) where 
        open import Level using (levelOfTerm)
        open Terminal 𝒞 using (TerminalT)
        open BinaryProducts 𝒞 using (BinaryProductsT)

        record CartesianT : Set (levelOfTerm 𝒞) where 
            field 
                terminal : TerminalT
                products : BinaryProductsT
                

    module Equalizer {o ℓ} (𝒞 : PreCat o ℓ) where 
        open PreCat 𝒞

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

    module Pullback {o ℓ}(𝒞 : PreCat o ℓ) where
        open PreCat 𝒞 
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

    module Finitely {o ℓ} (𝒞 : PreCat o ℓ) where 
        open import Level using (levelOfTerm)

        open PreCat 𝒞 
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
