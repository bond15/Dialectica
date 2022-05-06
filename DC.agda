module DC where 
open import Agda.Primitive using (Level; _⊔_)
open import CatLib using (PreCat;module Finitely; module BinaryProducts; module Cartesian; module Pullback; module ObjectProduct)
open import Cubical.Core.Everything using (_≡_)

module _ {o ℓ : Level}(𝒞 : PreCat o ℓ)where 
    open PreCat 𝒞
    open Finitely 𝒞 using (FinitelyComplete)
    module foo {fin : FinitelyComplete} where 
        open FinitelyComplete fin using (cartesian; pullback)
        open Cartesian 𝒞 using (CartesianT)
        open Pullback 𝒞 using (PullbackT ; IsPullback)
        open PullbackT
        open CartesianT cartesian using (products)
        open BinaryProducts 𝒞 using(BinaryProductsT)
        open BinaryProductsT products using (_×_; product)
        open ObjectProduct 𝒞 using (module Morphisms; Product)
  
        record Obj : Set (o ⊔ ℓ) where 
            field 
                {A} {U} {X} : Ob    
                α : A ⇒ (U × X)
                is-monic : ∀ {C} → (g₁ g₂ : C ⇒ A) → α ∘ g₁ ≡ α ∘ g₂ → g₁ ≡ g₂

        open Morphisms
        open Product
        record Hom (A B : Obj) : Set (o ⊔ ℓ) where 
            open Obj A
            open Obj B renaming (A to B; U to V; X to Y; α to β)
            field
                f : U ⇒ V 
                F : (U × Y) ⇒ X
           
            m₁ : (U × Y) ⇒ (U × X)
            m₁ = [ product ]⟨ π₁ product , F ⟩

            m₂ : (U × Y) ⇒ (V × Y)
            m₂ = [ product ⇒ product ] f × id

            -- α' and β' should be monic
            open PullbackT (pullback α m₁) renaming (P to apex₁; p₂ to α')
            open PullbackT (pullback m₂ β) renaming (P to apex₂; p₁ to β')

            field   
                -- should be unique
                k : apex₁ ⇒ apex₂
                k-cond : β' ∘ k ≡ α'

        open Hom
        open import Cubical.Foundations.Isomorphism using (isoToPath; iso ; Iso)
        open import Cubical.Foundations.Prelude using (_≡⟨_⟩_;≡⟨⟩-syntax;_∎;cong;cong₂;refl; transport; sym)
        open Iso
        open IsPullback

        module lemmas where 


            ispbsym : {P X Y Z : Ob} → (p₁ : P ⇒ X) → (p₂ : P ⇒ Y) → (f : X ⇒ Z) → (g : Y ⇒ Z) → 
                IsPullback p₁ p₂ f g ≡ IsPullback p₂ p₁ g f 
            ispbsym p₁ p₂ f g = isoToPath prf
                where prf : Iso (IsPullback p₁ p₂ f g) (IsPullback p₂ p₁ g f)
                      prf .fun ispb = record
                                        { commute = sym (ispb .commute)
                                        ; universal = λ x → (ispb  .universal) (sym x)
                                        ; unique = λ x y → ispb .unique y x
                                        {- 
                                        {h₂.A : Ob} {h₁ : h₂.A ⇒ X} {h₂ : h₂.A ⇒ Y} {eq : f ∘ h₁ ≡ g ∘ h₂} →
                                        p₁ ∘ Pullback.IsPullback.universal ispb eq ≡ h₁

                                        {h₂.A : Ob} {h₁ : h₂.A ⇒ Y} {h₂ : h₂.A ⇒ X}{eq : g ∘ h₁ ≡ f ∘ h₂} →
                                        p₂ ∘ ispb .Pullback.IsPullback.universal (λ i → eq (Cubical.Foundations.Prelude.~ i)) ≡ h₁
                                        
                                        -}
                                        ; p₁∘universal≈h₁ = {! refl!}
                                        ; p₂∘universal≈h₂ = {!   !}
                                        }
                      prf .inv ispb = record
                                        { commute = sym (ispb .commute)
                                        ; universal = λ x → (ispb  .universal) (sym x)
                                        ; unique = λ x y → ispb .unique y x
                                        ; p₁∘universal≈h₁ = {!   !}
                                        ; p₂∘universal≈h₂ = {!   !}
                                        }
                      prf .rightInv = λ b → {!   !}
                      prf .leftInv = λ b → {!   !}

            -- correct notion of equality... probably not
            pbsym : {X Y Z : Ob} → (f : X ⇒ Z) → (g : Y ⇒ Z) → PullbackT f g ≡ PullbackT g f
            pbsym f g = isoToPath isoprf 
                where isoprf : Iso (PullbackT f g) (PullbackT g f)
                      isoprf .fun pb₁ = record { p₁ = pb₁ .p₂ ; p₂ = pb₁ .p₁ ; isPullback = 
                                         record
                                            { commute = sym ((pb₁ .isPullback) .commute)
                                            ; universal = λ x → {!   !}
                                            ; unique = {!   !}
                                            ; p₁∘universal≈h₁ = {!   !}
                                            ; p₂∘universal≈h₂ = {!   !}
                                            } }
                      isoprf .inv pb₂ = record { p₁ = pb₂ .p₂ ; p₂ = pb₂ .p₁ ; isPullback = {!   !} }
                      isoprf .rightInv = {!   !}
                      isoprf .leftInv = {!   !}


        DCid : {X : Obj} → Hom X X
        DCid .f = id
        DCid .F = π₂ product
        DCid .k = {!   !}
        DCid .k-cond = {!   !}

    
        -- now try to make a category out of this...
        DC : PreCat (o ⊔ ℓ) (o ⊔ ℓ) 
        DC .Ob = Obj
        DC ._⇒_ = Hom 
        DC .Hom-set = {!   !}
        DC .id = {!   !} 
        DC ._∘_ = {!   !}
        DC .idr = {!   !}
        DC .idl = {!   !}
        DC .assoc = {!   !}


            
            

        

    
  