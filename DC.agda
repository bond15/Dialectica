module DC where 
open import Agda.Primitive using (Level; _⊔_)
open import CatLib using (PreCat;module Finitely; module BinaryProducts; module Cartesian; module Pullback; module ObjectProduct)

module _ {o ℓ : Level}(𝒞 : PreCat o ℓ)where 
    open PreCat 𝒞
    open Finitely 𝒞 using (FinitelyComplete)
    module foo {fin : FinitelyComplete} where 
        open FinitelyComplete fin using (cartesian; pullback)
        open Cartesian 𝒞 using (CartesianT)
        open Pullback 𝒞 using (PullbackT)
        open PullbackT
        open CartesianT cartesian using (products)
        open BinaryProducts 𝒞 using(BinaryProductsT)
        open BinaryProductsT products using (_×_; product)
        open ObjectProduct 𝒞 using (module Morphisms; Product)
  
        record Obj : Set (o ⊔ ℓ) where 
            field 
                {A} {U} {X} : Ob    
                α : A ⇒ (U × X)
                is-monic : ∀ {C} → (g₁ g₂ : C ⇒ A) → α ∘ g₁ ≣ α ∘ g₂ → g₁ ≣ g₂

        record Hom (A B : Obj) : Set (o ⊔ ℓ) where 
            open Morphisms
            open Product
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
                k-cond : β' ∘ k ≣ α'


            
            

        

    
 