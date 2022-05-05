module DC where 
open import Agda.Primitive using (Level; _⊔_)
open import CatLib using (PreCat)

module _ {o ℓ : Level}(𝒞 : PreCat o ℓ) where 
    open PreCat 𝒞
    open module Fin = CatLib.Finitely 𝒞 



    Mono : {A B : Ob} → (f : A ⇒ B) → Set (o ⊔ ℓ)
    Mono {A} f = ∀ {C} → (g₁ g₂ : C ⇒ A) → f ∘ g₁ ≣ f ∘ g₂ → g₁ ≣ g₂
{-

    Obj : {A U X : Ob} → Set (o ⊔ ℓ)
    Obj {A} {U} {X} = U × X
    -}

    
