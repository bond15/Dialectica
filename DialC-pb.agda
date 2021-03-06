module DC where 
open import Agda.Primitive using (Level; _β_)
open import CatLib using (Category;module Finitely; module BinaryProducts; module Cartesian; module Pullback; module ObjectProduct)
open import Cubical.Core.Everything using (_β‘_)

module _ {o β : Level}(π : Category o β)where 
    open Category π
    open Finitely π using (FinitelyComplete)
    module foo {fin : FinitelyComplete} where 
        open FinitelyComplete fin using (cartesian; pullback)
        open Cartesian π using (CartesianT)
        open Pullback π using (PullbackT ; IsPullback)
        open PullbackT
        open CartesianT cartesian using (products)
        open BinaryProducts π using(BinaryProductsT)
        open BinaryProductsT products using (_Γ_; product)
        open ObjectProduct π using (module Morphisms; Product)
  
        record Obj : Set (o β β) where 
            field 
                {A} {U} {X} : Ob    
                Ξ± : A β (U Γ X)
                is-monic : β {C} β (gβ gβ : C β A) β Ξ± β gβ β‘ Ξ± β gβ β gβ β‘ gβ

        open Morphisms
        open Product
        record Hom (A B : Obj) : Set (o β β) where 
            open Obj A
            open Obj B renaming (A to B; U to V; X to Y; Ξ± to Ξ²)
            field
                f : U β V 
                F : (U Γ Y) β X
           
            mβ : (U Γ Y) β (U Γ X)
            mβ = [ productΒ ]β¨ Οβ product , F β©

            mβ : (U Γ Y) β (V Γ Y)
            mβ = [ product β product ] f Γ id

            -- Ξ±' and Ξ²' should be monic
            open PullbackT (pullback Ξ± mβ) renaming (P to apexβ; pβ to Ξ±')
            open PullbackT (pullback mβ Ξ²) renaming (P to apexβ; pβ to Ξ²')

            field   
                -- should be unique
                k : apexβ β apexβ
                k-cond : Ξ²' β k β‘ Ξ±'

        open Hom
        open import Cubical.Foundations.Isomorphism using (isoToPath; iso ; Iso)
        open import Cubical.Foundations.Prelude using (_β‘β¨_β©_;β‘β¨β©-syntax;_β;cong;congβ;refl; transport; sym)
        open Iso
        open IsPullback

        module lemmas where 


            ispbsym : {P X Y Z : Ob} β (pβ : P β X) β (pβ : P β Y) β (f : X β Z) β (g : Y β Z) β 
                IsPullback pβ pβ f g β‘ IsPullback pβ pβ g f 
            ispbsym pβ pβ f g = isoToPath prf
                where prf : Iso (IsPullback pβ pβ f g) (IsPullback pβ pβ g f)
                      prf .fun ispb = record
                                        { commute = sym (ispb .commute)
                                        ; universal = Ξ» x β (ispb  .universal) (sym x)
                                        ; unique = Ξ» x y β ispb .unique y x
                                        {- 
                                        {hβ.A : Ob} {hβ : hβ.A β X} {hβ : hβ.A β Y} {eq : f β hβ β‘ g β hβ} β
                                        pβ β Pullback.IsPullback.universal ispb eq β‘ hβ

                                        {hβ.A : Ob} {hβ : hβ.A β Y} {hβ : hβ.A β X}{eq : g β hβ β‘ f β hβ} β
                                        pβ β ispb .Pullback.IsPullback.universal (Ξ» i β eq (Cubical.Foundations.Prelude.~ i)) β‘ hβ
                                        
                                        -}
                                        ; pββuniversalβhβ = {! refl!}
                                        ; pββuniversalβhβ = {!   !}
                                        }
                      prf .inv ispb = record
                                        { commute = sym (ispb .commute)
                                        ; universal = Ξ» x β (ispb  .universal) (sym x)
                                        ; unique = Ξ» x y β ispb .unique y x
                                        ; pββuniversalβhβ = {!   !}
                                        ; pββuniversalβhβ = {!   !}
                                        }
                      prf .rightInv = Ξ» b β {!   !}
                      prf .leftInv = Ξ» b β {!   !}

            -- correct notion of equality... probably not
            pbsym : {X Y Z : Ob} β (f : X β Z) β (g : Y β Z) β PullbackT f g β‘ PullbackT g f
            pbsym f g = isoToPath isoprf 
                where isoprf : Iso (PullbackT f g) (PullbackT g f)
                      isoprf .fun pbβ = record { pβ = pbβ .pβ ; pβ = pbβ .pβ ; isPullback = 
                                         record
                                            { commute = sym ((pbβ .isPullback) .commute)
                                            ; universal = Ξ» x β {!   !}
                                            ; unique = {!   !}
                                            ; pββuniversalβhβ = {!   !}
                                            ; pββuniversalβhβ = {!   !}
                                            } }
                      isoprf .inv pbβ = record { pβ = pbβ .pβ ; pβ = pbβ .pβ ; isPullback = {!   !} }
                      isoprf .rightInv = {!   !}
                      isoprf .leftInv = {!   !}


        DCid : {X : Obj} β Hom X X
        DCid .f = id
        DCid .F = Οβ product
        DCid .k = {!   !}
        DCid .k-cond = {!   !}

    
        -- now try to make a category out of this...

        DC : Category (o β β) (o β β) 
        DC .Ob = Obj
        DC ._β_ = Hom 
        DC .id = {!   !} 
        DC ._β_ = {!   !}
        DC .idr = {!   !}
        DC .idl = {!   !}
        DC .assoc = {!   !}


            
            

        

    

