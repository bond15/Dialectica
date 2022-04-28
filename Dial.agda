module Dial where 
open import Agda.Primitive
open import Data.Product

open import Lineale

module defs {ℓ : Level}{L : Set ℓ}
    {{ Pro : Proset L }}
    {{ _ : MonProset L }}
    {{ _ : Lineale L}} where    
    
    open module Pro = Proset Pro renaming (rel to _≤L_)

    {- TODO 
        * wrap these constructions in a PreCategory definition
        * Don't implicitly use Agda's Set as the base Category
            parameterize definition by a base PreCategory
    -}
    record Obj : Set (lsuc ℓ) where 
        field 
            {U} : Set ℓ
            {X} : Set ℓ
            rl : U → X → L

    record Hom (A B : Obj): Set ℓ where 
        open module A = Obj A renaming (rl to α)
        open module B = Obj B renaming (U to V ; X to Y ; rl to β)
        field 
            f : U → V
            F : Y → X
            cond : ∀ {u : U} {y : Y} → α u (F y) ≤L β (f u) y 
