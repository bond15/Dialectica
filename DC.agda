module DC where 
open import Agda.Primitive using (Level)
open import CatLib using (PreCat)

module _ {o h : Level}(𝒞 : PreCat o h) where 
    open PreCat 𝒞
    open CatLib.Finitely 𝒞 using (FinitelyComplete)

    
