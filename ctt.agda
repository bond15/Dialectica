module ctt where 
--open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)
open import Cubical.Core.Everything using (_≡_; I ; i0; i1; cong)
open import Cubical.Foundations.Prelude using (cong)

open import Data.Nat



data int : Set where 
    neg : ℕ → int 
    pos : ℕ → int 
    eq : neg 0 ≡ pos 0 





{-
funext : {A B : Set}(f g : A → B)(p : ∀ (x : A) → f x ≡ g x) → f ≡ g 
funext f g p = λ i → λ a → p a i


postulate
    funext' : {A B : Set}(f g : A → B)(p : ∀ (x : A) → f x ≡ g x) → f ≡ g 

-}