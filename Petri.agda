module Petri where 

open import Lineale
open import CatLib
open import Level 
open import Cubical.Core.Everything 
open import Cubical.Foundations.Prelude using (refl)


module DMLSet 
    {o ℓ : Level}
    {L : Set o} 
    {{Pro : Proset L}}
    {{Mon : MonProset L}}
    {{Lin : Lineale L }} where


    open import LDDialSet
    open LD {L = L}
    open Category
    open Proset Pro

    module eq-map {A B : LDepDialSet}{m₁ m₂ : A ⇒L B} where
        open LDepDialSet A 
        open LDepDialSet B renaming (pos to pos'; dir to dir'; α to β)

        open LDepDialSetMap m₁ renaming (cond to cond₁)
        open LDepDialSetMap m₂ renaming (f to g; F to G; cond to cond₂)

        open Proset Pro renaming (rel to _≤_)

        eq-cond : (f≡g : f ≡ g) → (F≡G : PathP (λ i → (p : pos) → dir' ((f≡g i) p) → dir p) F G) → 
            PathP (λ i → (p : pos) → (d' : dir' ((f≡g i) p)) → α p (F≡G i  p d') ≤ β (f≡g i p) d') cond₁ cond₂ 
        eq-cond = {!   !}

        eq-map : (f≡g : f ≡ g) → PathP (λ i → (p : pos) → dir' ((f≡g i) p) → dir p) F G  → m₁ ≡ m₂
        eq-map = {!   !}

    open eq-map
    
    DMLSet : Category (suc o) o 
    DMLSet .Ob = LDepDialSet
    DMLSet ._⇒_ = _⇒L_
    DMLSet .id  = (λ p → p) ∧ (λ p d → d) st (λ p d → prefl)
    DMLSet ._∘_ = _∘L_
    DMLSet .idr = eq-map refl refl
    DMLSet .idl = eq-map refl refl
    DMLSet .assoc = eq-map refl refl

    open import Data.Product
    open import Data.Sum 
    _&_ : LDepDialSet → LDepDialSet → LDepDialSet
    ⟨ pos , dir , α ⟩ & ⟨ pos' , dir' , β ⟩ = ⟨ pos × pos' , (λ{(p , p') → dir p ⊎ dir' p'}) , cond ⟩
        where 
            cond : (p : pos × pos') → (dir (proj₁ p) ⊎ dir' (proj₂ p))  → L
            cond (p , p') (inj₁ d) = α p d
            cond (p , p') (inj₂ d') = β p' d'

    _⊕_ : LDepDialSet → LDepDialSet → LDepDialSet
    ⟨ pos , dir , α ⟩ ⊕ ⟨ pos' , dir' , β ⟩ = ⟨ pos ⊎ pos' , c' , cond' ⟩ 
        where 
            -- problem
            -- This is the definition in the Dial Petri paper (extended to dependent setting)
            c : pos ⊎ pos' → Set o
            c (inj₁ p) = dir p × dir' {!   !}
            c (inj₂ p') = dir {!   !} × dir' p'

            cond : (p : pos ⊎ pos') → c p → L 
            cond (inj₁ p) (d , _) = α p d
            cond (inj₂ p') (_ , d') = β p' d'

            -- This is the map used in Poly
            c' : pos ⊎ pos' → Set o 
            c' (inj₁ p) = dir p
            c' (inj₂ p') = dir' p'

            cond' : (p : pos ⊎ pos') → c' p → L 
            cond' (inj₁ p) d = α p d
            cond' (inj₂ p') d' = β p' d'

    open MonProset Mon
    
    _⊗'_ : LDepDialSet → LDepDialSet → LDepDialSet
    ⟨ pos , dir , α ⟩ ⊗' ⟨ pos' , dir' , β ⟩ = ⟨ pos × pos' , c , cond ⟩
        where 
            c : (p : pos × pos') → Set o
            c (p , p') = dir p × dir' p'

            cond : (p : pos × pos') → c p → L 
            cond (p , p') (d , d') = α p d ⊙ β p' d'
            


    
    module NetL where 
        NetL : Category (ℓ-suc o) {!   !} 
        NetL .Ob = LDepDialSet × LDepDialSet
        NetL ._⇒_ A B = {! (A ⇒L B) × (A ⇒L B) !}
        NetL .id = {!   !}
        NetL ._∘_ = {!   !}
        NetL .idr = {!   !}
        NetL .idl = {!   !}
        NetL .assoc = {!   !}

    