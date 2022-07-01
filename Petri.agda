module Petri where 

open import Lineale
open import CatLib
open import Level 
open import Cubical.Core.Everything 
open import Cubical.Foundations.Prelude using (refl)


module DMLSet 
    {o : Level}
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
        open ProductCat
        NetL : Category (ℓ-suc o) o 
        NetL = Product DMLSet DMLSet

        open Category NetL renaming (Ob to Net)

        _⨂_ : Net → Net → Net
        (▸A , A▸) ⨂ (▸B , B▸) = (▸A ⊗' ▸B) , (A▸ ⊗' B▸)

        _⨁_ : Net → Net → Net 
        (▸A , A▸) ⨁ (▸B , B▸) = (▸A ⊕ ▸B) , (A▸ ⊕ B▸)

        _⋀_ : Net → Net → Net 
        (▸A , A▸) ⋀ (▸B , B▸) = (▸A & ▸B) , (A▸ & B▸)


        -- examples

module examples where 
    open import Natcopy
    open import Data.Nat

    -- Petri net with the ℕ lineale
    open DMLSet {L = ℕ}
    open Category NetL.NetL renaming (Ob to Net)
    open import LDDialSet
    open LD {L = ℕ}

    data Places {ℓ : Level} : Set ℓ where
        P₁ P₂ P₃ : Places 

    data Places' {ℓ : Level} : Set ℓ where 
       P₁' P₂' : Places'

    data Trans {ℓ : Level} : Set ℓ where 
        T₁ : Trans

    data Trans' {ℓ : Level} : Set ℓ where 

    data Trans'' {ℓ : Level} : Set ℓ where 
        T₁ T₂ T₃ : Trans''


    data fin : ℕ → Set where 
        z : fin 0
        s : {n : ℕ} → fin n → fin (ℕ.suc n)

    
    sub : Set → ℕ → Set 
    sub T n = fin n → T


    n₁' : Net -- something is wrong with this formalization... should have subsets
    n₁' = ⟨ Places , (λ {P₁ → sub Trans'' 2
                       ; P₂ → {!   !}
                       ; P₃ → {!   !}}) , (λ {P₁ y → {!  !}
                                            ; P₂ y → {!   !}
                                            ; P₃ y → {!   !}}) ⟩ , {!   !}
    n₁ : Net 
    n₁ = ⟨ Places , (λ{ P₁ → Trans
                      ; P₂ → Trans
                      ; P₃ → Trans'}) , (λ {P₁ T₁ → 2
                                          ; P₂ T₁ → 3}) ⟩ , 
        ⟨ Places , (λ{P₁ → Trans'
                    ; P₂ → Trans'
                    ; P₃ → Trans}) , (λ{P₃ T₁ → 2 }) ⟩


    n₂ : Net 
    n₂ = ⟨ Places , (λ{ P₁ → Trans
                      ; P₂ → Trans
                      ; P₃ → Trans'}) , (λ {P₁ T₁ → 2
                                          ; P₂ T₁ → 1}) ⟩ , 
        ⟨ Places , (λ{P₁ → Trans'
                    ; P₂ → Trans'
                    ; P₃ → Trans}) , (λ{P₃ T₁ → 2 }) ⟩

    n₃ : Net 
    n₃ = ⟨ Places' , (λ{P₁' → Trans
                      ; P₂' → Trans'}) , (λ{P₁' T₁ → 2}) ⟩ , 
                      
        ⟨ Places' , (λ{P₁' → Trans'
                     ; P₂' → Trans}) , (λ{ P₂' T₁ → 1}) ⟩


    -- example A
    m₁ : n₁ ⇒ n₂
    m₁ = ((λ {P₁ → P₁
            ; P₂ → P₂
            ; P₃ → P₃}) ∧ (λ{ P₁ T₁ → T₁
                            ; P₂ T₁ → T₁}) st λ{P₁ T₁ → ≥-refl -- 2 ≥ 2
                                              ; P₂ T₁ → s≥s n≥z}), -- 3 ≥ 1 
         ((λ{P₁ → P₁
           ; P₂ → P₂
           ; P₃ → P₃}) ∧ (λ {P₃ T₁ → T₁}) st λ {P₃ T₁ →  ≥-refl}) -- 2 ≥ 2

    -- example B
    m₂ : n₃ ⇒ n₂ 
    m₂ = ((λ{ P₁' → P₁
            ; P₂' → P₂}) ∧ {!   !} st {!   !}) , 
            ((λ{ P₁' → {! 2  !}
               ; P₂' → {!   !} }) ∧ {!   !} st {!   !})





    {-


    n₁ : Net 
    n₁ = ⟨ Pos₃ , (λ{ P₁ → Dir₁
                    ; P₂ → Dir₁
                    ; P₃ → Dir₁}) , (λ{P₁ D₁ → {!   !}
                                     ; P₂ D₁ → {!   !}
                                     ; P₃ D₁ → {!   !}}) ⟩ , ⟨ {!   !} , {!   !} , {!   !} ⟩

-}
    