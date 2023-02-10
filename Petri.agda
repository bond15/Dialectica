module Petri where 

open import Lineale
open import CatLib
open import Level 
open import Cubical.Core.Everything 
open import Cubical.Foundations.Prelude using (refl)


module demo where 
    
module subtyping {ℓ : Level} where
    open import Data.Bool
    open import Data.Empty
    open import Data.List
    open import Data.Nat
    open import Data.Unit

    -- decidable equality
    record Dec (T : Set ℓ) : Set ℓ where
        constructor MkDec 
        field 
            eqb : T → T → Bool 
    open Dec{{...}}

    _∈_ : {T : Set ℓ}{{ _ : Dec T}} → (t : T) → (xs : List T) → Set ℓ
    _∈_ t [] = Lift ℓ ⊥
    _∈_ t (x ∷ xs) with eqb t x
    ...             | true  = Lift ℓ ⊤
    ...             | false = t ∈ xs
        
    -- A subset of a type with decidable equality
    sub : {T : Set ℓ}{{_ : Dec T}} → List T → Set ℓ
    sub {T} xs = Σ[ t ∈ T ] (t ∈ xs)

    powerset : (T : Set ℓ)⦃ _ : Dec T ⦄ → Set ℓ 
    powerset T = Σ (List T) λ xs → sub xs

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
{-
    Not neccesaryily the case given the choice of relation on the carrirer of the Lineale.
    Instead parameterize the definition of Category by then correct notion of equality on morphisms.
-}
    module eq-map {A B : LDepDialSet}{m₁ m₂ : A ⇒L B} where
        open LDepDialSet A 
        open LDepDialSet B renaming (pos to pos'; dir to dir'; α to β)

        open LDepDialSetMap m₁ renaming (cond to cond₁)
        open LDepDialSetMap m₂ renaming (f to g; F to G; cond to cond₂)

        open Proset Pro renaming (rel to _≤_)

        -- This is false unless we have that the relation is a Set (HoTT Set)
        -- What do we want to use?
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

    module Petri where
        open subtyping
        open import Level
        open import Data.List

        {-record PetriOb (tr : Set o) : Set (suc o) where 
            constructor ⟨_,_,_⟩
            field 
                place : Set o
                tran : place → Σ (List tr) λ xs → Lift _ {! sub xs  !}
                --α' : (p : place) → tran p → L -}

    {-}
        PetriCat : Category (suc o) o 
        PetriCat .Ob = LDepDialSet
        PetriCat ._⇒_ = _⇒L_
        PetriCat .id  = (λ p → p) ∧ (λ p d → d) st (λ p d → prefl)
        PetriCat ._∘_ = _∘L_
        PetriCat .idr = eq-map refl refl
        PetriCat .idl = eq-map refl refl
        PetriCat .assoc = eq-map refl refl   
        -}     


        -- examples




module examples where
    open import Data.Nat
    open import Data.Bool
    open import Data.List
    open subtyping

    open import Nat -- the Lineale on ℕ
    open DMLSet {L = ℕ} -- the Category Dependent Dialectical on ℕ
    open Category NetL.NetL renaming (Ob to Net) -- The Petri net Category based on DMLSet ℕ
    open import LDDialSet
    open LD {L = ℕ}
    open NetL


    {-     
            3 ---->[T₁]--- 4
          /                ↓    6       2
        P₁                 P₂--> [t₃] -> P₃
          \                ↑ 
           2 ----->[T₂]--- 1
    -}
    data Places : Set where 
        P₁ P₂ P₃  : Places

    data Transitions : Set where 
        T₁ T₂ T₃ : Transitions

    instance 
        T-dec : Dec Transitions
        T-dec = MkDec _==_
            where 
                _==_ : Transitions → Transitions → Bool
                T₁ == T₁ = true
                T₂ == T₂ = true
                T₃ == T₃ = true
                _  == _  = false

    {-     
            3 ---->[T₁]--- 4
          /                ↓   6       2
        P₁                 P₂--> [t₃] -> P₃
          \                ↑ 
           2 ----->[T₂]--- 1
    -}
    --\blacktriangleright
    net : Net
    net = ▸A , A▸
        where 
            -- maps into places
            ▸arrows : Places → Set 
            ▸arrows P₁ = sub []
            ▸arrows P₂ = sub (T₁ ∷ T₂ ∷ [])
            ▸arrows P₃ = sub (T₃ ∷ [])

            ▸values : (p : Places) → ▸arrows p → ℕ 
            ▸values P₂ (T₁ , _) = 4
            ▸values P₂ (T₂ , _) = 1
            ▸values P₃ (T₃ , _) = 2

            ▸A = ⟨ Places , ▸arrows , ▸values ⟩

            -- maps out of places
            arrows▸ : Places → Set 
            arrows▸ P₁ = sub (T₁ ∷ T₂ ∷ [])
            arrows▸ P₂ = sub (T₃ ∷ [])
            arrows▸ P₃ = sub []

            values▸ : (p : Places) → arrows▸ p → ℕ 
            values▸ P₁ (T₁ , _) = 3
            values▸ P₁ (T₂ , _) = 2
            values▸ P₂ (T₃ , _) = 6
            
            A▸ = ⟨ Places , arrows▸ , values▸ ⟩


module example-mapping where
    open import Data.Bool
    open import Data.List
    open import Data.Nat hiding(_≥_)
    open subtyping
    
    open import Nat -- the Lineale on ℕ
    open DMLSet {L = ℕ} -- the Category Dependent Dialectical on ℕ
    open Category NetL.NetL renaming (Ob to Net) -- The Petri net Category based on DMLSet ℕ
    open import LDDialSet
    open LD {L = ℕ}


    data Places₁ : Set where 
        P₁ P₂ P₃ : Places₁

    data Places₂ : Set where 
        P₄ P₅ : Places₂

    data Transitions₁ : Set where 
        T₁ : Transitions₁

    data Transitions₂ : Set where 
        T₂ : Transitions₂ 

    instance 
        _ : Dec Transitions₁
        _ = MkDec (λ x y → true)

        _ : Dec Transitions₂ 
        _ = MkDec (λ x y → true)



    {- 

        P₁ 
          \2     2
           [T₁]---> P₃
          /3
        P₂
    -}
    net₁ : Net 
    net₁ = ▸A , A▸
        where 
            ▸arrows : Places₁ → Set
            ▸arrows P₁ = sub {T = Transitions₁} []
            ▸arrows P₂ = sub {T = Transitions₁} []
            ▸arrows P₃ = sub [ T₁ ]

            ▸values : (p : Places₁) → ▸arrows p → ℕ
            ▸values P₃ (T₁ , _) = 2
            
            ▸A = ⟨ Places₁ , ▸arrows , ▸values ⟩

            arrows▸ : Places₁ → Set
            arrows▸ P₁ = sub [ T₁ ]
            arrows▸ P₂ = sub [ T₁ ]
            arrows▸ P₃ = sub {T = Transitions₁} []

            values▸ : (p : Places₁) → arrows▸ p → ℕ
            values▸ P₁ (T₁ , _) = 2
            values▸ P₂ (T₁ , _) = 3

            A▸ = ⟨ Places₁ , arrows▸ , values▸ ⟩


    getPlaces : (n : Net) → Set 
    getPlaces n = pos
        where 
            open LD.LDepDialSet (fst n)


    -- Net doesn't seem to just be a direct product.. we want the set of places to be the same?
    record coherent (n : Net) : Set₁ where
        open LD.LDepDialSet (fst n) renaming (pos to places₁)
        open LD.LDepDialSet (snd n) renaming (pos to places₂)
        field 
            places≡ : places₁ ≡ places₂
            --transitions≡ : (p₁ : places₁)(p₂ : places₂) → {!   !}


    -- example trace
    module tokengame (n : Net)(coh : coherent n) where 

        State : Set 
        State = getPlaces n → ℕ

        -- chose transition to fire


       -- data ValidTransition : Net → Net → Set₁ where
                
            

    {- 
            2          1
        P₄ ---> [T₂] ---> P₅
    
    -}
    net₂ : Net 
    net₂ = ▸A , A▸
        where 
            ▸arrows : Places₂ → Set
            ▸arrows P₄ = sub {T = Transitions₂} []
            ▸arrows P₅ = sub [ T₂ ]

            ▸values : (p : Places₂) → ▸arrows p → ℕ
            ▸values P₅ (T₂ , _) = 1
            
            ▸A = ⟨ Places₂ , ▸arrows , ▸values ⟩

            arrows▸ : Places₂ → Set
            arrows▸ P₄ = sub [ T₂ ]
            arrows▸ P₅ = sub {T = Transitions₂} []

            values▸ : (p : Places₂) → arrows▸ p → ℕ
            values▸ P₄ (T₂ , _) = 2
            A▸ = ⟨ Places₂ , arrows▸ , values▸ ⟩
{- 

        P₁ 
          \2     2
           [T₁]---> P₃
          /1
        P₂
    -}
    net₃ : Net 
    net₃ = ▸A , A▸
        where 
            ▸arrows : Places₁ → Set
            ▸arrows P₁ = sub {T = Transitions₁} []
            ▸arrows P₂ = sub {T = Transitions₁} []
            ▸arrows P₃ = sub [ T₁ ]

            ▸values : (p : Places₁) → ▸arrows p → ℕ
            ▸values P₃ (T₁ , _) = 2
            
            ▸A = ⟨ Places₁ , ▸arrows , ▸values ⟩

            arrows▸ : Places₁ → Set
            arrows▸ P₁ = sub [ T₁ ]
            arrows▸ P₂ = sub [ T₁ ]
            arrows▸ P₃ = sub {T = Transitions₁} []

            values▸ : (p : Places₁) → arrows▸ p → ℕ
            values▸ P₁ (T₁ , _) = 2
            values▸ P₂ (T₁ , _) = 1

            A▸ = ⟨ Places₁ , arrows▸ , values▸ ⟩
{- 

        P₁ 
          \2     1
           [T₁]---> P₃
          /1
        P₂
    -}
    net₄ : Net 
    net₄ = ▸A , A▸
        where 
            ▸arrows : Places₁ → Set
            ▸arrows P₁ = sub {T = Transitions₁} []
            ▸arrows P₂ = sub {T = Transitions₁} []
            ▸arrows P₃ = sub [ T₁ ]

            ▸values : (p : Places₁) → ▸arrows p → ℕ
            ▸values P₃ (T₁ , _) = 1
            
            ▸A = ⟨ Places₁ , ▸arrows , ▸values ⟩

            arrows▸ : Places₁ → Set
            arrows▸ P₁ = sub [ T₁ ]
            arrows▸ P₂ = sub [ T₁ ]
            arrows▸ P₃ = sub {T = Transitions₁} []

            values▸ : (p : Places₁) → arrows▸ p → ℕ
            values▸ P₁ (T₁ , _) = 2
            values▸ P₂ (T₁ , _) = 1

            A▸ = ⟨ Places₁ , arrows▸ , values▸ ⟩



    {- 

        P₁ 
          \2     2
           [T₁]---> P₃
          /3
        P₂

            ⟱   

        P₁ 
          \2     2
           [T₁]---> P₃
          /1
        P₂
        
    -}
    -- maps between nets!
    open LDepDialSet
    m₁ : net₁ ⇒ net₃
    m₁ = ▸A⇒▸B , A▸⇒B▸
        where   
            ▸A = fst net₁
            A▸ = snd net₁
            ▸B = fst net₃
            B▸ = snd net₃
            
            -- not changing positions
            ▸f : Places₁ → Places₁
            ▸f x = x

            -- not changing arrows
            ▸F : (p : Places₁) → (▸B .dir) (▸f p) → (▸A .dir) p
            ▸F P₃ x = x
            
            ▸cond : (p : Places₁) → (d' : (▸B .dir)(▸f p)) → 
                (▸A .α) p (▸F p d') ≥ (▸B .α) (▸f p) d'
            ▸cond P₃ (T₁ , _) = ≥-refl -- 2 ≥ 2
            
            ▸A⇒▸B = ▸f ∧ ▸F st ▸cond 

            f▸ : Places₁ → Places₁ 
            f▸ x = x

            F▸ : (p : Places₁) → (B▸ .dir) (f▸ p) → (A▸ .dir) p
            F▸ P₁ x = x
            F▸ P₂ x = x

            cond▸ : (p : Places₁) → (d' : (B▸ .dir)(f▸ p)) → 
                (A▸ .α) p (F▸ p d') ≥ (B▸ .α) (f▸ p) d'
            cond▸ P₁ (T₁ , _) = ≥-refl -- 2 ≥ 2
            cond▸ P₂ (T₁ , _) = s≥s n≥z -- 3 ≥ 1  -- really the only thing that changes in this map

            A▸⇒B▸ = f▸ ∧ F▸ st cond▸



{- 

           2          1
        P₄ ---> [T₂] ---> P₅
 
                ⟱
                
        P₁ 
          \2     1
           [T₁]---> P₃
          /1
        P₂
    -}
    m₂ : net₂ ⇒ net₄
    m₂ = ▸A⇒▸B , A▸⇒B▸
        where   
            ▸A = fst net₂
            A▸ = snd net₂
            ▸B = fst net₄
            B▸ = snd net₄ 

            ▸f : Places₂ → Places₁
            ▸f P₄ = P₁
            ▸f P₅ = P₃

            ▸F : (p : Places₂) → (▸B .dir) (▸f p) → (▸A .dir) p
            ▸F P₅ (T₁ , _) = T₂ , _

            ▸cond : (p : Places₂) → (d' : (▸B .dir)(▸f p)) → 
                (▸A .α) p (▸F p d') ≥ (▸B .α) (▸f p) d'
            ▸cond P₅ (T₁ , _) = ≥-refl -- 1 ≥ 1

            ▸A⇒▸B  = ▸f ∧ ▸F st ▸cond 

            f▸ : Places₂ → Places₁
            f▸ P₄ = P₁
            f▸ P₅ = P₃

            F▸ : (p : Places₂) → (B▸ .dir) (f▸ p) → (A▸ .dir) p
            F▸ P₄ (T₁ , _) = T₂ , _
            
            cond▸ : (p : Places₂) → (d' : (B▸ .dir)(f▸ p)) → 
                (A▸ .α) p (F▸ p d') ≥ (B▸ .α) (f▸ p) d'
            cond▸ P₄ (T₁ , _) = ≥-refl -- 2 ≥ 2

            A▸⇒B▸ = f▸ ∧ F▸ st cond▸


    open NetL
    net₅ : Net
    net₅ = net₁ ⨂ net₂




{-
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
        z : {n : ℕ} → fin n
        s : {n : ℕ} → fin n → fin (ℕ.suc n)

    open import Data.List
    open import Data.Empty
    open import Data.Unit 
    open import Data.Bool
    
    record Dec (T : Set) : Set where
        constructor MkDec 
        field 
            eqb : T → T → Bool 
    open Dec{{...}}

    instance
        ℕ-dec : Dec ℕ 
        ℕ-dec = MkDec _==_
            where 
                _==_ : ℕ → ℕ → Bool 
                zero == zero = true
                suc x == suc y = x == y
                _ == _ = false

    inn : {T : Set}{{ _ : Dec T}} → (t : T) → (xs : List T) → Set
    inn t [] = ⊥
    inn t (x ∷ xs) with eqb t x
    ...             | true  = ⊤
    ...             | false = ⊥
    
    sub : {T : Set}{{_ : Dec T}} → List T → Set 
    sub {T} xs = Σ[ t ∈ T ] inn t xs

    _ : sub (4 ∷ 2 ∷ 7 ∷ [])
    _ = 4 , tt
   

    n₁' : Net 
    n₁' = ▸A , A▸
        where 
            ▸A = ⟨ Places , (λ{P₁ → sub {! T₁ ∷ [] !}
                             ; P₂ → sub {!   !}
                             ; P₃ → sub {!   !}}) , {!   !} ⟩

            A▸ = ⟨ Places , {!   !} , {!   !} ⟩
            
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
-}   
  