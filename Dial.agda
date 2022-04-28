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
                use display category?
    -}
    record DObj : Set (lsuc ℓ) where 
        constructor _⇒_∍_
        field 
            U : Set ℓ
            X : Set ℓ
            rl : U → X → L

    record DHom (A B : DObj): Set ℓ where 
        constructor _⟫_⟪_
        open module A = DObj A renaming (rl to α)
        open module B = DObj B renaming (U to V ; X to Y ; rl to β)
        field 
            f : U → V
            F : Y → X
            cond : ∀ {u : U} {y : Y} → α u (F y) ≤L β (f u) y 


    _；_ : ∀{ℓ : Level} {A B C : Set ℓ} → (A → B) → (B → C) → (A → C) 
    _；_ f g x = g (f x)

    comp : {A B C : DObj} → DHom B C → DHom A B → DHom A C
    comp {U ⇒ X ∍ α} {V ⇒ Y ∍ β} {W ⇒ Z ∍ γ} (g ⟫ G ⟪ p₂) (f ⟫ F ⟪ p₁)
        = (f ； g) ⟫ G ； F ⟪ prf 
        where 
            prf : {u : U}{z : Z} → α u (F (G z)) ≤L γ (g (f u)) z
            prf {u} {z} = ptrans p₁ p₂

    infixl 5 _⊚_
    _⊚_ = comp

    id : {ℓ : Level}{A : Set ℓ} → A → A 
    id x = x

    Did : {A : DObj} → DHom A A 
    Did = id ⟫ id ⟪ prefl

    open import Cubical.Core.Everything using (_≡_)
    open import Cubical.Foundations.Prelude using (refl)

    infix 4 _≡h_
    
    _≡h_ : {A B : DObj} → (f g : DHom A B) → Set ℓ 
    _≡h_ (f ⟫ F ⟪ _) (g ⟫ G ⟪ _) = f ≡ g × F ≡ G


    ⊚-idl : ∀{A B}{f : DHom A B} → (Did ⊚ f) ≡h f 
    ⊚-idl = refl , refl

    ⊚-idr : ∀{A B}{f : DHom A B} → (f ⊚ Did) ≡h f 
    ⊚-idr = refl , refl

    ⊚-assoc : ∀{A B C D}{h : DHom A B}{g : DHom B C}{f : DHom C D} → (f ⊚ (g ⊚ h)) ≡h ((f ⊚ g) ⊚ h)
    ⊚-assoc = refl , refl

    
module asPreCat {ℓ : Level}{L : Set ℓ}
    {{ Pro : Proset L }}
    {{ _ : MonProset L }}
    {{ _ : Lineale L}} where 

    open defs renaming (id to id')

    open import Cubical.Core.Everything using (_≡_)
    open import Data.Nat using (ℕ;suc)

    record is-contr {ℓ} (A : Set ℓ) : Set ℓ where
        constructor contr 
        field 
            centre : A 
            paths : (x : A) → centre ≡ x
    open is-contr public

    is-prop : ∀{ℓ} → Set ℓ → Set _ 
    is-prop A = (x y : A) → x ≡ y  

    is-hlevel : ∀{ℓ} → Set ℓ → ℕ → Set _ 
    is-hlevel A 0 = is-contr A
    is-hlevel A 1 = is-prop A
    is-hlevel A (suc n) = (x y : A) → is-hlevel (x ≡ y) n

    is-set : ∀{ℓ} → Set ℓ → Set ℓ 
    is-set A = is-hlevel A 2

    record PreCat (o h : Level) : Set (lsuc (o ⊔ h)) where 
        field 
            Ob : Set o
            Hom : Ob → Ob → Set h
            Hom-set : (x y : Ob) → is-set (Hom x y) -- if p : x ≡ y, q : x ≡ y, then p ≡ q
            id : ∀ {x} → Hom x x
            _≣_ : ∀{A B}→ (f g : Hom A B) → Set h
            _∘_ : ∀{x y z} → Hom y z → Hom x y → Hom x z

            idr : ∀{x y}{f : Hom x y} → (f ∘ id) ≣ f 
            idl : ∀{x y}{f : Hom x y} → id ∘ f ≣ f
            assoc : ∀{w x y z} {f : Hom y z}{g : Hom x y}{h : Hom w x} → f ∘ (g ∘ h) ≣ (f ∘ g) ∘ h
        infixr 40 _∘_

    Dial : PreCat (lsuc ℓ) ℓ
    Dial = record
        { Ob = DObj
        ; Hom = DHom
        ; Hom-set = {!   !}
        ; id = Did
        ; _≣_ = _≡h_
        ; _∘_ = _⊚_
        ; idr = ⊚-idr
        ; idl = ⊚-idl
        ; assoc = ⊚-assoc
        } 