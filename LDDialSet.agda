module LDDialSet where
open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Product
open import Function using (_∘_)

record LDepDialSet {ℓ : Level}{L : Set ℓ} : Set (lsuc ℓ) where 
    field 
        pos : Set ℓ
        dir : pos → Set ℓ
        α : (p : pos) → dir p → L

open import Lineale
record LDepDialSetMap {ℓ}{L} (A B : LDepDialSet{ℓ}{L})
        {{pl : Proset L}}
        {{_ : MonProset L}}
        {{_ : Lineale L}}: Set ℓ where 

    open Proset pl renaming (rel to _≤_)
    open LDepDialSet A 
    open LDepDialSet B renaming (pos to pos'; dir to dir'; α to β)
    field 
        f : pos → pos' 
        F : (p : pos) → (dir' (f p)) → dir p
        cond : (p : pos)(d' : dir' (f p)) → α p (F p d') ≤ β  (f p) d'

module _ {ℓ : Level}{L : Set ℓ}
        {{pl : Proset L}}
        {{mp : MonProset L}}
        {{_ : Lineale L}} where 
        
    open MonProset mp

    _⊗_ : LDepDialSet {ℓ}{L} → LDepDialSet {ℓ}{L} → LDepDialSet {ℓ} {L}
    record { pos = pos ; dir = dir ; α = α } ⊗ record { pos = pos' ; dir = dir' ; α = β } = 
        record { pos = pos × pos' ; dir = λ{(p , p') → dir p × dir' p'} ; α = λ{ (p , p') (d , d') → α p d ⊙ β p' d' }}
    --⟨ pos₁ , dir₁ , α ⟩ ⊗ ⟨ pos₂ , dir₂ , β ⟩ = ⟨ pos₁ × pos₂ , dir₁ × dir₂ , m ⟩ 
     --   where m : pos₁ × pos₂ → dir₁ × dir₂ → Two
     --         m (u , v) (x , y) =  α u x ⊗² β v y 


    _⇒L_ : (A B : LDepDialSet{ℓ}{L}) → Set ℓ
    _⇒L_ A B  = LDepDialSetMap A B
    
    _∘L_ : {A B C : LDepDialSet {ℓ} {L}} → (B ⇒L C) → (A ⇒L B) → (A ⇒L C)
    _∘L_ {A} {B} {C} record { f = g ; F = G ; cond = cond₁ } record { f = f ; F = F ; cond = cond₂ } = thing
        where 
            open LDepDialSet A renaming (pos to pos₁; dir to dir₁) 
            open LDepDialSet B renaming (pos to pos₂; dir to dir₂; α to β)
            open LDepDialSet C renaming (pos to pos₃; dir to dir₃; α to ɣ)

            open Proset pl renaming (rel to _≤_) 
            
            F' : (p : pos₁) → dir₃ (g (f p)) → dir₁ p
            F' p₁ d₃ = 
                        let p₂ = f p₁
                            d₂ = G p₂ d₃
                            d₁ = F p₁ d₂
                        in  d₁
            cond' : (p : pos₁) (d' : dir₃ (g (f p))) → (α p (F' p d')) ≤ (ɣ (g (f p)) d')
            cond' p₁ d₃ = let p₂ = f p₁
                              d₂ = G p₂ d₃
                              r1 = cond₁ p₂ d₃
                              r2 = cond₂ p₁ d₂ 
                          in ptrans r2 r1

            thing : A ⇒L C
            thing = record { f = g ∘ f ; F = F' ; cond = cond' }

     {-
        cond' : (u : pos₁)(z : dir₃) → α u (F' u z) ≤² γ (f' u) z
        cond' u z = let 
                    v = f u
                    y = G v z
                    r1 = cond₁ u y       -- : α u (F₁ u (F₂ (f₁ u) z)) ≤² β (f₁ u) (F₂ (f₁ u) z)
                    r2 = cond₂ v z       -- : β (f₁ u) (F₂ (f₁ u) z) ≤² γ (f₂ (f₁ u)) z
                    in ≤-trans r1 r2
     -}
