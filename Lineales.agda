module Lineales where
open import Cubical.Core.Everything using (_≡_; PathP;Path; I ; i0 ; i1 ; hcomp)
open import Cubical.Foundations.Prelude using (cong; cong₂;refl; transport)

open import Lineale 
open Lineale.Proset {{...}}
open Lineale.MonProset {{...}}
open Lineale.Lineale {{...}}

module Two where 
    data Two : Set where ⊤ ⊥ : Two

    data Empty : Set where 

    data Unit : Set where tt : Unit

    _⊗²_ : Two → Two → Two 
    ⊤ ⊗² ⊤ = ⊤
    ⊤ ⊗² ⊥ = ⊥
    ⊥ ⊗² ⊤ = ⊥
    ⊥ ⊗² ⊥ = ⊥

    -- modeling ⊥ → ⊤ category
    _≤²_ : Two → Two → Set 
    ⊤ ≤² ⊤ = Unit
    ⊤ ≤² ⊥ = Empty
    ⊥ ≤² ⊤ = Unit
    ⊥ ≤² ⊥ = Unit 

    ≤-refl : {x : Two} → x ≤² x 
    ≤-refl {⊤} = tt
    ≤-refl {⊥} = tt

    ≤-trans : {x y z : Two} → x ≤² y → y ≤² z → x ≤² z 
    ≤-trans {⊤} {⊤} {⊤} _ _ = tt
    ≤-trans {⊤} {⊤} {⊥} _ ()
    ≤-trans {⊤} {⊥} {z} () _ 
    ≤-trans {⊥} {⊤} {⊤} _ _ = tt
    ≤-trans {⊥} {⊤} {⊥} _ ()
    ≤-trans {⊥} {⊥} {⊤} _ _ = tt
    ≤-trans {⊥} {⊥} {⊥} _ _ = tt


    assoc' : {a b c : Two} → a ⊗² (b ⊗² c) ≡ (a ⊗² b) ⊗² c 
    assoc' {⊤} {⊤} {⊤} = refl
    assoc' {⊤} {⊤} {⊥} = refl
    assoc' {⊤} {⊥} {⊤} = refl
    assoc' {⊤} {⊥} {⊥} = refl
    assoc' {⊥} {⊤} {⊤} = refl
    assoc' {⊥} {⊤} {⊥} = refl
    assoc' {⊥} {⊥} {⊤} = refl
    assoc' {⊥} {⊥} {⊥} = refl
    
    lunity : {a : Two} → ⊤ ⊗² a ≡ a 
    lunity {⊤} = refl
    lunity {⊥} = refl

    runity : {a : Two} → a ⊗² ⊤ ≡ a 
    runity {⊤} = refl
    runity {⊥} = refl

    symm' : {a b : Two} → a ⊗² b ≡ b ⊗² a 
    symm' {⊤} {⊤} = refl
    symm' {⊤} {⊥} = refl
    symm' {⊥} {⊤} = refl
    symm' {⊥} {⊥} = refl

    compat' : {a b : Two} → a ≤² b → ({c : Two} → (a ⊗² c) ≤² (b ⊗² c))
    compat' {⊤} {⊤} p {⊤} = tt
    compat' {⊤} {⊤} p {⊥} = tt
    compat' {⊥} {⊤} p {⊤} = tt
    compat' {⊥} {⊤} p {⊥} = tt
    compat' {⊥} {⊥} p {⊤} = tt
    compat' {⊥} {⊥} p {⊥} = tt

    instance 
        two-pro : Proset Two 
        two-pro .rel = _≤²_
        two-pro .prefl = ≤-refl
        two-pro .ptrans = ≤-trans
        
        two-mon : MonProset Two 
        two-mon ._⊙_ = _⊗²_
        two-mon .unit = ⊤
        two-mon .assoc = assoc'
        two-mon .left-ident = lunity
        two-mon .right-ident = runity
        two-mon .symm = symm'
        two-mon .compat = compat'

        two-lineale : Lineale Two 
        two-lineale ._⊸_ = {!   !}
        two-lineale .rlcomp = {!   !}
        two-lineale .adj = {!   !}


    