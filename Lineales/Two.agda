module Two where
open import Cubical.Core.Everything using (_≡_; PathP;Path; I ; i0 ; i1 ; hcomp)
open import Cubical.Foundations.Prelude using (cong; cong₂;refl; transport)

open import Lineale 
open Lineale.Proset {{...}}
open Lineale.MonProset {{...}}
open Lineale.Lineale {{...}}


data Two : Set where ⊤ ⊥ : Two

data Empty : Set where 

data Unit : Set where tt : Unit

_⊗²_ : Two → Two → Two 
⊤ ⊗² ⊤ = ⊤
⊤ ⊗² ⊥ = ⊥
⊥ ⊗² ⊤ = ⊥
⊥ ⊗² ⊥ = ⊥

_⊸²_ : Two → Two → Two 
⊤ ⊸² ⊤ = ⊤
⊤ ⊸² ⊥ = ⊥
⊥ ⊸² ⊤ = ⊤
⊥ ⊸² ⊥ = ⊤

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

compatˡ' : {a b : Two} → a ≤² b → ({c : Two} → (c ⊗² a) ≤² (c ⊗² b))
compatˡ' {⊤} {⊤} p {⊤} = tt
compatˡ' {⊤} {⊤} p {⊥} = tt
compatˡ' {⊥} {⊤} p {⊤} = tt
compatˡ' {⊥} {⊤} p {⊥} = tt
compatˡ' {⊥} {⊥} p {⊤} = tt
compatˡ' {⊥} {⊥} p {⊥} = tt
    
compatʳ' : {a b : Two} → a ≤² b → ({c : Two} → (a ⊗² c) ≤² (b ⊗² c))
compatʳ' {⊤} {⊤} p {⊤} = tt
compatʳ' {⊤} {⊤} p {⊥} = tt
compatʳ' {⊥} {⊤} p {⊤} = tt
compatʳ' {⊥} {⊤} p {⊥} = tt
compatʳ' {⊥} {⊥} p {⊤} = tt
compatʳ' {⊥} {⊥} p {⊥} = tt

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
    two-mon .compatˡ = compatˡ'
    two-mon .compatʳ = compatʳ'

    two-lineale : Lineale Two 
    two-lineale ._⊸_ = _⊸²_
    two-lineale .rlcomp {⊤} {⊤} = tt
    two-lineale .rlcomp {⊤} {⊥} = tt
    two-lineale .rlcomp {⊥} {⊤} = tt
    two-lineale .rlcomp {⊥} {⊥} = tt
    two-lineale .adj {⊤} {⊤} {⊤} h = tt
    two-lineale .adj {⊤} {⊤} {⊥} h = tt
    two-lineale .adj {⊤} {⊥} {⊥} h = tt
    two-lineale .adj {⊥} {⊤} {⊤} h = tt
    two-lineale .adj {⊥} {⊤} {⊥} h = tt
    two-lineale .adj {⊥} {⊥} {⊤} h = tt
    two-lineale .adj {⊥} {⊥} {⊥} h = tt
