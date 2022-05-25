module Lineale where

{- 
 These definitions are from 
 https://github.com/heades/cut-fill-agda/blob/master/lineale.agda
-}
open import Agda.Primitive
open import Cubical.Core.Everything using (_≡_;_≃_;equivFun; PathP; i0; i1)
open import Cubical.Foundations.Prelude using (_≡⟨_⟩_;≡⟨⟩-syntax;_∎;cong;cong₂;refl; transport; sym)
open import Cubical.Foundations.Univalence using (pathToEquiv)

record Proset {ℓ : Level}(A : Set ℓ) : Set (lsuc ℓ) where
  constructor MkProset
  field
    rel : A → A → Set ℓ
    prefl : ∀{a : A} → rel a a
    ptrans : ∀{a b c : A} → rel a b → rel b c → rel a c
open Proset {{...}}

-- wiring diagrams representation?
record MonProset {ℓ : Level}(P : Set ℓ){{ _ : Proset P}} : Set (lsuc ℓ) where
 constructor MkMonProset
 infixl 20 _⊙_
 field
   _⊙_ : P → P → P
   unit : P
   
   assoc : ∀{a b c : P} → a ⊙ (b ⊙ c) ≡ (a ⊙ b) ⊙ c
   left-ident : ∀{a : P} → unit ⊙ a ≡ a
   right-ident : ∀{a : P} → a ⊙ unit ≡ a

   compatʳ : ∀{a b : P} → rel a b → (∀{c : P} → (rel (a ⊙ c) (b ⊙ c)))
   compatˡ : ∀{a b : P} → rel a b → (∀{c : P} → (rel (c ⊙ a) (c ⊙ b)))
open MonProset {{...}}

record Lineale {ℓ : Level} (L : Set ℓ) {{ _ : Proset L }} {{ _ : MonProset L}}: Set (lsuc ℓ) where
    constructor MkLineale
    infixl 20 _⊸_
    field
        _⊸_ : L → L → L
        
        rlcomp : {a b : L} → rel (a ⊙ (a ⊸ b)) b
        adj : {a b y : L} → rel (a ⊙ y) b → rel y (a ⊸ b)
open Lineale {{...}}


-- TODO: Helper lemmas

{- 
module _ {ℓ}{L : Set ℓ} 
  {{ _ : Proset L}}
  {{ _ : MonProset L }}
  {{ _ : Lineale L }} where 

{-
  lemma₁ : ∀{a b c : L} → c ⊙ b ⊙ a ≡ a ⊙ b ⊙ c 
  lemma₁ {a} {b} {c} = c ⊙ b ⊙ a ≡⟨ sym assoc ⟩ 
                       c ⊙ (b ⊙ a) ≡⟨ symm ⟩ 
                       (b ⊙ a) ⊙ c ≡⟨ cong (_⊙ c) symm ⟩ 
                       a ⊙ b ⊙ c ∎

  ex : ∀(a b c x : L) → rel(c ⊙ b ⊙ a) x ≡ rel (a ⊙ b ⊙ c) x
  ex a b c x = cong₂ rel lemma₁ refl 
-} 



  --ex₂ : ∀{a b c : L} → rel(( a ⊸ b) ⊙ a) b ≡ rel (a ⊙ (a ⊸ b)) b
  --ex₂  = cong₂ rel symm refl

  --relassocl : ∀{a b c : L} → rel (a ⊙ (b ⊙ c)) ((a ⊙ b) ⊙ c)
  --relassocl = transport (cong₂ rel (sym assoc) refl) prefl

  relidl : ∀{a x : L} → rel (unit ⊙ a) x → rel a x 
  relidl = transport (cong₂ rel left-ident refl)
  
  relassocl : ∀{a b c x : L} → rel (a ⊙ (b ⊙ c)) x → rel ((a ⊙ b) ⊙ c) x 
  relassocl = transport (cong₂ rel assoc refl)

  relassocl' : ∀{a b c x : L} → rel ((a ⊙ b) ⊙ c) x → rel (a ⊙ (b ⊙ c)) x 
  relassocl' = transport (cong₂ rel (sym assoc) refl)

{-
  relsyml : ∀{a b c : L} → rel (a ⊙ b) c → rel (b ⊙ a) c
  relsyml t = transport (cong₂ rel symm refl) t

  relsymr : ∀{a b c : L} → rel c (a ⊙ b) → rel c (b ⊙ a)
  relsymr t = transport (cong₂ rel refl symm ) t

  swap : ∀{a b : L} → rel (a ⊙ b) (b ⊙ a)
  swap = transport (cong₂ rel symm refl) prefl

  compat-sym : ∀{a b : L} → rel a b → (∀{c : L} → (rel (c ⊙ a) (c ⊙ b)))
  compat-sym {a} {b} t {c} = let acRbc = compat t {c} 
                                 caRbc = relsyml acRbc
                              in relsymr caRbc

  bifun : ∀(a b c d : L) → 
    rel a c → 
    rel b d → 
    rel (a ⊙ b) (c ⊙ d)
  bifun a b c d t1 t2 = let abRcb = compat t1 {b}
                            bcRdc = compat t2 {c} 
                            abRbc = ptrans abRcb swap
                            bcRcd = ptrans bcRdc swap 
                        in ptrans abRbc bcRcd

  ex₃ : ∀{a b c : L} → rel((a ⊸ b) ⊙ a) b → rel (a ⊙ (a ⊸ b)) b
  ex₃ = relsyml

  -- harder example
  --        adj : {a b y : L} → rel (a ⊙ y) b → rel y (a ⊸ b)
  ex₄ : ∀{a b c d x : L} → rel (c ⊙ a ⊙ unit ⊙ d ⊙ b) x → rel a (d ⊸ (c ⊸ (b ⊸ x)))
  ex₄ t = let aUNITd|c⊸b⊸x = adj (relassocl' (relassocl' (adj (relsyml t))))
          in adj (relidl (relassocl' (relsyml aUNITd|c⊸b⊸x)))
-}
 -}