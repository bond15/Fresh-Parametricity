{-# OPTIONS --cubical --type-in-type  #-} -- type-in-type for the exponent object in Psh-𝒞.. yeah yeah ... it will dissapear 
open import CatLib 
open import Agda.Primitive 
open import Cubical.Foundations.Prelude hiding(comp)

module LearnPresheaf {o ℓ} (𝒞 : Category o ℓ) where 


    
    module power where
        open import Cubical.Data.Bool
        open Category

        -- MCP
        𝓟 : Set₀ → Set₀ 
        𝓟 X = X → Bool

        data ⊥ : Set₀ where
        data ⊤ : Set₀ where
            tt : ⊤


        _∈_ : {X : Set₀} → (× : X) → (s : 𝓟 X) → Set₀
        x ∈ s with s x 
        x ∈ s     | true = ⊤
        x ∈ s     | false = ⊥


        _⊆_ : {X : Set₀} → 𝓟 X → 𝓟 X → Set₀
        X ⊆ Y = ∀ {x} → x ∈ X → x ∈ Y


        data W : Set₀ where 
            w1 w2 w3 w4 w5 : W

        _=?_ : W → W → Bool 
        w1 =? w1 = true
        w2 =? w2 = true
        w3 =? w3 = true
        w4 =? w4 = true
        w5 =? w5 = true
        _ =? _ = false

        singleton : W → 𝓟 W 
        singleton x = x =?_

        World : Category ℓ-zero ℓ-zero 
        World .Ob = 𝓟 W   
        World ._⇒_ X Y = X ⊆ Y
        World .id x = x
        World ._∘_ f g z = f (g z)
        World .idr {f} = refl
        World .idl {f} = refl
        World .assoc {f = f} {g} {h}= refl 

        module WorldExample where

            S₁ : 𝓟 W
            S₁ w2 = true
            S₁ w3 = true
            S₁ _  = false
        
            S₂ : 𝓟 W
            S₂ w2 = true
            S₂ w3 = true
            S₂ w4 = true
            S₂ _  = false

            ex₁ : S₁ ⊆ S₂ 
            ex₁ {w2} tt = tt
            ex₁ {w3} tt = tt

            -- no : S₂ ⊆ S₁ 
            -- no {w2} s = tt
            -- no {w3} s = tt
            -- no {w4} s = {!   !} -- impossible


    module Psh {o ℓ} (𝒞 : Category o ℓ)  where
        open Category
        open SetCat hiding (Sets)


        Psh-𝒞 : Category (ℓ-max o (ℓ-suc ℓ)) (o ⊔ ℓ) 
        Psh-𝒞 .Ob = Functor.FunctorT (𝒞 ^op) (ℓSets {ℓ})
            -- Objects are functors from 𝒞 ^op to Set
        Psh-𝒞 ._⇒_ F G = F ⇛ G
            -- Morphisms are natural transformations 
        Psh-𝒞 .id {x = P} = 
            Mknt 
                (λ o → id ℓSets ) 
                -- The component of the natural transformation is the identity morphism in Set
                (λ X Y f → refl)
                -- The commuting diagram trivially becomes P(f) = P(f)
        (Psh-𝒞 ._∘_ {x = F} {y = G} {z = H} M N) = 
            (Mknt α commutes ) where 
                α₁ : (x : Ob (𝒞 ^op)) → (ℓSets ⇒ Functor.FunctorT.F₀ F x) (Functor.FunctorT.F₀ G x)
                α₁ = _⇛_.η N
                -- F₀(x) → G₀(x)

                α₂ : (x : Ob 𝒞) → (ℓSets ⇒ Functor.FunctorT.F₀ G x) (Functor.FunctorT.F₀ H x)
                α₂ = _⇛_.η M
                -- G₀(x) → H₀(x)

                -- simply compose
                α : (x : Ob 𝒞) → (ℓSets ⇒ Functor.FunctorT.F₀ F x) (Functor.FunctorT.F₀ H x)
                α o = comp (α₂ o) (α₁ o)

                sq₁ = _⇛_.is-natural N -- top square
                sq₂ = _⇛_.is-natural M -- bottom square

                -- this holds because the two squares hold
                open import Cubical.Foundations.Prelude hiding (comp)

                F₁ = Functor.FunctorT.F₁ F
                G₁ = Functor.FunctorT.F₁ G
                H₁ = Functor.FunctorT.F₁ H

                commutes : 
                    (x y : Ob (𝒞 ^op)) 
                    (f : ((𝒞 ^op) ⇒ x) y) →
                        comp (α y) (F₁ f) ≡ comp (H₁ f) (α x)
                commutes x y f =  
                        comp (α y) (F₁ f)                   ≡⟨ refl ⟩ 
                        comp (comp (α₂ y) (α₁ y)) (F₁ f)    ≡⟨ sym (ℓSets .assoc {f = (α₂ y)} {g = (α₁ y)} {h = (F₁ f)}) ⟩        
                        comp (α₂ y) (comp (α₁ y) (F₁ f))    ≡⟨ (post {h = α₂ y} (sq₁ x y f)) ⟩
                        comp (α₂ y) (comp (G₁ f) (α₁ x))    ≡⟨ ℓSets .assoc {f = (α₂ y)} {g = G₁ f} ⟩ 
                        comp (comp (α₂ y) (G₁ f) ) (α₁ x)   ≡⟨ pre (sq₂ x y f) ⟩ 
                        comp (comp (H₁ f) (α₂ x) ) (α₁ x)   ≡⟨ sym (ℓSets .assoc {f = H₁ f} {g = α₂ x})  ⟩ 
                        comp (H₁ f) (comp (α₂ x) ((α₁ x)))  ≡⟨ refl ⟩ 
                        comp (H₁ f) (α x) ∎


        Psh-𝒞 .idr {x = F} {y = G} = Nat-path (λ o → refl) where --the componets are trivially the same (idₓ ∘ αₓ ≡ αₓ)
            open NP F G
  
        Psh-𝒞 .idl {x = F} {y = G} = Nat-path (λ o → refl) where --the componets are trivially the same (αₓ ∘ idₓ ≡ αₓ)
            open NP F G
        Psh-𝒞 .assoc {w = F} {z = G}= Nat-path λ o → refl where  -- the components are trivially associative (just associatity of functions in Set)
            open NP F G



        -- See Notability 1-25-24
        module Yoneda where
            open Functor
            open FunctorT 
            open HomFunctors

            open Category 𝒞 renaming (Ob to Cob; _⇒_ to _⇒c_ ; _∘_ to _∘c_ ; id to cId ; assoc to Cassoc ; idl to  cidl)
            open Category Psh-𝒞 renaming (Ob to psh; _⇒_ to _⇒psh_)
            open Category (ℓSets {ℓ}) renaming (Ob to set; _⇒_ to _⇒s_ ; _∘_ to _∘s_)

            𝓨₀ : Ob 𝒞 → Ob Psh-𝒞
            𝓨₀ = Hom[-,_]

            𝓨₁ : {X Y : Ob 𝒞} → (f : X ⇒c Y) → 𝓨₀ X ⇒psh 𝓨₀ Y
            𝓨₁ {X} {Y} f = Mknt (λ Z → f ∘c_) λ A B g → funExt λ h → Cassoc

            -- MCY 
            -- Yonedda embedding
            𝓨 : FunctorT 𝒞 Psh-𝒞 
            𝓨 .F₀ = 𝓨₀ 
            𝓨 .F₁ = 𝓨₁
            𝓨 .Fid = Nat-path _ _ λ o → funExt λ g → cidl where open NP
            𝓨 .Fcomp = Nat-path _ _ λ o → funExt λ h → sym Cassoc where open NP

        module Psh× where 
            open BinaryProducts Psh-𝒞 
            open BinaryProductsT hiding (_×_)
            open ObjectProduct Psh-𝒞
            open Product
            open import Cubical.Data.Prod
            open Functor 

            psh× : {A B : Ob (𝒞 ^op)}{F G : FunctorT (𝒞 ^op) ℓSets} → 
                ((𝒞 ^op) ⇒ A) B → ((FunctorT.F₀ F A) × (FunctorT.F₀ G A)) → ((FunctorT.F₀ F B) × (FunctorT.F₀ G B))
            psh× {F = F} {G} f (FA , GA) = F₁ f FA , G₁ f GA where 
                open Functor.FunctorT G renaming (F₀ to G₀ ; F₁ to G₁)
                open Functor.FunctorT F 
            
            Psh-prod : BinaryProductsT
            Psh-prod .product {F} {G} .A×B = p where


                open Functor.FunctorT G renaming (F₀ to G₀ ; F₁ to G₁)
                open Functor.FunctorT F 
                open Category 𝒞 renaming (Ob to Cob ; id to cId ; _⇒_ to _⇒c_ ; _∘_ to _∘c_)
                
                m : {A B : Ob (𝒞 ^op)} → ((𝒞 ^op) ⇒ A) B → ((F₀ A) × (G₀ A)) → ((F₀ B) × (G₀ B))
                m f (FA , GA) = F₁ f FA , G₁ f GA

                p : Functor.FunctorT (𝒞 ^op) ℓSets
                p .FunctorT.F₀ c = (F₀ c) × (G₀ c)
                p .FunctorT.F₁ f pair = psh× {F = F} {G = G} f pair 
                p .FunctorT.Fid = funExt λ {(Fa , Ga) →  
                    (F₁ cId Fa , G₁ cId Ga) ≡⟨ cong₂ _,_ (funExt⁻ (F .Fid) Fa) (funExt⁻ (G .Fid) Ga) ⟩ 
                    (Fa , Ga) ∎ }  
                p .FunctorT.Fcomp {f = f} {g = g} = funExt λ {(Fa , Ga) → --(F₁ (f ∘ g) Fa , G₁ (f ∘ g) Ga) ≡ (F₁ g (F₁ f Fa) , G₁ g (G₁ f Ga))
                    ((F₁ (f ∘c g) Fa , G₁ (f ∘c g) Ga)) ≡⟨ cong₂ _,_ (funExt⁻ (F .Fcomp {f = f} {g = g}) Fa) ((funExt⁻ (G .Fcomp {f = f} {g = g}) Ga)) ⟩ 
                    (F₁ g (F₁ f Fa) , G₁ g (G₁ f Ga)) ∎   }


            Psh-prod .product {A} {B} .π₁ = Mknt (λ o → λ {(x , _ ) → x}) λ x y f → funExt λ {(x , _) → refl}
            Psh-prod .product {A} {B} .π₂ = Mknt (λ o → λ {( _ , y ) → y}) λ x y f → funExt λ {( _ , y ) → refl}
            Psh-prod .product {A} {B} .⟨_,_⟩ = λ f g → Mknt (λ o → {!   !}) {!   !}
            Psh-prod .product {A} {B} .project₁ = {!   !}
            Psh-prod .product {A} {B} .project₂ = {!   !}
            Psh-prod .product {A} {B} .unique = {!   !}

        module Psh^ where 
            open Functor
            open FunctorT
            open HomFunctors
            open Yoneda

            open Psh× 
            open BinaryProducts
            open BinaryProductsT Psh-prod renaming (_×_ to _×psh_)
            open import Cubical.Data.Prod  using (_×_ ; _,_)
            open Category 𝒞 renaming (Ob to Cob ; _⇒_ to _⇒c_ ; _∘_ to _∘c_)
            open Category Psh-𝒞 renaming (Ob to psh ; _⇒_ to _⇒p_ ; _∘_ to _∘p_)
            open Category ℓSets renaming (Ob to set ; _⇒_ to _⇒s_ ; _∘_ to _∘s_)
            
            -- TODO: type-in-type violation here
            Psh-𝒞^ : (A B : Ob Psh-𝒞) → Ob Psh-𝒞
            Psh-𝒞^ A B .F₀ c = (𝓨₀ c ×psh A) ⇛ B
            Psh-𝒞^ A B .F₁ {X} {Y} = fmap where 
                fmap : (f : Y ⇒c X) → ((𝓨₀ X ×psh A) ⇛ B) → ((𝓨₀ Y ×psh A) ⇛ B)
                fmap f nt = Mknt η₃ is-natural₃ where 

                    open FunctorT A renaming (F₀ to A₀ ; F₁ to A₁)
                    open FunctorT B renaming (F₀ to B₀ ; F₁ to B₁)
                    open _⇛_ nt renaming (η to η₁ ; is-natural to is-natural₁) 
                    open _⇛_ (𝓨₁ f) renaming (η to η₂ ; is-natural to is-natural₂)

                    _ : (Z : Cob) → ((Z ⇒c X) × A₀ Z) ⇒s (B₀ Z)
                    _ = η₁

                    _ : (V : Cob) → (V ⇒c Y) → (V ⇒c X)
                    _ = η₂ 

                    η₃ : (Z : Cob) → ((Z ⇒c Y) × A₀ Z) ⇒s (B₀ Z)
                    η₃ Z (z→y , Az) = η₁ Z (η₂ Z z→y , Az) 

                    -- square
                    open NP
                    -- x₁ : (V ⇒c Y) × A₀ V
                    is-natural₃ : (V W : Cob) → (g : W ⇒c V) →  
                        (λ x₁ → η₃ W (psh× g x₁)) ≡ (λ x₁ → B₁ g (η₃ V x₁))
                    is-natural₃ = {!   !}

                
            Psh-𝒞^ A B .Fid = {!   !}
            Psh-𝒞^ A B .Fcomp = {!   !}

        -- the category of presheaves on 𝒞 is cartesian closed

        open CartesianClosed Psh-𝒞
        open CartesianClosedT

        open BinaryProducts Psh-𝒞 
        open BinaryProductsT hiding (_×_)

        open Terminal Psh-𝒞
        open TerminalT

        open Exponentials Psh-𝒞
        open ExponentialsT

        open ObjectProduct Psh-𝒞
        open Product

        open Functor
        --open FunctorT

        open import Cubical.Data.Prod
        Psh-prod : BinaryProductsT
        Psh-prod .product {F} {G} .A×B = p where

            open Functor.FunctorT G renaming (F₀ to G₀ ; F₁ to G₁)
            open Functor.FunctorT F 
            
            m : {A B : Ob (𝒞 ^op)} → ((𝒞 ^op) ⇒ A) B → ((F₀ A) × (G₀ A)) → ((F₀ B) × (G₀ B))
            m f (FA , GA) = F₁ f FA , G₁ f GA

            p : Functor.FunctorT (𝒞 ^op) ℓSets
            p .FunctorT.F₀ c = (F₀ c) × (G₀ c) 
            p .FunctorT.F₁ = m 
            p .FunctorT.Fid = {!   !} 
            p .FunctorT.Fcomp = {!   !}

        Psh-prod .product {A} {B} .π₁ = {!   !}
        Psh-prod .product {A} {B} .π₂ = {!   !}
        Psh-prod .product {A} {B} .⟨_,_⟩ = {!   !}
        Psh-prod .product {A} {B} .project₁ = {!   !}
        Psh-prod .product {A} {B} .project₂ = {!   !}
        Psh-prod .product {A} {B} .unique = {!   !}


        open Functor.FunctorT 
        
       -- term : Ob Psh-𝒞 
       -- term .F₀ Cob  = Terminal.TerminalT.⊤ set-term
       -- term .F₁ f = λ x → x
       -- term .Fid {F} = refl
       -- term .Fcomp = refl

    {- 
        Psh-term : TerminalT
        Psh-term .⊤ = term
        Psh-term .⊤-is-terminal = record { ! = ! ; !-unique = uniq } where
                    ! : {A : FunctorT (𝒞 ^op) ℓSets} → A ⇛ term
                    ! = Mknt (λ X → λ _ → tt) λ X Y f → refl

                    uniq : {F : FunctorT (𝒞 ^op) ℓSets} (f : F ⇛ term) → ! ≡ f 
                    uniq {F} nt = Nat-path λ Cob → funExt λ x → unit-is-prop tt (_⇛_.η nt Cob x)  
                                    where open NP F term
    -}

        Psh-exp : ExponentialsT
        Psh-exp = record { 
            exponential = 
                record { 
                    B^A = {!   !} ; 
                    product = {!   !} ; 
                    eval = {!   !} ; 
                    λg = {!   !} 
                } 
            }
        
        -- https://rak.ac/blog/2016-08-24-presheaf-categories-are-cartesian-closed/
        --CCC-Psh-𝒞 : CartesianClosedT 
        --CCC-Psh-𝒞 .terminal = Psh-term
        --CCC-Psh-𝒞 .products = Psh-prod
        --CCC-Psh-𝒞 .exponentials = Psh-exp


        -- yoneda embedding
        -- Mcy
        𝓎 : FunctorT 𝒞 Psh-𝒞
        𝓎 .F₀ = 𝓎₀ where 
            𝓎₀ : Ob 𝒞 → Ob Psh-𝒞
            𝓎₀ c .F₀ c' = {! (_⇒_ 𝒞) c' c  !}
            𝓎₀ c .F₁ = {!   !}
            𝓎₀ c .Fid = {!   !}
            𝓎₀ c .Fcomp = {!   !}
        𝓎 .F₁ = {!   !}
        𝓎 .Fid = {!   !}
        𝓎 .Fcomp = {!   !}

        -- also need hom functor
        --https://ncatlab.org/nlab/show/closed+monoidal+structure+on+presheaves
        -- https://github.com/agda/agda-categories/blob/9ece1e0b86b0bf5092ef1a0b74dadcb90810b936/src/Categories/Category/Construction/Properties/Presheaves/CartesianClosed.agda
        -- https://github.com/agda/agda-categories/blob/9ece1e0b86b0bf5092ef1a0b74dadcb90810b936/src/Categories/Functor/Hom.agda


    module Syntax where 

        data VType : Set₀ 
        data CType : Set₀

        data VType where 
            One : VType 
            _×ty_ _*_ : VType → VType → VType
            U : CType → VType
        
        data CType where 
            -- \-->
            _⟶_ _-*_ : VType → CType → CType
            F : VType → CType


        data Trm : Set₀ where 
            
        
            
    module Semantics where
        open Category
        open power using (World)
        open Psh World
        open Syntax

    
        Psh-World : Category  {!   !} {!   !} 
        Psh-World = Psh-𝒞

       -- open ObjectProduct
        open BinaryProducts Psh-World
        open BinaryProductsT

        ⦅_⦆val : VType → Psh-World .Ob
        ⦅_⦆cmp : CType → {!   !} 
        
        ⦅ One ⦆val = {!   !} -- term
        ⦅ T ×ty T₁ ⦆val = _×_ Psh-prod ⦅ T ⦆val ⦅ T₁ ⦆val 
        ⦅ T * T₁ ⦆val = {!   !} -- Day convolution?
        ⦅ U T ⦆val = ⦅ T ⦆cmp

        ⦅_⦆cmp = {!   !}        
    