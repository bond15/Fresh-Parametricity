{-# OPTIONS --cubical #-}
open import CatLib 
open import Agda.Primitive 
module LearnPresheaf {o ℓ} (𝒞 : Category o ℓ) where 

    open Category        
    open import Cubical.Foundations.Prelude hiding(comp)

    comp : {A B C : Set₀} → (B → C) → (A → B) → A → C 
    comp g f x = g (f x)

    pre : {A B C : Set₀}{g h : B → C}{f : A → B} → (p : g ≡ h) → 
        comp g f ≡ comp h f
    pre p = cong₂ comp p  refl
    
    post : {A B C : Set₀}{h : B → C}{f g : A → B} → (p : f ≡ g) → 
        comp h f ≡ comp h g
    post p = {!   !}
    
    Sets : Category (lsuc lzero) (lzero)
    Sets .Ob = Set₀
    Sets ._⇒_ X Y = X → Y
    Sets .id x = x
    Sets ._∘_ = comp
    Sets .idr = refl
    Sets .idl = refl
    Sets .assoc = refl


    


    module _ {o ℓ} (𝒞 : Category o ℓ)  where

        Psh-𝒞 : Category (lsuc lzero ⊔ o ⊔ ℓ) (o ⊔ ℓ) 
        Psh-𝒞 .Ob = Functor.FunctorT (𝒞 ^op) Sets
            -- Objects are functors from 𝒞 ^op to Set
        Psh-𝒞 ._⇒_ F G = F ⇛ G
            -- Morphisms are natural transformations 
        Psh-𝒞 .id {x = P} = 
            Mknt 
                (λ o → id Sets ) 
                -- The component of the natural transformation is the identity morphism in Set
                (λ X Y f → refl)
                -- The commuting diagram trivially becomes P(f) = P(f)
        (Psh-𝒞 ._∘_ {x = F} {y = G} {z = H} M N) = 
            (Mknt α commutes ) where 
                α₁ : (x : Ob (𝒞 ^op)) → (Sets ⇒ Functor.FunctorT.F₀ F x) (Functor.FunctorT.F₀ G x)
                α₁ = _⇛_.η N
                -- F₀(x) → G₀(x)

                α₂ : (x : Ob 𝒞) → (Sets ⇒ Functor.FunctorT.F₀ G x) (Functor.FunctorT.F₀ H x)
                α₂ = _⇛_.η M
                -- G₀(x) → H₀(x)

                -- simply compose
                α : (x : Ob 𝒞) → (Sets ⇒ Functor.FunctorT.F₀ F x) (Functor.FunctorT.F₀ H x)
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
                        comp (comp (α₂ y) (α₁ y)) (F₁ f)    ≡⟨ sym (Sets .assoc {f = (α₂ y)} {g = (α₁ y)} {h = (F₁ f)}) ⟩        
                        comp (α₂ y) (comp (α₁ y) (F₁ f))    ≡⟨ (post {h = α₂ y} (sq₁ x y f)) ⟩
                        comp (α₂ y) (comp (G₁ f) (α₁ x))    ≡⟨ Sets .assoc {f = (α₂ y)} {g = G₁ f} ⟩ 
                        comp (comp (α₂ y) (G₁ f) ) (α₁ x)   ≡⟨ pre (sq₂ x y f) ⟩ 
                        comp (comp (H₁ f) (α₂ x) ) (α₁ x)   ≡⟨ sym (Sets .assoc {f = H₁ f} {g = α₂ x})  ⟩ 
                        comp (H₁ f) (comp (α₂ x) ((α₁ x)))  ≡⟨ refl ⟩ 
                        comp (H₁ f) (α x) ∎


        Psh-𝒞 .idr {x = F} {y = G} = Nat-path (λ o → refl) where --the componets are trivially the same (idₓ ∘ αₓ ≡ αₓ)
            open NP F G
  
        Psh-𝒞 .idl {x = F} {y = G} = Nat-path (λ o → refl) where --the componets are trivially the same (αₓ ∘ idₓ ≡ αₓ)
            open NP F G
        Psh-𝒞 .assoc {w = F} {z = G}= Nat-path λ o → refl where  -- the components are trivially associative (just associatity of functions in Set)
            open NP F G


        -- the category of presheaves on 𝒞 is cartesian closed

        open CartesianClosed Psh-𝒞
        open CartesianClosedT

        open BinaryProducts Psh-𝒞 
        open BinaryProductsT hiding (_×_)

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

            p : Functor.FunctorT (𝒞 ^op) Sets
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
        
        -- https://rak.ac/blog/2016-08-24-presheaf-categories-are-cartesian-closed/
        CCC-Psh-𝒞 : CartesianClosedT 
        CCC-Psh-𝒞 .terminal = {!   !}
        CCC-Psh-𝒞 .products = {!   !}
        CCC-Psh-𝒞 .exponentials = {!   !}


    