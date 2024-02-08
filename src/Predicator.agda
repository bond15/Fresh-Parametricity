{-# OPTIONS --cubical --type-in-type #-} 
open import CatLib
open import Agda.Primitive 
open import Cubical.Foundations.Prelude 
open import Cubical.Foundations.Isomorphism

module Predicator{o ℓ} (𝒞 : Category o ℓ) where

    open Category 𝒞
    record Pred : Set ((lsuc o) ⊔ ℓ) where 
        field 
            P⟨_⟩ : Ob → Set o
            _*_ : ∀{A B : Ob} → P⟨ B ⟩ → (A ⇒ B) → P⟨ A ⟩

            *id : ∀ {A : Ob}(φ : P⟨ A ⟩) → φ * id ≡ φ 
            *cmp : ∀{A B C : Ob}(φ : P⟨ C ⟩)(f : A ⇒ B)(g : B ⇒ C) → φ * (g ∘ f) ≡ ((φ * g) * f)

    
    open import Cubical.Data.Prod
    prod : (a b : Ob) → Pred 
    prod a b = record { 
            P⟨_⟩ = λ c → (c ⇒ a) × (c ⇒ b) ;
            _*_ = λ{ {x} {y} (π₁' , π₂') h → ((π₁' ∘  h) , π₂' ∘ h)} ; 
            *id = {!   !} ; 
            *cmp = {!   !} }

    module isPresheaf where 
        open import LearnPresheaf 𝒞 
        open SetCat
        open Functor

        -- Predicator IS a Presheaf
        same : Iso Pred (FunctorT (𝒞 ^op) (ℓSets {o}))
        same = iso pred→psh psh→pred s r where 

            pred→psh : (x : Pred) → FunctorT (𝒞 ^op) ℓSets
            pred→psh record { P⟨_⟩ = P⟨_⟩ ; _*_ = _*_ ; *id = *id ; *cmp = *cmp } = 
                     record { F₀ = P⟨_⟩ ; F₁ = λ {A} {B} f x → x * f ; Fid = λ{X} → funExt λ φ → *id {X} φ ; Fcomp = λ {X}{Y}{Z}{f}{g} → funExt λ φ → *cmp φ g f }

            psh→pred : (x : FunctorT (𝒞 ^op) ℓSets) → Pred
            psh→pred record { F₀ = F₀ ; F₁ = F₁ ; Fid = Fid ; Fcomp = Fcomp } = 
                     record { P⟨_⟩ = F₀ ; _*_ = λ FB f → F₁ f FB ; *id = λ {A} φ → funExt⁻ Fid φ ; *cmp = λ φ f g → funExt⁻ Fcomp φ }

        
            s : (x : FunctorT (𝒞 ^op) ℓSets) → pred→psh (psh→pred x) ≡ x
            s x = refl

            r : (x : Pred) → psh→pred (pred→psh x) ≡ x
            r x = refl

    open Functor
    open SetCat
    module yonedaLemma (P : (Functor.FunctorT (𝒞 ^op) (ℓSets {o}))) where 
        import LearnPresheaf
        module lp =  LearnPresheaf 𝒞 
        open lp.Psh 
        open Yoneda 𝒞
        open HomFunctors
        open isPresheaf
        open Cubical.Foundations.Isomorphism.Iso 

        open FunctorT P renaming (F₀ to P₀ ; F₁ to P₁)
        yoneda-lemma : ∀ (A : Ob) → Iso (P₀ A) (𝓨₀ A ⇛ P) 
        yoneda-lemma A = iso to fro {!   !} {!   !} where 

            to : P₀ A → Hom[-, A ] ⇛ P 
            to φ = Mknt η sq where 


                pred : Pred 
                pred = inv same P
                
                open Pred pred

                η : (x : Ob) → x ⇒ A → P₀ x
                η x f = φ * f

                sq : (x y : Ob) (f : y ⇒ x) → (λ g → P₁ (g ∘ f) φ) ≡ (λ g → P₁ f (P₁ g φ)) 
                sq x y f = funExt λ g → {! *cmp  !}

                
            fro : Hom[-, A ] ⇛ P → P₀ A
            fro nt = η A id where 
                open _⇛_ nt
 