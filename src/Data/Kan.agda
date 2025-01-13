module src.Data.Kan where
    open import Cubical.Categories.Presheaf.KanExtension
    open import Cubical.Foundations.Function
    open import Cubical.Foundations.Prelude
    open import Cubical.Foundations.HLevels hiding (extend)
    open import Cubical.Functions.Embedding
    open import Cubical.Functions.FunExtEquiv

    open import Cubical.Categories.Adjoint
    open import Cubical.Categories.Adjoint.Monad
    open import Cubical.Categories.Bifunctor.Redundant
    open import Cubical.Categories.Category 
    open import Cubical.Categories.Functor
    open import Cubical.Categories.Functors.Constant
    open import Cubical.Categories.Instances.Discrete
    open import Cubical.Categories.Instances.Functors
    open import Cubical.Categories.Instances.Sets 
    open import Cubical.Categories.Monad.Base
    open import Cubical.Categories.NaturalTransformation
    open import Cubical.Categories.Presheaf.Base
    open import Cubical.Categories.Presheaf.Constructions
    open import Cubical.Foundations.Isomorphism
    open import Cubical.Categories.Equivalence
    open import Cubical.HITs.PropositionalTruncation
    module _ {ℓ : Level}(G : hGroupoid ℓ) where

        C : Category _ _ 
        C = DiscreteCategory G 
        open Functor

        F : Functor C (C ^op)
        F .F-ob c = c
        F .F-hom f = sym f
        F .F-id = refl
        F .F-seq {x}{y}{z} f g = goal where 
            _ : x ≡ y 
            _ = f

            _ : y ≡ z 
            _ = g

            goal : sym (f ∙ g) ≡ (sym g) ∙ (sym f)
            goal = {! doubleCompPath-filler ? ? ? !}

        F' : Functor (C ^op) C 
        F' .F-ob c = c
        F' .F-hom f = sym f
        F' .F-id = refl
        F' .F-seq {x}{y}{z} f g = goal where 
            goal : sym (g ∙ f) ≡ (sym f) ∙ (sym g)
            goal = {!    !}

        lemma : C ≃ᶜ (C ^op) 
        lemma = equivᶜ F 
                ∣ record { 
                        invFunc = F' ;
                        η = record { 
                            trans = natTrans (λ x → refl) λ f → {!  !} ; 
                            nIso = λ x → isiso refl {! refl  !} {! refl  !} } ; 
                        ε = record { 
                            trans = natTrans (λ x → refl) λ f → {!   !} ; 
                            nIso = λ x → isiso refl {!   !} {!   !} } }  ∣₁

        𝓒 : Category _ _ 
        𝓒 = PresheafCategory C ℓ

        𝓓 : Category _ _ 
        𝓓 = PresheafCategory (C ^op) ℓ




        theorem : 𝓒 ≃ᶜ 𝓓 
        theorem = equivᶜ {!   !} {!   !}