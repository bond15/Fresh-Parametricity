{-# OPTIONS --safe --lossy-unification #-}
module src.Models.AlgebraModel where
    open import Cubical.Foundations.Prelude
    open import Cubical.Foundations.HLevels 

    open import Cubical.Categories.Adjoint.Monad
    open import Cubical.Categories.Category
    open import Cubical.Categories.Functor
    open import Cubical.Categories.Instances.EilenbergMoore
    open import Cubical.Categories.Instances.Functors
    open import Cubical.Categories.Instances.Sets   
    open import Cubical.Categories.Monad.Base
    open import Cubical.Categories.Presheaf.KanExtension

    open import Cubical.Data.FinSet

    module Instance1 where 
        -- Monad on FUNCTOR (W ^op) (SET ℓ) given by 
        -- the left kan extension of precomposition with the identity functor
        module CBPV {ℓS ℓC ℓC' : Level}(W : Category ℓC ℓC') where

            ℓ = (ℓ-max (ℓ-max ℓC ℓC') ℓS)
            
            𝒱 : Category  (ℓ-suc ℓ) ℓ 
            𝒱 = FUNCTOR (W ^op) (SET ℓ)

            open Lan ℓ 𝟙⟨ W ⟩ 
            
            T : Functor 𝒱 𝒱 
            T = Lan 

            F* : Functor 𝒱 𝒱 
            F* = precomposeF (SET ℓ) (𝟙⟨ W ⟩ ^opF)

            Eff : Monad 𝒱 
            Eff = F* ∘F T , MonadFromAdjunction T F* adj

            𝒞 : Category (ℓ-suc ℓ) ℓ 
            𝒞 = EMCategory Eff

        module Initialize {ℓS : Level} where 
            open Category
            open Functor
            open import Cubical.Categories.Instances.FunctorAlgebras
            open import Cubical.Categories.NaturalTransformation
            open import Cubical.Categories.Functors.Constant
            open import Cubical.HITs.SetQuotients renaming ([_] to q[_])
            open import src.Data.Worlds 
            open import Cubical.Data.Bool 
            open import Cubical.Data.Unit 
            open import Cubical.Data.Nat
            
            -- a dummy syntactic type
            -- codes for unit bool nat
            data SynTy' : Type ℓS where 
                u n b : SynTy'
                
            -- what is the easiest way to do this
            SynTyisSet : isSet SynTy'
            SynTyisSet = {!   !}
  
            SynTy : hSet ℓS   
            SynTy = SynTy' , SynTyisSet


            W = World SynTy 
            open CBPV {ℓS} W

            -- an interpretation of syntactic types
            tys : SynTy' → ob 𝒱
            tys b = Constant _ _ (Lift Bool , isOfHLevelLift 2 isSetBool)  
            tys u = Constant _ _ (Unit* , isOfHLevelLift 2 isSetUnit)  
            tys n = Constant _ _ (Lift ℕ , isOfHLevelLift 2 isSetℕ) 

            term : ob 𝒱 
            term .F-ob _ = Unit* , isSetUnit*
            term .F-hom f x = x
            term .F-id = refl
            term .F-seq f g = refl
            
            Case : (ty : SynTy') → ob 𝒱 
            Case ty .F-ob (((X , Xfin) , _ ) , w) = (Σ[ σ ∈ X ] Lift (w σ ≡ ty)) , {!   !}
            Case ty .F-hom f x = {!   !}
            Case ty .F-id = {!   !}
            Case ty .F-seq = {!   !}

            -- pattern matching on the HIT 
            newcase : (ty : SynTy') → 𝒞 [ freeEMAlgebra Eff term , freeEMAlgebra Eff (Case ty) ] 
            newcase ty = algebraHom (natTrans (λ{ x y → q[ {!   !} , {!   !} , {!   !} ]}) {!   !}) {!   !}
