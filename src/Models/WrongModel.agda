{-# OPTIONS --safe --lossy-unification #-}

module src.Models.WrongModel where
    open import Cubical.Foundations.Prelude
    open import Cubical.Foundations.HLevels hiding (extend)
    open import Cubical.Functions.Embedding

    open import Cubical.Categories.Adjoint.Monad
    open import Cubical.Categories.Bifunctor.Redundant
    open import Cubical.Categories.Category
    open import Cubical.Categories.Functor
    open import Cubical.Categories.Instances.Discrete
    open import Cubical.Categories.Instances.Functors
    open import Cubical.Categories.Instances.Sets   
    open import Cubical.Categories.Monad.Base
    open import Cubical.Categories.NaturalTransformation
    open import Cubical.Categories.Presheaf.Base
    open import Cubical.Categories.Presheaf.Constructions
    open import Cubical.Categories.Presheaf.KanExtension
    

    open import Cubical.Data.Bool 
    open import Cubical.Data.FinSet
    open import Cubical.Data.FinSet.Constructors
    open import Cubical.Data.Nat
    open import Cubical.Data.Sigma
    open import Cubical.Data.Sum
    open import Cubical.Data.Unit

    open import Cubical.HITs.SetQuotients renaming ([_] to q[_])

    open Category
    open Functor

    -- This model is "wrong" in that the left Kan extension given from the inclusion functor 
    -- yields a monad on Psh(|W|) instead of Psh(W)
    -- the following module has 𝒱 := Psh(|W|) ,  𝒞 := Psh(W)
    -- but we'd like 𝒱 := Psh(W) ,  𝒞 := Psh(|W|)
    
    -- Q: does having 𝒱 := Psh(|W|) trivialize the day convoluton structure?
    -- See Steven's day conv on Psh(|String|)
    -- I "think" that would be a good argument against this setup.. otherwise..?
    module Cats {ℓS ℓC ℓC' : Level}(W : Category ℓC ℓC')(isSetWob : isSet (ob W)) where
        ℓ = (ℓ-max (ℓ-max ℓC ℓC') ℓS)

        |W| : Category ℓC ℓC 
        |W| = (DiscreteCategory (ob W , isSet→isGroupoid isSetWob))
            
        𝒱 : Category  (ℓ-suc ℓ) ℓ 
        𝒱 = PresheafCategory |W| ℓ

        𝒞 : Category (ℓ-suc ℓ) ℓ 
        𝒞 = PresheafCategory W ℓ 
        
        _×P_ : ob 𝒱 → ob 𝒱 → ob 𝒱
        (P ×P Q)  = PshProd ⟅ P , Q ⟆b
        
        Inc : Functor |W| W
        Inc = DiscFunc λ x → x
        
        open Lan ℓ Inc
        
        F : Functor 𝒱 𝒞
        F = Lan 

        U : Functor 𝒞 𝒱 
        U = precomposeF (SET ℓ) (Inc ^opF)

        _ : Monad 𝒱 
        _ = U ∘F F , MonadFromAdjunction F U adj

    -- however, denotations of terms and types are much easier in this setting (compared to algebras)
    -- see denoted terms for newcase and injection
    module Instantiate {ℓS : Level} where 
        open import src.Data.Worlds

        data SynTy' : Type ℓS where 
            u n b : SynTy'

        SynTyisSet : isSet SynTy' 
        SynTyisSet = {!   !}

        SynTy : hSet ℓS 
        SynTy = SynTy' , SynTyisSet

        W =  World SynTy
        open Cats {ℓS} (W ^op) {!  !}

        -- utilities
        module _ where 
            -- pattern syntax for ob World
            pattern _◂_ x z = (((x , _), _ ) , z) 
            pattern _◂_◂_ x y z = (((x , y), _ ) , z) 
                    
            -- this is dumb, just so I can use DiscFun
            cast : {ℓC ℓC' : Level}{C : Category ℓC ℓC'} → Functor |W| C → Functor (|W| ^op) C 
            cast X .F-ob = X .F-ob
            cast X .F-hom f = X .F-hom (sym f)
            cast X .F-id = X .F-id
            cast X .F-seq f g = {! sym ?   !}

            UnitF : FinSet ℓS
            UnitF = Unit* , {! !}

            inlemb : {ℓ : Level}{A B : Type ℓ} → isEmbedding (inl {ℓ}{ℓ}{A}{B})
            inlemb = {!   !}
            
            inc : FinSet ℓS → FinSet ℓS
            inc X = ((X .fst ⊎ Unit*) , isFinSet⊎ X UnitF)

            inj : {X Y  : FinSet ℓS}(f : X .fst → Y .fst) → (inc X) .fst → (inc Y) .fst
            inj f (inl x) = inl (f x)
            inj f (inr x) = inr x

            extend' : {X : FinSet ℓS} → (f : X .fst → SynTy')(ty : SynTy') → ((inc X) .fst → SynTy')
            extend' f ty (inl x) = f x
            extend' f ty (inr tt*) = ty

            extend : (ty : SynTy') → ob |W| → ob |W|
            extend ty ((X , tt*) , w) = (inc X , tt*) , extend' {X} w ty

        -- denote types
        module _ where 
    
            tys : SynTy' → ob 𝒱
            tys b = cast (DiscFunc λ _ → Lift Bool , isOfHLevelLift 2 isSetBool)
            tys u = cast (DiscFunc λ _ → Unit* , isOfHLevelLift 2 isSetUnit)
            tys n = cast (DiscFunc λ _ → Lift ℕ , isOfHLevelLift 2 isSetℕ)

            OSum : ob 𝒱
            OSum = cast (DiscFunc λ{ (((X , Xfin) , tt* ) , w) → 
                (Σ[ x ∈ X ] ((tys (w x)) ⟅ (((X , Xfin) , _ ) , w) ⟆) .fst) , 
                isSetΣ (isFinSet→isSet Xfin) λ x → ((tys (w x)) ⟅ (((X , Xfin) , _ ) , w) ⟆) .snd })
                
            Case : (ty : SynTy') → ob 𝒱
            Case ty = cast (DiscFunc 
                            λ{ (X ◂ Xfin ◂ w) → (Σ[ σ ∈ X ] Lift ( w σ ≡ ty)) , 
                                                isSetΣ (isFinSet→isSet Xfin) λ σ → isOfHLevelLift 2 {!   !} })

            Termᵛ : ob 𝒞 
            Termᵛ .F-ob X = Unit* , isOfHLevelLift 2 isSetUnit
            Termᵛ .F-hom f x = x
            Termᵛ .F-id = refl
            Termᵛ .F-seq _ _ = refl 
 
        -- denote terms
        module _ where 
        
            injSem : 𝒱 [ (Case b) ×P (tys b) , OSum ]
            injSem = natTrans α {!   !} where
            
                α : N-ob-Type (Case b ×P (tys b)) OSum
                α w ((x , lift wxisb), y) = x , transport eqty y where

                    eqty : (tys b ⟅ w ⟆) .fst ≡ (tys (w .snd x) ⟅ w ⟆) .fst
                    eqty = cong fst (cong₂ _⟅_⟆ (cong tys (sym wxisb)) refl) 

            newcase : (ty : SynTy') → 𝒞 [ Termᵛ , F ⟅ Case ty ⟆ ]
            newcase ty = natTrans α {!   !} where 

                w' : ob W → ob W
                w' = extend ty

                w→w' : (w : ob W) → (W ^op) [ w , w' w ]
                w→w' w = (((inl , inlemb) , refl) , refl)

                Case_w : (w : ob W) →  Case ty .F-ob (w' w) .fst
                Case_w _ = (inr tt* , lift refl)

                α : N-ob-Type Termᵛ (F ⟅ Case ty ⟆)
                α w tt* = q[ w' w , w→w' w , Case_w w ] 

        
          