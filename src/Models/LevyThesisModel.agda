{-# OPTIONS --safe --lossy-unification #-}

module src.Models.LevyThesisModel where
    open import Cubical.Foundations.Prelude
    open import Cubical.Foundations.HLevels hiding (extend)
    open import Cubical.Functions.Embedding

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
    
    {-
        This approach follows from Levy's thesis (section 7)

        𝒱 := Set^World  
        𝒞 := Set^(World ^op)

        An indirect way to get F : F∪nctor 𝒱 𝒞 and U : Functor 𝒞 𝒱 
        is to use the kan extension module twice and an equivalence of Set^|W| and Set^(|W| ^op)

        probably an easier way to get this adjunction between Set^World and Set^(World ^op)
        library doesn't have composition of adjucnctions
    -}
    module Cats {ℓS ℓC ℓC' : Level}(W : Category ℓC ℓC')(isSetWob : isSet (ob W)) where
        
        ℓ = (ℓ-max (ℓ-max ℓC ℓC') ℓS)

        |W| : Category ℓC ℓC 
        |W| = (DiscreteCategory (ob W , isSet→isGroupoid isSetWob))

        Inc : Functor |W| W
        Inc = DiscFunc λ x → x
            
        -- covariant
        𝒱 : Category (ℓ-suc ℓ) ℓ 
        𝒱 = PresheafCategory (W ^op) ℓ

        -- contravariant
        𝒞 : Category (ℓ-suc ℓ) ℓ 
        𝒞 = PresheafCategory W ℓ

        _×P_ : ob 𝒱 → ob 𝒱 → ob 𝒱
        (P ×P Q)  = PshProd ⟅ P , Q ⟆b

        -- functor C → D to a functor PresheafCategory C ℓ → PresheafCategory D ℓ
        module L = Ran ℓ (Inc ^opF)
            -- |W|^op -> W^op
            -- FUNCTOR |W| Set -> FUNCTOR W Set
        module R = Lan ℓ Inc
            -- |W| -> W 
            -- FUNCTOR |W|^op Set -> Functor W^op Set

        Inc* = precomposeF (SET ℓ) (Inc)
        Inc^op* = precomposeF (SET ℓ) (Inc ^opF)

        -- this nonsense, can be avoided
        module _ where 
            cast : {ℓC ℓC' : Level}{C : Category ℓC ℓC'} → Functor |W| C → Functor (|W| ^op) C 
            cast X .F-ob = X .F-ob
            cast X .F-hom f = X .F-hom (sym f)
            cast X .F-id = X .F-id
            cast X .F-seq f g = {! X .F-seq (sym f) (sym g)  !}

            cast' : {ℓC ℓC' : Level}{C : Category ℓC ℓC'} → Functor (|W| ^op) C → Functor |W| C 
            cast' X .F-ob = X .F-ob
            cast' X .F-hom f = X .F-hom (sym f)
            cast' X .F-id = X .F-id
            cast' X .F-seq f g = {! X .F-seq (sym f) (sym g)  !}

            castF : Functor (FUNCTOR |W| (SET ℓ)) (FUNCTOR (|W| ^op) (SET ℓ))
            castF .F-ob = cast
            castF .F-hom f = natTrans (λ x₁ x₂ → {! x₂  !}) {!   !}
            castF .F-id = {!   !}
            castF .F-seq = {!   !}

            castF' : Functor (FUNCTOR (|W| ^op) (SET ℓ)) (FUNCTOR |W| (SET ℓ))
            castF' .F-ob = cast'
            castF' .F-hom f = {!   !}
            castF' .F-id = {!   !}
            castF' .F-seq = {!   !}

        -- R.Lan is exists future 
        F : Functor 𝒱 𝒞 
        F = (R.Lan ∘F castF) ∘F Inc*

        -- L.Ran is forall future (technically forall past, but op fixes direction)
        U : Functor 𝒞 𝒱
        U = (L.Ran ∘F castF') ∘F Inc^op*  

        -- observe the action on objects R.Lan (exists future)
        module _ (G : ob (FUNCTOR (|W| ^op) (SET ℓ))) (w₁ w₂ w₃ : ob W) where 

            _ : (g : W [ w₁ , (Inc ⟅ w₂ ⟆) ] ) (f : |W| [ w₂ , w₃ ])(a : (G ⟅ w₃ ⟆) .fst) →
                (G R.≈ w₁) (w₃ , g ⋆⟨ W ⟩ (Inc ⟪ f ⟫) , a) (w₂ , g , (G ⟪ f ⟫) a)
            _ = R._≈_.shift {G}{w₁}{w₂}{w₃}

        -- and the action on objects of L.Ran (forall future)
        module _ (G : ob (FUNCTOR |W| (SET ℓ))) (w₁ : ob W) where

            _ : L.End G w₁
            _ = record { fun = m ; coh = λ{ {w₂} {w₃} f g → {!   !} } } where 

                m : (w₂ : ob |W|)(g : W ^op [ w₂ , w₁ ]) → G .F-ob w₂ .fst
                m = {!   !} 

    module Instantiate {ℓS : Level} where 
        open import src.Data.Worlds hiding (Inc)
        
        data SynTy' : Type ℓS where 
            u n b : SynTy'

        SynTyisSet : isSet SynTy' 
        SynTyisSet = {!  !}

        SynTy : hSet ℓS 
        SynTy = SynTy' , SynTyisSet

        -- W has forward top maps
        W = (World SynTy) ^op

        wset : isSet (ob W)
        wset = {!   !}

        open Cats {ℓS} W wset
        -- utilities
        module _ where 
            -- pattern syntax for ob World
            pattern _◂_ x z = (((x , _), _ ) , z) 
            pattern _◂_◂_ x y z = (((x , y), _ ) , z) 

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

        module _ where 
    
            tys : SynTy' → ob 𝒱
            tys b = Constant _ _ (Lift Bool , isOfHLevelLift 2 isSetBool)  
            tys u = Constant _ _ (Unit* , isOfHLevelLift 2 isSetUnit)  
            tys n = Constant _ _ (Lift ℕ , isOfHLevelLift 2 isSetℕ) 

            OSum : ob 𝒱
            OSum .F-ob (((X , Xfin) , tt* ) , w) = 
                (Σ[ x ∈ X ] ((tys (w x)) ⟅ (((X , Xfin) , _ ) , w) ⟆) .fst) , 
                isSetΣ (isFinSet→isSet Xfin) λ x → ((tys (w x)) ⟅ (((X , Xfin) , _ ) , w) ⟆) .snd
            OSum .F-hom f (x , elem) = f .fst .fst .fst x , {! elem  !}
            OSum .F-id = {!   !}
            OSum .F-seq = {!   !}
            
            Case : (ty : SynTy') → ob 𝒱
            Case ty .F-ob (X ◂ Xfin ◂ w) = (Σ[ σ ∈ X ] Lift ( w σ ≡ ty)) , {!   !}
            Case ty .F-hom 
                {(((X , Xfin) , tt* ) , w)}
                {(((Y , Yfin) , tt* ) , w')}
                (((f , femb), _) , Δ )  
                (x , wx≡ty ) 
                = f x , transport lemma wx≡ty where 

                    lemma : Lift (w x ≡ ty) ≡ Lift (w' (f x) ≡ ty)
                    lemma = cong Lift (cong ( _≡ ty ) {!  Δ !})
                    
            Case ty .F-id = {!   !}
            Case ty .F-seq = {!   !}

            Termᶜ : ob 𝒞 
            Termᶜ = Constant _ _ (Unit* , isOfHLevelLift 2 isSetUnit)
            
            Termᵛ : ob 𝒱
            Termᵛ = Constant _ _ (Unit* , isOfHLevelLift 2 isSetUnit)

            ret : {val : ob 𝒱} → 𝒱 [ val , (U ∘F F) ⟅ val ⟆ ]
            ret {val}= natTrans α {!   !} where 

                α : N-ob-Type val ((U ∘F F) ⟅ val ⟆)
                α w Vw = record { fun = fun' ; coh = coh' } where 
                
                    fun' : (w' : ob (|W| ^op)) → (W ^op) [ w' , w ]  →  (castF' ⟅ Inc^op* ⟅ F ⟅ val ⟆ ⟆ ⟆) .F-ob w' .fst
                    fun' w' f = q[ w' , (id W , val .F-hom f Vw) ] 

                    coh' : {w₁ w₂ : ob |W|}
                             (f : |W| [ w₂ ,  w₁ ] ) --w₂ ≡ w₁
                             (g : W [ w , w₂ ] ) → 
                             fun' w₁ (((Inc ^opF) ⟪ f ⟫) ⋆⟨ W ^op ⟩ g) ≡ ((castF' ⟅ Inc^op* ⟅ F ⟅ val ⟆ ⟆ ⟆) ⟪ f ⟫) (fun' w₂ g)
                    coh' f g = {! refl  !}
 
        -- denote terms
        module _ where 
        
            injSem : 𝒱 [ (Case b) ×P (tys b) , OSum ]
            injSem = natTrans α {!   !} where
            
                α : N-ob-Type (Case b ×P (tys b)) OSum
                α w ((x , lift wxisb), y) = x , transport eqty y where

                    eqty : (tys b ⟅ w ⟆) .fst ≡ (tys (w .snd x) ⟅ w ⟆) .fst
                    eqty = cong fst (cong₂ _⟅_⟆ (cong tys (sym wxisb)) refl) 

            newcase : (ty : SynTy') → 𝒞 [ Termᶜ , F ⟅ Case ty ⟆ ]
            newcase ty = natTrans α {!   !} where 

                w' : ob W → ob W
                w' = extend ty

                w→w' : (w : ob W) → W [ w , w' w ]
                w→w' w = (((inl , inlemb) , refl) , refl)

                Case_w : (w : ob W) →  Case ty .F-ob (w' w) .fst
                Case_w _ = (inr tt* , lift refl)

                α : N-ob-Type Termᶜ (F ⟅ Case ty ⟆)
                α w tt* = q[ w' w , w→w' w , Case_w w ] 

            -- simple match
            match : (ty : SynTy') → 𝒱 [ Case ty ×P OSum , tys ty ]
            match ty = natTrans {!   !} {!   !}  where 
                α : N-ob-Type (Case ty ×P OSum) (tys ty)
                α w ((σ , lift wσ≡ty) , (σ' , e∈ty)) = transport lemma e∈ty where 
                
                    assuming : σ ≡ σ'
                    assuming = {!   !}

                    lemma : (tys (w .snd σ') ⟅ w ⟆) .fst ≡ (tys ty ⟅ w ⟆) .fst
                    lemma = cong fst (cong₂ _⟅_⟆ (cong tys (snd w σ' ≡⟨ cong₂ _ refl assuming ⟩ snd w σ ≡⟨ wσ≡ty ⟩ ty ∎)) refl)
