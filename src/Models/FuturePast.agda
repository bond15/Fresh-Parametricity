{-# OPTIONS --allow-unsolved-metas  --lossy-unification #-}

module src.Models.FuturePast where
    open import Cubical.Foundations.Prelude
    open import Cubical.Foundations.HLevels hiding (extend)
    open import Cubical.Functions.Embedding

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

    module Cats {ℓS ℓC ℓC' : Level}(W : Category ℓC ℓC')(isSetWob : isSet (ob W)) where
        ℓ = (ℓ-max (ℓ-max ℓC ℓC') ℓS)


        |W| : Category ℓC ℓC 
        |W| = (DiscreteCategory (ob W , isSet→isGroupoid isSetWob))

        Inc : Functor |W| W
        Inc = DiscFunc λ x → x

        Inc^op : Functor |W| (W ^op)
        Inc^op = DiscFunc λ x → x
        

        -- since World is already ^op
        -- this is a covariant presheaf category
        -- op ^ op ↦ id
        𝒱 : Category (ℓ-suc ℓ) ℓ
        𝒱 = PresheafCategory W ℓ

        -- since World is already ^op
        -- this is a contravariant (normal) presheaf category
        -- op ^ op ^ op ↦ op
        𝒞 : Category (ℓ-suc ℓ) ℓ
        𝒞 = PresheafCategory (W ^op) ℓ

        _×P_ : ob 𝒱 → ob 𝒱 → ob 𝒱
        (P ×P Q)  = PshProd ⟅ P , Q ⟆b

        Fam : Category (ℓ-suc ℓ) ℓ
        Fam = FUNCTOR |W| (SET ℓ)

        open import src.Data.Direct
        module Future = Lan {ℓS = ℓ} (W ^op) isSetWob
        module Past = Ran {ℓS = ℓ} W isSetWob
        open UnitCounit
        
        Inc* : Functor 𝒞 Fam 
        Inc* = precomposeF (SET ℓ) (Inc)

        Inc^op* : Functor 𝒱 Fam 
        Inc^op* = precomposeF (SET ℓ) (Inc^op)
        
        F' : Functor Fam 𝒞 
        F' = Future.Lan

        F : Functor 𝒱 𝒞 
        F = F' ∘F Inc^op*

        adjF : F' ⊣ Inc*
        adjF = Future.adj

        U' : Functor Fam 𝒱 
        U' = Past.Ran

        U : Functor 𝒞 𝒱 
        U = U' ∘F Inc*

        adjU : Inc^op* ⊣ U' 
        adjU = Past.adj


    module Model {ℓS : Level} where 
        open import src.Data.Worlds hiding (Inc)


        data SynTy' : Type ℓS where 
            u n b : SynTy'

        SynTyisSet : isSet SynTy' 
        SynTyisSet = {!  !}

        SynTy : hSet ℓS 
        SynTy = SynTy' , SynTyisSet

        -- top maps are op
        W : Category (ℓ-suc ℓS) ℓS
        W = World SynTy



        _ : isSet (Σ[ X ∈ FinSet ℓS ] Unit* → SynTy')
        _ = isSet→ {A' = SynTy'}{A = Σ[ X ∈ FinSet ℓS ] Unit* } SynTyisSet   
        wset : isSet (ob W)
        wset = isSetΣ (isSetΣ {! isFinSet→isSet !} λ _ → isSetUnit*) λ _ → {!  !}

        open Cats {ℓS} W wset

        open import src.Data.DayConv
        open MonoidalStructure SynTy hiding (W)
        _ = {! src.Data.Worlds.MonoidalStructure  !}
        
        _⨂ᴰ_ : ob 𝒱 → ob 𝒱 → ob 𝒱
        A ⨂ᴰ B = _⊗ᴰ_ {MC = strmon} A B 

        -- observe action of F on objects
        module _ (A : ob 𝒱)(w₁ : ob W) where 
            -- must provide
            -- a future world w₂
            -- an injection f from w₁ to w₂ 
            -- and an element at that future world
            sig : (w₂ : ob W)(f : W [ w₂ , w₁ ])(a : (A ⟅ w₂ ⟆) .fst) → ((F ⟅ A ⟆) ⟅ w₁ ⟆) .fst 
            sig w₂ f a = w₂ , (f , a)
            -- action of F ⟅ A ⟆ on morphisms
            -- just precomposition of w₂↪w₁
            sigact : (w₂ : ob W)(f : W [ w₁ , w₂ ])→ ((F ⟅ A ⟆) ⟅ w₁ ⟆) .fst → ((F ⟅ A ⟆) ⟅ w₂ ⟆) .fst 
            sigact w₂ w₂↪w₁ (w₃ , w₁↪w₃ , Aw₃ ) = ((F ⟅ A ⟆)⟪ w₂↪w₁ ⟫) (w₃ , (w₁↪w₃ , Aw₃))
            
            
            
        -- observe actions of F on morphism
        module _ (A B : ob 𝒱)(nt : A ⇒ B )(w₁ : ob W) where 

            mor : 𝒞 [ F ⟅ A ⟆ , F ⟅ B ⟆ ]
            mor = F ⟪ nt ⟫

            open NatTrans
            -- in some current world w₁ 
            -- for any past world w₂ of w₁ 
            -- with injection p from 
            act : (w₂ : ob W)(p : W [ w₂ , w₁ ])(a : F-ob A w₂ .fst) → ((F ⟅ B ⟆) .F-ob w₁ ).fst
            act w₂ p a = mor .N-ob w₁ (w₂ , p , a )

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
            ret {val} = natTrans α {! makeNatTransPath ?  !} where 
                α : N-ob-Type val ((U ∘F F) ⟅ val ⟆)
                α w Vw = record { fun = λ w2 f → w2 , ((W ^op) .id , val .F-hom f Vw) }

                prf : N-hom-Type val ((U ∘F F) ⟅ val ⟆) α
                prf f = {!  !}

        -- denote terms
        module _ where 
            open import Cubical.HITs.SetCoequalizer.Base
            conv : 𝒱 [ Case b  ⨂ᴰ Case n , Termᵛ ]
            conv = natTrans {!   !} {!   !} where 
                α : N-ob-Type (Case b ⨂ᴰ Case n) Termᵛ
                α w₀ (SetCoequalizer.inc (((X ◂ _ ◂ wmap) , (Y ◂ _ ◂ wmap')) , (((w₁⊗w₂↪w₀ , ttmap) , Δ) , Case_b_w₁) , Case_n_w₂)) = {!   !}
                α w (coeq a i) = {!   !}
                α w (squash x x₁ p q i i₁) = {!   !}
                
            injSem : 𝒱 [ (Case b) ×P (tys b) , OSum ]
            injSem = natTrans α prf where
            
                α : N-ob-Type (Case b ×P (tys b)) OSum
                α w ((x , lift wxisb), y) = x , transport eqty y where

                    eqty : (tys b ⟅ w ⟆) .fst ≡ (tys (w .snd x) ⟅ w ⟆) .fst
                    eqty = cong fst (cong₂ _⟅_⟆ (cong tys (sym wxisb)) refl) 

                prf : N-hom-Type (Case b ×P tys b) OSum α
                prf f = {!   !}
               -- prf : N-hom-Type (Case b ×P Constant ((W ^op) ^op) (SET ℓ) (Lift Bool , isOfHLevelLift 2 isSetBool)) OSum α
               -- prf {(((X , Xfin) , tt* ) , w)}
               --     {(((Y , Yfin) , tt* ) , w')}
               --     (((f , femb), _) , Δ )  = ? --funExt λ{((x , lift wx≡b) , lift bval) → {!   !} }

            newcase : (ty : SynTy') → 𝒞 [ Termᶜ , F ⟅ Case ty ⟆ ]
            newcase ty = natTrans α {!   !} where 

                w' : ob W → ob W
                w' = extend ty

                w→w' : (w : ob W) → (W ^op) [ w , w' w ]
                w→w' w = (((inl , inlemb) , refl) , refl)

                Case_w : (w : ob W) →  Case ty .F-ob (w' w) .fst
                Case_w _ = (inr tt* , lift refl)

                α : N-ob-Type Termᶜ (F ⟅ Case ty ⟆)
                α w tt* = w' w , (w→w' w , Case_w  w)

            -- simple match
            match : (ty : SynTy') → 𝒱 [ Case ty ×P OSum , tys ty ]
            match ty = natTrans {!   !} {!   !}  where 
                α : N-ob-Type (Case ty ×P OSum) (tys ty)
                α w ((σ , lift wσ≡ty) , (σ' , e∈ty)) = transport lemma e∈ty where 
                
                    assuming : σ ≡ σ'
                    assuming = {!   !}

                    lemma : (tys (w .snd σ') ⟅ w ⟆) .fst ≡ (tys ty ⟅ w ⟆) .fst
                    lemma = {!   !}
                       --cong fst (cong₂ _⟅_⟆ (cong tys (snd w σ' ≡⟨ cong₂ _ refl assuming ⟩ snd w σ ≡⟨ wσ≡ty ⟩ ty ∎)) refl)
     


 

 