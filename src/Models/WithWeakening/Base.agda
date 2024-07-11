{-# OPTIONS --allow-unsolved-metas  --lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels hiding (extend)
open import Cubical.Functions.Embedding

open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets 
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.NaturalTransformation

open import Cubical.Data.Bool 
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.FinSet.DecidablePredicate 
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit

open import Cubical.HITs.SetQuotients renaming ([_] to q[_]) hiding (rec)

open Category
open Functor

module src.Models.WithWeakening.Base {ℓS : Level} where


    -- Syntactic Types
    module SyntacticTypes  where 

        data SynTy' : Type ℓS where 
            u n b : SynTy'

        SynTyisSet : isSet SynTy' 
        SynTyisSet = {!  !}

        SynTy : hSet ℓS 
        SynTy = SynTy' , SynTyisSet
    
    module Worlds where 
        open SyntacticTypes
        open import src.Data.FinSet
        open import Cubical.Categories.Displayed.Constructions.Comma
        open import Cubical.Categories.Instances.Terminal


        Inc : Functor (FinSetMono{ℓS}) (SET ℓS)
        Inc .F-ob (ty , fin) = ty , isFinSet→isSet fin 
        Inc .F-hom (f , _) x = f x
        Inc .F-id = refl
        Inc .F-seq (f , _) (g , _) = refl
        
        G : Functor (TerminalCategory {ℓS}) ((SET ℓS))
        G = FunctorFromTerminal SynTy

        -- this variance is used for the semicartisian day conv
        -- this is essentially a slice category but the Identity functor is replaced with an inclusion functor
        -- so that we have the top maps of the slice homs as injective functions
        W : Category (ℓ-suc ℓS) ℓS
        W = (Comma Inc G) ^op

        _ : isSet (Σ[ X ∈ FinSet ℓS ] Unit* → SynTy')
        _ = isSet→ {A' = SynTy'}{A = Σ[ X ∈ FinSet ℓS ] Unit* } SynTyisSet   
        wset : isSet (ob W)
        wset = isSetΣ (isSetΣ {! isFinSet→isSet !} λ _ → isSetUnit*) λ _ → {!  !}

    module CBPV
            {ℓS ℓC ℓC' : Level}
            (W : Category ℓC ℓC')
            (isSetWob : isSet (ob W)) where 
            
        open import Cubical.Categories.Adjoint
        open import Cubical.Categories.Adjoint.Monad
        open import Cubical.Categories.Instances.Discrete
        open import Cubical.Categories.Presheaf.Base
        open import Cubical.Categories.Presheaf.Constructions

        ℓ = (ℓ-max (ℓ-max ℓC ℓC') ℓS)

        |W| : Category ℓC ℓC 
        |W| = (DiscreteCategory (ob W , isSet→isGroupoid isSetWob))

        Inc : Functor |W| W
        Inc = DiscFunc λ x → x

        Inc^op : Functor |W| (W ^op)
        Inc^op = DiscFunc λ x → x
        
        -- since World is already ^op
        -- this is morally a covariant presheaf category
        -- op ^ op ↦ id
        𝒱 : Category (ℓ-suc ℓ) ℓ
        𝒱 = PresheafCategory W ℓ

        -- since World is already ^op
        -- this is morally a contravariant (normal) presheaf category
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

    module Monoids where 
        open Worlds 
        open CBPV {ℓS} W wset


        open import Cubical.Categories.Constructions.BinProduct 
        open import Cubical.Categories.Monoidal.Base
        
        open import Cubical.Data.Empty hiding (rec)
        open import Cubical.Data.SumFin.Base 

        open import Cubical.HITs.PropositionalTruncation hiding(rec ; map)

        -- Monoid on Worlds
        
        emptyFin* : isFinSet {ℓS} (Lift ⊥)
        emptyFin* = 0 , ∣ (λ()) , record { equiv-proof = λ() } ∣₁

        emptymap : ob W 
        emptymap = ((Lift (Fin 0 ) , emptyFin*) , tt*) , λ() 

        _⨂_ : Functor (W ×C W) W
        _⨂_ .F-ob ((((X , Xfin) , tt* ) , w) , (((Y , Yfin) , tt* ) , w')) = 
            (((X ⊎ Y) , isFinSet⊎ ((X , Xfin)) (Y , Yfin)) , tt*) , rec w w'
        _⨂_ .F-hom {X}{Y}((((f , femb) , _), Δ₁) , (((g , gemb) , _), Δ₂)) = 
            ((map f g , {!   !}) , refl) , funExt λ {(inl x) → {!  Δ₁  !}
                                                    ; (inr x) → {! Δ₂  !}} 
        _⨂_ .F-id = {! refl  !}
        _⨂_ .F-seq = {!  isSetHom !}

        mon : StrictMonStr W
        mon = record { tenstr = 
            record { ─⊗─ = _⨂_ ; 
                        unit = emptymap } ; 
                assoc = {!   !} ; 
                idl = λ{x → ΣPathP ((ΣPathP (ΣPathP ({! lemma  !} , {!   !}) , {!   !})) , {! ΣPathP ?  !})} ; 
                idr = {!   !} }

        strmon : StrictMonCategory (ℓ-suc ℓS) ℓS 
        strmon = record { C = W ; sms = mon }
        
        open import src.Data.Semicartesian

        semimon : SemicartesianStrictMonCat {!   !} {!   !}
        semimon = record { C = W ; sms = mon ; term = emptymap , λ y → ((((λ{()}) , {!  !}) , refl) , {!   !}) , {!   !} ; semi = refl }


        -- Monoid on Values
        open import src.Data.DayConv
        _⨂ᴰᵥ_ : ob 𝒱 → ob 𝒱 → ob 𝒱
        A ⨂ᴰᵥ B = _⊗ᴰ_ {MC = strmon} A B 


        module AlgExperiment where
            open import Cubical.Categories.Instances.FunctorAlgebras

            module _ (M : Monad 𝒞) where 
                T : Functor 𝒞 𝒞
                T = M .fst

                Alg : Category (ℓ-suc ℓ) ℓ
                Alg = AlgebrasCategory {C = 𝒞} T

                open Algebra
                open AlgebraHom
                open NatTrans
                open IsMonad


                partial : ob W → ob 𝒱 → ob 𝒱 
                partial w A .F-ob w' = A .F-ob (_⨂_ .F-ob (w , w'))
                partial w A .F-hom {w₂}{w₃} f Aw⊗w₂ = A .F-hom  (_⨂_ .F-hom (((W ^op) .id) , f))  Aw⊗w₂
                partial w A .F-id  = cong (λ x → (A .F-hom x)) (_⨂_ .F-id) ∙ A .F-id
                partial w A .F-seq f g = {!   !}
                
                vsep : ob 𝒱 → ob 𝒱 → ob 𝒱 
                vsep A B .F-ob w = 𝒱 [ A , partial w B ]  ,  𝒱 .isSetHom
                vsep A B .F-hom f = {!   !}
                vsep A B .F-id = {!   !}
                vsep A B .F-seq = {!   !}
                
                sep : ob 𝒱 → ob Alg → ob Alg 
                sep A B = algebra {!   !} {!   !}
        module Sterling  where 
            open import Cubical.Categories.Instances.FunctorAlgebras

            module _ (M : Monad (SET ℓ)) where 

                T : Functor (SET ℓ) (SET ℓ)
                T = fst M

                Alg' : Category (ℓ-suc ℓ) ℓ
                Alg' = AlgebrasCategory {C = (SET ℓ)} T

                -- W ^op in Sterling, adjusted here for our variance
                Alg : Category (ℓ-suc ℓ) ℓ
                Alg = FUNCTOR W Alg'

                open Algebra
                open AlgebraHom
                open NatTrans
                open IsMonad

                Forget : Functor Alg 𝒞
                Forget .F-ob A .F-ob w = A .F-ob w .carrier
                Forget .F-ob A .F-hom{w₁}{w₂} f = A .F-hom f .carrierHom
                Forget .F-ob A .F-id = {!  refl !}
                Forget .F-ob A .F-seq f g = {!   !}
                Forget .F-hom f .N-ob w = f .N-ob w .carrierHom 
                Forget .F-hom f .N-hom g = {! f .N-hom g .strHom !}
                Forget .F-id = {!   !}
                Forget .F-seq = {!   !}

                Free : Functor 𝒞 Alg 
                Free .F-ob A .F-ob w = algebra (T .F-ob (A .F-ob w)) (μ (snd M) .N-ob _)
                Free .F-ob A .F-hom{w₁}{w₂} f = algebraHom (T .F-hom (A .F-hom f)) {!   !}
                Free .F-ob A .F-id = {!   !}
                Free .F-ob A .F-seq = {!   !}
                Free .F-hom{A}{B} f .N-ob w = algebraHom (T .F-hom (f .N-ob w)) {!   !}
                Free .F-hom f .N-hom = {!   !}
                Free .F-id = {!   !}
                Free .F-seq = {!   !}

                module experiment where 
                    -- working out the denotation of a separating function type
                    -- first, denotation of a function type

                    fun : (A : ob 𝒱)(B : ob Alg) → ob Alg 
                    fun A B .F-ob w = algebra   ((SET ℓ)[ A .F-ob w , B .F-ob w .carrier ] , (SET ℓ) .isSetHom) 
                                                λ T_a→b Aw → B .F-ob w .str (T .F-hom  (λ f → f Aw) T_a→b)
                        {- a map 
                            A(w) → B(w)  in Set where B is the carrier of the given algebra

                            The rest should follow similarly to the Levy model
                            it just requires more side obligations.. 
                                -- computation function types
                                funty : ob 𝒱 → ob 𝒞 → ob 𝒞 
                                funty A B .F-ob w = (SET ℓ)[ A .F-ob w , B .F-ob w ] , (SET ℓ) .isSetHom
                                funty A B .F-hom f g Ay = (B .F-hom f) (g ((A .F-hom f) Ay)) 
                                funty A B .F-id = funExt λ g → funExt λ a → 
                                    B .F-hom (id W) (g (A .F-hom (id W) a)) ≡⟨ funExt⁻  (B .F-id) _ ⟩
                                    (g (A .F-hom (id W) a)) ≡⟨ cong g (funExt⁻ (A .F-id) _) ⟩ 
                                    g a ∎
                                funty A B .F-seq f g = funExt λ h → funExt λ Az → funExt⁻ (B .F-seq f g) _ ∙ 
                                    cong (λ x → seq' (SET ℓ) (F-hom B f) (F-hom B g) (h x)) (funExt⁻ (A .F-seq _ _) _) 
                        -}
                    fun A B .F-hom f = algebraHom (λ g Ay → B .F-hom f .carrierHom ((g ((A .F-hom f) Ay)))) {!   !}
                    fun A B .F-id = AlgebraHom≡ _ (funExt λ g → funExt λ a → {! (funExt⁻  (B .F-id) _) ∙ cong g (funExt⁻ (A .F-id) _)   !})
                    fun A B .F-seq = {!   !}


                    {- From the Levy Model
                        -- separating function type
                        sep : ob 𝒱 → ob 𝒞 → ob 𝒞 
                            -- should be an end ?
                        sep A B .F-ob w = (∀ (w' : ob W) → (SET ℓ)[ A .F-ob w' , B .F-ob (_⨂_ .F-ob (w , w')) ]) , isSetΠ  λ _ → (SET ℓ) .isSetHom
                        sep A B .F-hom {w₁}{w₂} w₁→w₂ end w₃ Aw₃ = B .F-hom (_⨂_ .F-hom (w₁→w₂ , W .id)) (end w₃ Aw₃)
                        sep A B .F-id = funExt λ end → funExt λ w₃  → funExt λ Aw₃ → cong (λ x → (B .F-hom x) (end w₃ Aw₃) ) (_⨂_ .F-id) ∙ funExt⁻ (B .F-id) ((end w₃ Aw₃))
                        sep A B .F-seq f g = funExt λ end → funExt λ w₃  → funExt λ Aw₃ → cong (λ x → (B .F-hom x) (end w₃ Aw₃) ) {!  (_⨂_ .F-seq _ _ )  !} ∙ {!   !}
                        -- cong (λ x → (B .F-hom x) (end w₃ Aw₃) ) {! _⨂_ .F-seq _ _  !} ∙ funExt⁻ (B .F-seq _ _ ) ((end w₃ Aw₃))
 
                    -}
                    partial : ob W → ob 𝒱 → ob 𝒱 
                    partial w A .F-ob w' = A .F-ob (_⨂_ .F-ob (w , w'))
                    partial w A .F-hom {w₂}{w₃} f Aw⊗w₂ = A .F-hom  (_⨂_ .F-hom (((W ^op) .id) , f))  Aw⊗w₂
                    partial w A .F-id  = cong (λ x → (A .F-hom x)) (_⨂_ .F-id) ∙ A .F-id
                    partial w A .F-seq f g = {!   !}
                    
                    vsep : ob 𝒱 → ob 𝒱 → ob 𝒱 
                    vsep A B .F-ob w = 𝒱 [ A , partial w B ]  ,  𝒱 .isSetHom
                    vsep A B .F-hom f = {!   !}
                    vsep A B .F-id = {!   !}
                    vsep A B .F-seq = {!   !}

                    sep' : (A : ob 𝒱)(B : ob Alg) → ob Alg  
                    sep' A B .F-ob w = algebra ( vsep A {!   !} .F-ob w ) {!   !}
                    sep' A B .F-hom = {!   !}
                    sep' A B .F-id = {!   !}
                    sep' A B .F-seq = {!   !}

                    -- ??
                            -- separating function typ

                    -- no UP shown yet
                    sepc : ob 𝒱 → ob 𝒞 → ob 𝒞 
                        -- should be an end ?
                    sepc A B .F-ob w = (∀ (w' : ob W) → (SET ℓ)[ A .F-ob w' , B .F-ob (_⨂_ .F-ob (w , w')) ]) , isSetΠ  λ _ → (SET ℓ) .isSetHom
                    sepc A B .F-hom {w₁}{w₂} w₁→w₂ end w₃ Aw₃ = B .F-hom (_⨂_ .F-hom (w₁→w₂ , W .id)) (end w₃ Aw₃)
                    sepc A B .F-id = funExt λ end → funExt λ w₃  → funExt λ Aw₃ → cong (λ x → (B .F-hom x) (end w₃ Aw₃) ) (_⨂_ .F-id) ∙ funExt⁻ (B .F-id) ((end w₃ Aw₃))
                    sepc A B .F-seq f g = funExt λ end → funExt λ w₃  → funExt λ Aw₃ → cong (λ x → (B .F-hom x) (end w₃ Aw₃) ) {!  (_⨂_ .F-seq _ _ )  !} ∙ {!   !}
                    -- cong (λ x → (B .F-hom x) (end w₃ Aw₃) ) {! _⨂_ .F-seq _ _  !} ∙ funExt⁻ (B .F-seq _ _ ) ((end w₃ Aw₃))

                    sep : (A : ob 𝒱)(B : ob Alg) → ob Alg 
                    sep A B .F-ob w = algebra ((∀ (w' : ob W) → (SET ℓ)[ A .F-ob w' , B .F-ob (_⨂_ .F-ob (w , w')) .carrier ]) , isSetΠ  λ _ → (SET ℓ) .isSetHom) 
                                     λ Tf w' Aw' → B .F-ob (_⨂_ .F-ob (w , w')) .str ((T . F-hom (λ f → f w' Aw') Tf))
                                     
                    sep A B .F-hom {w₁}{w₂} w₁→w₂  = 
                        algebraHom 
                            (λ f w₃ Aw₃ → B .F-hom (_⨂_ .F-hom (w₁→w₂ , W .id)) .carrierHom (f w₃ Aw₃)) 
                            {! AlgebraHom≡ ? ?  !}
                    sep A B .F-id = AlgebraHom≡ T {!   !}
                    sep A B .F-seq f g = AlgebraHom≡ T {!   !}

                    -- TODO arbitrary
                    {-
                        should be an "oblique" morphism
                        and work for 𝒱 [A , U B] and Alg [ F A , B ] 
                    -}
                    computation : (A : ob 𝒱)(B : ob Alg) → Set ℓ 
                    computation A B = ∀ (w : ob W) → (SET ℓ)[ A .F-ob w , B .F-ob w .carrier ]

                    open import Cubical.Foundations.Isomorphism
                    open Iso hiding (fun)
                    open import Cubical.HITs.SetCoequalizer.Base
                    open SetCoequalizer


                    -- same issue as Levy model
                    sepUp : (A B : ob 𝒱)(C : ob Alg) → Iso (computation (A ⨂ᴰᵥ B) C) (computation A (sep B C))
                    sepUp A B C = 
                        iso 
                            (λ{ M → λ w Aw w' Bw' → M (_⨂_  .F-ob (w , w')) (inc ((w , w') , (((W .id) , Aw) , Bw'))) }) 
                            (λ{M w (inc ((w₂ , w₃) , (w→w₂⊗w₃ , Aw₂) , Bw₃)) → {! M  w₂ Aw₂ w₃ Bw₃  !}
                                    -- {! C .F-hom w→w₂⊗w₃   !}  
                                    -- {! M  w₂ Aw₂ w₃ Bw₃!} 
                             ; M w (coeq a i) → {!   !}
                             ; M w (squash x₁ x₂ p q i i₁) → {!   !}}) 
                            {!   !} 
                            {!   !}
{-
            module asExt where
                open import Cubical.Categories.Monad.Algebra hiding (T)
                open import Cubical.Categories.Monad.ExtensionSystem

                T : Functor 𝒞 𝒞 
                T = Id 

                E : ExtensionSystem 𝒞
                E = T .F-ob , record
                                { η = λ {X} → natTrans (λ w Xw → Xw) λ f → refl ; 
                                bind = λ {X Y} → λ x → x; 
                                bind-r = makeNatTransPath refl ; 
                                bind-l = makeNatTransPath refl ; 
                                bind-comp = makeNatTransPath refl }


                𝒞-Alg : Category (ℓ-suc ℓ) (ℓ-suc ℓ)
                𝒞-Alg = ALGEBRA {C = 𝒞} E

                 

            module asMonad where 
                open import Cubical.Categories.Instances.FunctorAlgebras

                -- TODO guarded ITrees
                -- TODO Option monad
                T : Functor 𝒞 𝒞 
                T = Id 

                TMon : Monad 𝒞
                TMon = T , (record { η = natTrans (λ x → {!   !}) {!   !} ; μ = {!   !} ; idl-μ = {!   !} ; idr-μ = {!   !} ; assoc-μ = {!   !} })
                
                𝒞-Alg : Category (ℓ-suc ℓ) ℓ
                𝒞-Alg = AlgebrasCategory {C = 𝒞} T

                FreeT : (X : ob 𝒞) →  𝒞 [ T .F-ob (T .F-ob X) , (T .F-ob X) ]
                FreeT X = natTrans (λ {w TTXw → {!  TTXw !}}) {!   !}

                FreeAlg : Functor 𝒞 𝒞-Alg 
                FreeAlg .F-ob X = algebra (T .F-ob X) (FreeT X)
                FreeAlg .F-hom = {!   !}
                FreeAlg .F-id = {!   !}
                FreeAlg .F-seq = {!   !}

                ℱ : Functor 𝒱 𝒞-Alg
                ℱ = FreeAlg ∘F F

                𝒰 : Functor 𝒞-Alg 𝒱 
                𝒰 = U ∘F ForgetAlgebra T
-} 
        
             