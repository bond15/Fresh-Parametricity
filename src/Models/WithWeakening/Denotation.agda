{-# OPTIONS --allow-unsolved-metas  --lossy-unification #-}

module src.Models.WithWeakening.Denotation {ℓS} where
    
    open import Cubical.Foundations.HLevels hiding (extend)
    open import Cubical.Foundations.Prelude hiding (comp)
    open import Cubical.Functions.Embedding 

    open import Cubical.Categories.Category 
    open import Cubical.Categories.Functor
    open import Cubical.Categories.Functors.Constant
    open import Cubical.Categories.Instances.Sets 
    open import Cubical.Categories.NaturalTransformation


    open import Cubical.Data.Bool 
    open import Cubical.Data.FinSet
    open import Cubical.Data.FinSet.Constructors
    open import Cubical.Data.FinSet.DecidablePredicate 
    open import Cubical.Data.Nat
    open import Cubical.Data.Sigma
    open import Cubical.Data.Sum
    open import Cubical.Data.Unit

    open Category
    open Functor

    open import src.Models.WithWeakening.Base {ℓS} 
    
    module utils  where 

        open import Cubical.Foundations.Isomorphism 
        open Iso
        open Worlds
        open SyntacticTypes 
        open CBPV {ℓS} W wset

        Unit*Fin : FinSet ℓS
        Unit*Fin = Unit* , EquivPresIsFinSet 
                            (isoToEquiv (iso 
                                            (λ{tt  → tt*}) 
                                            (λ{tt* → tt}) 
                                            (λ{ tt*  → refl}) 
                                            (λ{ tt → refl }))) isFinSetUnit

        inlemb : {ℓ : Level}{A B : Type ℓ} → isEmbedding (inl {ℓ}{ℓ}{A}{B})
        inlemb = λ w x → record { equiv-proof = λ y → ({!   !} , {!   !}) , (λ y₁ → {!   !}) }
        
        inc : FinSet ℓS → FinSet ℓS
        inc X = ((X .fst ⊎ Unit*) , isFinSet⊎ X Unit*Fin)

        inj : {X Y  : FinSet ℓS}(f : X .fst → Y .fst) → (inc X) .fst → (inc Y) .fst
        inj f (inl x) = inl (f x)
        inj f (inr x) = inr x

        extend' : {X : FinSet ℓS} → (f : X .fst → SynTy')(ty : SynTy') → ((inc X) .fst → SynTy')
        extend' f ty (inl x) = f x
        extend' f ty (inr tt*) = ty

        extend : (ty : SynTy') → ob |W| → ob |W|
        extend ty ((X , tt*) , w) = (inc X , tt*) , extend' {X} w ty

        dup : {A : ob 𝒱} → 𝒱 [ A , A ×P A ]
        dup = natTrans (λ x a → a , a) λ f → refl
        
        bimap : {A B C D : ob 𝒱} → 
            𝒱 [ A , B ] → 
            𝒱 [ C , D ] → 
            𝒱 [ A ×P C , B ×P D ]
        bimap M N = natTrans (λ{w (Aw , Cw) → M .N-ob w Aw , N .N-ob w Cw}) λ f → {! refl  !} where 
            open NatTrans   
        
        p₁ : {A₁ A₂ : ob 𝒱} → 𝒱 [ (A₁ ×P A₂) , A₁ ]
        p₁ = natTrans (λ x p → fst p) λ f → refl 

 
    -- denote types
    module _ where 
        open Worlds 
        open SyntacticTypes 
        open CBPV {ℓS} W wset 
        open Monoids 
        
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
        Case ty .F-ob (((X , Xfin ), _ ), w) = (Σ[ σ ∈ X ] Lift ( w σ ≡ ty)) , {!   !}
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

        -- value function types
        -- exponent object in presheaf category
        funty' : ob 𝒱 → ob 𝒱 → ob 𝒱 
        funty' A B .F-ob w = {!   !}
        funty' A B .F-hom f g = {! A .F-hom f  !}
        funty' A B .F-id = {!   !}
        funty' A B .F-seq f g = {!   !}

        -- separating function type
        sep : ob 𝒱 → ob 𝒞 → ob 𝒞 
            -- should be an end ?
        sep A B .F-ob w = (∀ (w' : ob W) → (SET ℓ)[ A .F-ob w' , B .F-ob (_⨂_ .F-ob (w , w')) ]) , isSetΠ  λ _ → (SET ℓ) .isSetHom
        sep A B .F-hom {w₁}{w₂} w₁→w₂ end w₃ Aw₃ = B .F-hom (_⨂_ .F-hom (w₁→w₂ , W .id)) (end w₃ Aw₃)
        sep A B .F-id = funExt λ end → funExt λ w₃  → funExt λ Aw₃ → cong (λ x → (B .F-hom x) (end w₃ Aw₃) ) (_⨂_ .F-id) ∙ funExt⁻ (B .F-id) ((end w₃ Aw₃))
        sep A B .F-seq f g = funExt λ end → funExt λ w₃  → funExt λ Aw₃ → cong (λ x → (B .F-hom x) (end w₃ Aw₃) ) {!  (_⨂_ .F-seq _ _ )  !} ∙ {!   !}
        -- cong (λ x → (B .F-hom x) (end w₃ Aw₃) ) {! _⨂_ .F-seq _ _  !} ∙ funExt⁻ (B .F-seq _ _ ) ((end w₃ Aw₃))

        -- separating function type for values

        partial : ob W → ob 𝒱 → ob 𝒱 
        partial w A .F-ob w' = A .F-ob (_⨂_ .F-ob (w , w'))
        partial w A .F-hom {w₂}{w₃} f Aw⊗w₂ = A .F-hom  (_⨂_ .F-hom (((W ^op) .id) , f))  Aw⊗w₂
        partial w A .F-id  = cong (λ x → (A .F-hom x)) (_⨂_ .F-id) ∙ A .F-id
        partial w A .F-seq f g = {!   !}

        open NatTrans
        sepv' : ob 𝒱 → ob 𝒱 → ob 𝒱
            -- this version is a natural transformation in V
        sepv' A B .F-ob w = 𝒱 [ A , partial w B ] , 𝒱 .isSetHom
        sepv' A B .F-hom {w₁}{w₂} w₁→w₂ M = natTrans (λ w₃ Aw₃ → B .F-hom (_⨂_ .F-hom (w₁→w₂ , W .id))  (M .N-ob w₃ Aw₃)) λ f → {! w  !}
        sepv' A B .F-id = {!   !}
        sepv' A B .F-seq f g = {!   !}

        
        sepv : ob 𝒱 → ob 𝒱 → ob 𝒱
            -- this version is a natural transformation in V
        sepv A B .F-ob w = (∀ (w' : ob W) → (SET ℓ)[ A .F-ob w' , B .F-ob (_⨂_ .F-ob (w , w')) ]) , isSetΠ  λ _ → (SET ℓ) .isSetHom
        sepv A B .F-hom {w₁}{w₂} w₁→w₂ end w₃ Aw₃ = B .F-hom (_⨂_ .F-hom (w₁→w₂ , W .id)) (end w₃ Aw₃)
        sepv A B .F-id = funExt λ end → funExt λ w₃  → funExt λ Aw₃ → cong (λ x → (B .F-hom x) (end w₃ Aw₃) ) (_⨂_ .F-id) ∙ funExt⁻ (B .F-id) ((end w₃ Aw₃))
        sepv A B .F-seq f g = funExt λ end → funExt λ w₃  → funExt λ Aw₃ → {! funExt⁻ (B .F-seq _ _) _ ∙ ?  !}



        Termᶜ : ob 𝒞 
        Termᶜ = Constant _ _ (Unit* , isOfHLevelLift 2 isSetUnit)
        
        Termᵛ : ob 𝒱
        Termᵛ = Constant _ _ (Unit* , isOfHLevelLift 2 isSetUnit)

        -- judgements
        value : (Γ A : ob 𝒱) → Set (ℓ-suc ℓS)
        value Γ A = 𝒱 [ Γ , A ]

        -- not quite a morphism in 𝒞 ..
        -- the naturality condition is off
        -- alternatively, could find some way to turn Γ into a computation.. 
        -- besides F?
        record computation (Γ : ob 𝒱)(B : ob 𝒞) : Set (ℓ-suc ℓS) where 
            field 
                α : ∀ (w : ob W) → (SET ℓ)[ Γ .F-ob w , B .F-ob w ]
                -- nat : ∀ {w w' : ob W} → (f : W [ w , w' ]) → Γ .F-hom f ⋆⟨ SET ℓ ⟩ α w ⋆⟨ SET ℓ ⟩ A .F-hom f ≡ α w' 

        computation' : (Γ : ob 𝒱)(B : ob 𝒞) → Set (ℓ-suc ℓS)
        computation' Γ B = 𝒞 [ F .F-ob Γ , B ]

        Comp : (Γ : ob 𝒱)(B : ob 𝒞) → Set (ℓ-suc ℓS)
        Comp Γ B = ∀ (w : ob W) → (SET ℓ)[ Γ .F-ob w , B .F-ob w ]

        CompAgain : (Γ : ob 𝒱)(B : ob 𝒞) → Set (ℓ-suc ℓS)
        CompAgain Γ B = value Γ (U .F-ob B)

        comp≡ : {Γ : ob 𝒱}{A : ob 𝒞}{c₁ c₂ : computation Γ A} → c₁ .computation.α ≡ c₂ .computation.α → c₁ ≡ c₂
        comp≡ = cong (λ x → record { α = x })

    -- denote terms
    module _ where 
        open utils
        open Worlds
        open SyntacticTypes 
        open CBPV {ℓS} W wset
        open Monoids
        open import src.Data.DayConv
        open import src.Data.Semicartesian
        open import Cubical.HITs.SetCoequalizer.Base
        
        injSem : {Γ : ob 𝒱} → value Γ (Case b) → value Γ (tys b ) → value Γ OSum 
        injSem {Γ} m p  = ctx ⋆⟨ 𝒱 ⟩ injSem' where 

            ctx : 𝒱 [ Γ  , (Case b) ×P (tys b) ]
            ctx = natTrans (λ w γ → (m ⟦ w ⟧)(γ) , (p ⟦ w ⟧)(γ)) λ f → {!  !}

            injSem' : 𝒱 [ (Case b) ×P (tys b) , OSum ]
            injSem' = natTrans α prf where
            
                α : N-ob-Type (Case b ×P (tys b)) OSum
                α w ((x , lift wxisb), y) = x , transport eqty y where

                    eqty : (tys b ⟅ w ⟆) .fst ≡ (tys (w .snd x) ⟅ w ⟆) .fst
                    eqty = cong fst (cong₂ _⟅_⟆ (cong tys (sym wxisb)) refl) 

                prf : N-hom-Type (Case b ×P tys b) OSum α
                prf f = {!   !}

        newcase : 
            {Γ : ob 𝒱}{B : ob 𝒞}→ 
            (ty : SynTy') → 
            computation (Γ ⨂ᴰᵥ Case ty) B → 
            computation Γ B
        newcase {Γ} {B} ty record { α = α } = record { α = goal} where 
            goal : (w : ob W) → SET ℓ [ Γ .F-ob w , B .F-ob w ]
            goal w₁ Γw₁ = B .F-hom w₁⊗w₂→w₁ (α w₁⊗w₂ (SetCoequalizer.inc ((w₁ , w₂) , ((W .id , Γw₁) , casew₂))) ) where
                -- this doesn't work
                -- α w₁ (SetCoequalizer.inc ((w₁ , w₂) , ((w₁→w₁⊗w₂ , Γw₁) , casew₂))) where
                -- b/c
                -- this doesn't exist
                --w₁→w₁⊗w₂ : W [ w₁ , w₁⊗w₂ ]
                open SemicartesianStrictMonCat semimon
                
                w₂ : ob W 
                w₂ = (Unit*Fin , tt*) , (λ{tt* → ty})

                w₁⊗w₂ : ob W 
                w₁⊗w₂ = _⨂_ .F-ob (w₁ , w₂)

                w₁⊗w₂→w₁ : W [ w₁⊗w₂ , w₁ ]
                w₁⊗w₂→w₁ = proj₁

                casew₂ : fst (Case ty ⟅ w₂ ⟆)
                casew₂ = tt* , (lift refl) 

        -- fun Intro
        funIntro : {Γ A : ob 𝒱}{B : ob 𝒞} → computation (Γ ×P A) B → computation Γ (funty A B) 
        funIntro {Γ} {A} {B} record { α = α } = record { α = λ w Γw Aw → α w (Γw , Aw) }

        funElim : {Γ Δ A : ob 𝒱}{B : ob 𝒞} → 
            computation Γ (funty A B) → 
            value Δ A → 
            computation (Γ ×P Δ) B 
        funElim record { α = α } (natTrans N-ob N-hom) = record { α = λ{ w (Γw , Δw) → α w Γw (N-ob w Δw) }}
        
        open import Cubical.Foundations.Isomorphism
        open Iso hiding (fun)

        funUP : {Γ A : ob 𝒱}{B : ob 𝒞} → Iso (computation (Γ ×P A) B) (computation Γ (funty A B))
        funUP = iso 
                funIntro 
                (λ{record { α = α } → record { α = λ{ w (Γw , Aw) → α w Γw Aw } }}) 
                (λ{record { α = α } → refl }) 
                (λ{record { α = α } → refl })

        prodIntro : {Γ  A₁ A₂ : ob 𝒱} → 
            value Γ A₁ → 
            value Γ A₂ → 
            value Γ (A₁ ×P A₂)
        prodIntro M N = dup ⋆⟨ 𝒱 ⟩ bimap M N

        prodElim₁ : {Γ  A₁ A₂ : ob 𝒱} → 
            value Γ (A₁ ×P A₂) → 
            value Γ A₁
        prodElim₁ M = M ⋆⟨ 𝒱 ⟩ p₁

        prodBeta : {Γ  A₁ A₂ : ob 𝒱} → 
            (M : value Γ A₁) → 
            (N : value Γ A₂) → 
            prodElim₁ (prodIntro M N) ≡ M 
        prodBeta M N = makeNatTransPath refl
        
        -- just bilinear map
        sepProdIntro : {Γ Δ A₁ A₂ : ob 𝒱} → 
            value Γ A₁ → 
            value Δ A₂ → 
            value (Γ  ⨂ᴰᵥ Δ) (A₁ ⨂ᴰᵥ A₂) 
        sepProdIntro M N  = Day-Functor strmon .F-hom (M , N)

        sepProdElim₁ : {Γ Δ A₁ A₂ : ob 𝒱} → 
            value (Γ  ⨂ᴰᵥ Δ) (A₁ ⨂ᴰᵥ A₂) → 
            value (Γ  ⨂ᴰᵥ Δ) A₁ 
        sepProdElim₁ M = M ⋆⟨ 𝒱 ⟩ {!   !}  
        -- semicartesian projection
        -- but how does thas split up worlds?

        uhg  : {w : ob W}{B : ob 𝒞} → U .F-ob B .F-ob w .fst → B .F-ob w .fst
        uhg {w} {B} record { fun = fun } = fun w (W .id)
        module variancesucks where   
            -- same problem if you try to interpret computations as 
            -- 𝒱 [ A , (U B) ]
            -- or 𝒞 [ F A ,  B ]       
            sepIntro :  {Γ A : ob 𝒱}{B : ob 𝒞} → CompAgain (Γ ⨂ᴰᵥ A) B → CompAgain Γ (sep A B) 
            sepIntro {Γ} {A} {B} (natTrans N-ob N-hom) = natTrans goal {!   !} where 
                goal : N-ob-Type Γ (U .F-ob (sep A B))
                goal w₁ Γw₁ = record { fun = wtf } where 
                    wtf : (w₂ : ob W) → W [ w₂ , w₁ ] → (Inc* ⟅ sep A B ⟆) .F-ob w₂ .fst
                    wtf w₂ w₂→w₁ w₃ Aw₃ = uhg (N-ob (_⨂_ .F-ob  (w₂ , w₃)) (SetCoequalizer.inc ((w₂ , w₃) , (((W .id) , (Γ .F-hom w₂→w₁ Γw₁)) , Aw₃))) ) 

            open Past.End
            sepIntroInv : {Γ A : ob 𝒱}{B : ob 𝒞} → CompAgain Γ (sep A B) → CompAgain (Γ ⨂ᴰᵥ A) B 
            sepIntroInv {Γ} {A} {B} (natTrans N-ob N-hom) = natTrans goal {!   !} where 
                goal : N-ob-Type (Γ ⨂ᴰᵥ A) (U .F-ob B)
                goal w₁ (SetCoequalizer.inc ((w₂ , w₃) , (w₁→w₂⊗w₃ , Γw₂) , Aw₃)) = record { fun = λ  w₄  w₄→w₁ → B .F-hom {! w₄→w₁ ⋆⟨ W ⟩ w₁→w₂⊗w₃  !}  (N-ob w₂ Γw₂ .fun w₂ (W .id) w₃ Aw₃)  }
                goal w₁ (coeq a i) = {!   !}
                goal w₁ (squash x₁ x₂ p q i i₁) = {!   !}

        module valuesep where 
            sepvIntro :  {Γ A B : ob 𝒱} → value (Γ ⨂ᴰᵥ A) B → value Γ (sepv A B)
            sepvIntro {Γ} {A} {B} (natTrans N-ob N-hom) = natTrans goal {!   !} where 
                goal : N-ob-Type Γ (sepv A B)
                goal w₁ Γw₁ w₂ Aw₂ = N-ob (_⨂_ .F-ob (w₁ , w₂)) (SetCoequalizer.inc ((w₁ , w₂) , (((W .id) , Γw₁) , Aw₂)))

            sepvIntroInv :  {Γ A B : ob 𝒱} → value Γ (sepv A B) → value (Γ ⨂ᴰᵥ A) B 
            sepvIntroInv {Γ} {A} {B} (natTrans N-ob N-hom) = natTrans goal {!   !} where 
                goal : N-ob-Type (Γ ⨂ᴰᵥ A) B
                goal w₁ (SetCoequalizer.inc ((w₂ , w₃) , (w₁→w₂⊗w₃ , Γw₂) , Aw₃)) = B .F-hom w₁→w₂⊗w₃ (N-ob w₂ Γw₂ w₃ Aw₃)
                goal w₁ (coeq a i) = {!   !}
                goal w₁ (squash x x₁ p q i i₁) = {!   !}

            -- so this works as expected.. 
            open NatTrans
            sepUP : {Γ A B : ob 𝒱} → Iso (value (Γ ⨂ᴰᵥ A) B)  (value Γ (sepv A B))
            sepUP {Γ}{A}{B}= iso 
                        sepvIntro 
                        sepvIntroInv 
                        ((λ b → makeNatTransPath (funExt λ w → funExt λ Γw → funExt λ w' → funExt λ Aw' → funExt⁻  (B .F-id {(_⨂_ .F-ob (w , w'))}) (N-ob b w Γw w' Aw')) )) 
                        λ b → makeNatTransPath (funExt λ w → funExt λ p → {! refl  !})
            
            -- but this is an issue?
            sus : 𝒱 [ Termᵛ , sepv (Case b) (tys b) ]
            sus = natTrans (λ{w₁ tt* w' (σ , w'σ≡b) → {!   !}}) {!   !}
            {-
                from simplestate.agda
                
                        -- if reference y is supposed to be fresh.. why can i use it?!
            test3 : (X : ob Inj) → (Ref ⊸ T .F-ob BoolF) .F-ob X .fst
            test3 X = λ Y y → λ Z X+Y→Z Sz → Z , ((Inj .id) , (Sz , (Sz ((inr ⋆⟨ SET ℓS ⟩ (fst X+Y→Z)) y))))
            -- Z X+Y→Z Sz come from the U functor 
            -}


        sepIntro :  {Γ A : ob 𝒱}{B : ob 𝒞} → computation (Γ ⨂ᴰᵥ A) B → computation Γ (sep A B) 
        sepIntro record { α = α } = record { α = λ w Γw w' Aw' → α (_⨂_ .F-ob (w , w')) (SetCoequalizer.inc ((w , w') , ( W .id , Γw) , Aw')) }


        {-sepProdIso : {A B : ob 𝒱}{w : ob W} → Iso ((A ⨂ᴰᵥ B) .F-ob w .fst) ((A ×P B) .F-ob w .fst)
        sepProdIso {A}{B}{w} = iso to {!   !} {!   !} {!   !} where 
            open SemicartesianStrictMonCat semimon
            to : (A ⨂ᴰᵥ B) .F-ob w .fst → (A ×P B) .F-ob w .fst
            to (SetCoequalizer.inc ((w₂ , w₃) , (w→w₂⊗w₃ , Aw₂) , Bw₃)) = (A .F-hom (w→w₂⊗w₃ ⋆⟨ W ⟩ proj₁) Aw₂) , (B .F-hom (w→w₂⊗w₃ ⋆⟨ W ⟩ proj₂) Bw₃)
            to (coeq a i) = {!   !}
            to (squash x x₁ p q i i₁) = {!   !}

            -- no, not an injection
            fro : (A ×P B) .F-ob w .fst → (A ⨂ᴰᵥ B) .F-ob w .fst
            fro (Aw , Bw) = SetCoequalizer.inc ((w , w) , (((((rec (λ x → x) (λ x → x)) , {!   !}) , {!   !}) , {!   !}) , Aw) , Bw)
            -}

        -- show monomorphism (should be injective)
        sepProd : {A B : ob 𝒱} → value (A ⨂ᴰᵥ B) (A ×P B)
        sepProd {A}{B}= natTrans  α{!   !} where 
            α : N-ob-Type (A ⨂ᴰᵥ B) (A ×P B)
            α w (SetCoequalizer.inc ((w₂ , w₃) , (w→w₂⊗w₃ , Aw₂) , Bw₃)) = (A .F-hom (w→w₂⊗w₃ ⋆⟨ W ⟩ proj₁) Aw₂) , (B .F-hom (w→w₂⊗w₃ ⋆⟨ W ⟩ proj₂) Bw₃) where 
                open SemicartesianStrictMonCat semimon
            α w (coeq a i) = {!   !}
            α w (squash x x₁ p q i i₁) = {!   !}

        open NatTrans
        {- Γ → A ⊸ B 
        ≅ Γ * A → B 
          Γ , A → B 
        -}
        alternate : {Γ A : ob 𝒱}{B : ob 𝒞} → computation Γ (sep A B) → computation (Γ ×P  A) B
        alternate {Γ}{A}{B} record { α = α } = record { α = goal } where 
            open SemicartesianStrictMonCat semimon

            goal : (w : ob W) → SET ℓ [ (Γ ×P  A) .F-ob w , B .F-ob w ]
            goal w (Γw , Aw) = B .F-hom proj₁ (α w Γw w Aw) -- proj₁ is arbitrary choice

        sepIntro' : {Γ A : ob 𝒱}{B : ob 𝒞} → computation Γ (sep A B) → computation (Γ ⨂ᴰᵥ A) B
        sepIntro' {Γ} {A} {B} record { α = α } = record { α = goal } where 
            goal : (w : ob W) → SET ℓ [ (Γ ⨂ᴰᵥ A) .F-ob w , B .F-ob w ]
            goal w x = B .F-hom proj₁ close where -- proj₁ is arbitrary choice
                open SemicartesianStrictMonCat semimon
                p : fst ((Γ ×P A) .F-ob w)
                p = sepProd .N-ob w x

                close : B .F-ob (_⨂_ .F-ob (w , w)) .fst 
                close = α w (fst p) w (snd p) 
            
            {-(SetCoequalizer.inc ((w₂ , w₃) , (w→w₂⊗w₃ , Γw₂) , Aw₃)) = working where 
                open SemicartesianStrictMonCat semimon

                postulate w₂⊗w₃→w : W [ (_⨂_ .F-ob (w₂ , w₃))  , w ]

                alternate = B .F-hom w₂⊗w₃→w (α w₂ Γw₂ w₃ Aw₃)

                -- arbitrary choice of inl hiden in proj₁
                working = B .F-hom proj₁ (α w (Γ .F-hom (w→w₂⊗w₃ ⋆⟨ W ⟩ proj₁) Γw₂) w (A .F-hom (w→w₂⊗w₃ ⋆⟨ W ⟩ proj₂) Aw₃)) 

                Γw = (Γ .F-hom (w→w₂⊗w₃ ⋆⟨ W ⟩ proj₁) Γw₂)
                Aw = (A .F-hom (w→w₂⊗w₃ ⋆⟨ W ⟩ proj₂) Aw₃)
                whatif = {! α w Γw emptymap  !}
                
            goal w (coeq a i) = {!   !}
            goal w (squash c c₁ p q i i₁) = {!   !}        -}

        sepUP : {Γ A : ob 𝒱}{B : ob 𝒞} → Iso (computation (Γ ⨂ᴰᵥ A) B) (computation Γ (sep A B))
        sepUP {Γ}{A}{B}= iso 
                    sepIntro 
                    sepIntro'
                    (λ{record { α = α } → comp≡ (funExt λ w → funExt λ Γw → funExt λ w' → funExt λ Aw' → {!  refl !}) })
                    (λ{record { α = α } → comp≡ (funExt λ w → funExt λ {(SetCoequalizer.inc ((w₂ , w₃) , (w→w₂⊗w₃ , Γw₂) , Aw₃)) → {!  refl!}
                                                                      ; (coeq a i) → {!   !}
                                                                      ; (squash x x₁ p q i i₁) → {!   !}}) })

        -- morphism in the day convolution is the wrong direction..?
        -- day convolution needed in the computation category?
        sepElim : {Γ Δ A : ob 𝒱}{B : ob 𝒞} → 
            computation Γ (sep A B) → 
            value Δ A → 
            computation (Γ ⨂ᴰᵥ Δ) B 
        sepElim {Γ}{Δ}{A}{B} record { α = α } (natTrans N-ob N-hom) = record { α = goal } where 

            goal : (w : ob W) → SET ℓ [ (Γ ⨂ᴰᵥ Δ) .F-ob w , B .F-ob w ] 
            goal w (SetCoequalizer.inc ((w₂ , w₃) , (w→w₂⊗w₃ , Γw₂) , Δw₃)) = goal' where
                open SemicartesianStrictMonCat semimon
                -- instead of..
                --  B .F-hom w₂⊗w₃→w (α w₂ Γw₂ w₃ (N-ob w₃ Δw₃))
                -- since we don't have w₂⊗w₃→w ..
                w⊗w→w : W [ (_⨂_ .F-ob (w , w)) , w ]
                w⊗w→w  = proj₁ 
                -- This is an arbitrary choice between inl and inr... which feels wrong

                w→w₂ : W [ w , w₂ ]
                w→w₂ = w→w₂⊗w₃ ⋆⟨ W ⟩ proj₁

                w→w₃ : W [ w , w₃ ]
                w→w₃ = w→w₂⊗w₃ ⋆⟨ W ⟩ proj₂

                goal' : fst (B .F-ob w)
                goal' = B .F-hom w⊗w→w  (α w (Γ .F-hom w→w₂ Γw₂) w (N-ob w (Δ .F-hom w→w₃ Δw₃)))
                
            goal w (coeq ((w₂ , w₃) , (w₄ , w₅) , (w₄→w₂ , w₅→w₃) , (w→w₄⊗w₅ , Γw₂) , Δw₃) i) = goal' where 
            
                goal' : fst (B .F-ob w)
                goal' = B .F-hom {! hmm  !} {! α w Γw w Aw!}
            goal w (squash c c₁ p q i i₁) = {!   !} 

        -- no
        sepElim' : {Γ Δ A : ob 𝒱}{B : ob 𝒞} → 
            computation' Γ (sep A B) → 
            value Δ A → 
            computation' (Γ ⨂ᴰᵥ Δ) B 
        sepElim' {Γ} {Δ} {A} {B} (natTrans N-ob-c N-hom-c) (natTrans N-ob-v N-hom-v) = natTrans α {!   !} where 
            open SemicartesianStrictMonCat semimon
            α : N-ob-Type (F .F-ob (Γ ⨂ᴰᵥ Δ)) B
            α w (w₂ , w₂→w , SetCoequalizer.inc ((w₃ , w₄) , (w₂→w₃⊗w₄ , Γw₃) , Δw₄)) = goal' where 

                a1 : fst (F .F-ob Γ .F-ob w₂ )
                a1 = w₂ , ((W .id) , (Γ .F-hom (w₂→w₃⊗w₄ ⋆⟨ W ⟩ proj₁) Γw₃))

                a2 : fst( A .F-ob w₂ )
                a2 = N-ob-v w₂ (Δ .F-hom (w₂→w₃⊗w₄ ⋆⟨ W ⟩ proj₂) Δw₄)

                goal' : fst (B .F-ob w) 
                goal' = B .F-hom (proj₁ ⋆⟨ W ⟩ w₂→w) (N-ob-c w₂ a1 w₂ a2 )

            α w (w₂ , w₂→w , coeq a i) = {!   !}
            α w (w₂ , w₂→w , squash snd₁ snd₂ p q i i₁) = {!   !}

        thunk : {Γ : ob 𝒱}{B : ob 𝒞} → computation Γ B → value Γ (U .F-ob B)
        thunk {Γ}{B} record { α = α } = natTrans (λ{w Γw → record { fun = λ w' f → α w' (Γ .F-hom f Γw) }}) {!   !} 

        force : {Γ : ob 𝒱}{B : ob 𝒞} → value Γ (U .F-ob B) → computation Γ B 
        force {Γ} {B} (natTrans N-ob N-hom) = record { α = goal } where 
            goal : (w : ob W) → SET ℓ [ Γ .F-ob w , B .F-ob w ]
            goal w Γw = huh (N-ob w Γw) where 
                huh : fst (U .F-ob B .F-ob w) → fst (B .F-ob w)
                huh record { fun = fun } = fun w (W .id)

        thunk' : {Γ : ob 𝒱}{B : ob 𝒞} → computation' Γ B → value Γ (U .F-ob B)
        thunk' {Γ} {B} (natTrans N-ob N-hom) = natTrans α λ f → {!   !} where 
            α : N-ob-Type Γ (U .F-ob B)
            α w Γw = record { fun = goal } where 
                goal : (w₂ : ob W) → W [ w₂ , w ] →  B .F-ob w₂ .fst 
                goal w₂ w₂→w = N-ob w₂ (w₂ , (W .id , Γ .F-hom w₂→w Γw))

        return : {Γ A : ob 𝒱} → value Γ A → computation Γ (F .F-ob A) 
        return (natTrans N-ob N-hom) = record { α = λ w Γw → w , W .id , N-ob w Γw }
    
        return' : {Γ A : ob 𝒱} → value Γ A → computation' Γ (F .F-ob A) 
        return' {Γ}{A}(natTrans N-ob N-hom) = natTrans (λ{w (w' , w'→w , Γw') → w' , (w'→w , (N-ob w' Γw')) }) λ f → refl

        OSumElim : {A : SynTy'}{Γ : ob 𝒱}{B : ob 𝒞} → 
            value Γ (Case A) →
            value Γ OSum → 
            computation (Γ ×P tys A) B → 
            computation Γ B → 
            computation Γ B
        OSumElim {A}{Γ}{B}(natTrans Vt N-hom) 
                (natTrans V N-hom₁) 
                record { α = M } 
                record { α = N } = record { α = goal } where 

                    goal : (w : ob W) → (SET ℓ) [ Γ .F-ob w , B .F-ob w ]
                    goal w Γw = goal' where
                        open import Cubical.Foundations.Equiv
                        open import Cubical.Foundations.Isomorphism
                        open Iso
                        
                        osum : fst (OSum .F-ob w)
                        osum = V w Γw

                        case : fst( (Case A) .F-ob w )
                        case = Vt w Γw
                        
                        -- why is this red?
                        -- see src.sandbox... no red there
                        goal' : fst (B .F-ob w)
                        goal' with (isDecProp≡ (w .fst .fst) (case .fst) (osum .fst) )
                        ... | false , _ = N w Γw
                        ... | true , eq = M w (Γw , a) where 
                            eqtag : case .fst ≡ osum .fst 
                            eqtag = equivToIso eq .inv tt

                            prf : (snd w (fst osum)) ≡ A 
                            prf = cong (λ x → snd w x) (sym eqtag) ∙ case .snd .lower 

                            eqty : ((tys (snd w (fst osum)) ) .F-ob w) .fst ≡ ((tys A) .F-ob w) .fst
                            eqty = cong (λ x → fst ((tys x) .F-ob w)) prf

                            a : fst (F-ob (tys A) w)
                            a = transport eqty (osum .snd)   


        _⊹p_ : ob 𝒱 → ob 𝒱 → ob 𝒱 
        (x ⊹p y) .F-ob  w = ((x .F-ob w .fst) ⊎ y .F-ob w .fst) , {!   !}
        (x ⊹p y) .F-hom {w1}{w2} f (inl x₁) = inl (x .F-hom f x₁)
        (x ⊹p y) .F-hom {w1}{w2} f (inr y₁) = inr (y .F-hom f y₁)
        (x ⊹p y) .F-id = {!   !}
        (x ⊹p y) .F-seq = {!   !}
        
        c2c : {A : ob 𝒱}{B : ob 𝒞} → computation A B → Comp A B 
        c2c record { α = α } = α

        theTest : ∀(ty : SynTy') → value Termᵛ OSum → value Termᵛ (Case ty) → Comp Termᵛ ((funty OSum (sep (Case ty) (F .F-ob (tys ty ⊹p Termᵛ)))))
        theTest ty osum cas = goal where 
            open computation
            goal : Comp Termᵛ (funty OSum (sep (Case ty) (F .F-ob (tys ty ⊹p Termᵛ))))
            goal w ttt (σ₁ , e) w' (σ₂ , prf) = {! OSumElim {ty} {Termᵛ} {(F .F-ob (tys ty ⊹p Termᵛ))} cas osum ? ?  !} where
                -- we get to pick some future world w''
                -- such that we have some injective function w ⨂ w' → w''
                -- then we need to provide an element of [[ ty ]](w'')
                
                -- one possible option is to just choose w ⨂ w'
                w'' : ob W 
                w'' =  (_⨂_ .F-ob (w , w'))

                f : W [ w'' , (_⨂_ .F-ob (w , w')) ]
                f = W .id 

                -- can we use the OSum elim to get an element?
                M : value Termᵛ (Case ty)
                M = {!   !}
            _ = OSumElim {ty} {Termᵛ}{(F .F-ob (tys ty ⊹p Termᵛ))} {!   !} {!   !} {!   !} {!   !}
            
        Forall : ob 𝒱 
        Forall = {!   !}

        cant : ∀ (ty  : SynTy') → Comp Termᵛ (funty OSum (sep (Case ty) (F .F-ob (tys ty)))) 
        cant ty w tt* (σ₁ , e) w' (σ₂ , prf) = w'' , (f , goal) where 
            w'' : ob W 
            w'' =  {!   !}

            f : W [ w'' , (_⨂_ .F-ob (w , w')) ]
            f = {!   !}

            goal : tys ty .F-ob w'' .fst 
            goal = {!   !}
            
        -- without inspecting ty
        test' : ∀ (ty  : SynTy') → Comp Termᵛ (funty OSum (sep (Case ty) (F .F-ob (tys ty ⊹p Termᵛ)))) 
        test' ty w tt* (σ₁ , e) w' (σ₂ , prf) = w'' , (f , (inl goal)) where 
            
            -- ((_⨂_ .F-ob (w , w'))) , (W .id , inl {!   !} ) where --(tys ty .F-hom {!   !} {! e  !})) where 
            -- claim this should be the only allowed term (inr)
            --((_⨂_ .F-ob (w , w'))) , (W .id , inr (lift tt))
            -- so what do we know..

            {- 
                X --w-> SynTy

                Y --w'-> SynTy

                σ₁ : X 
                σ₂ : Y 

                e : [[ w(σ₁) ]]

                prf : w'(σ₂) ≡ ty

                w' should be a fresh world distinct from w
            
            -}
            -- we get to pick some future world w''
            -- such that we have some injective function w ⨂ w' → w''
            -- then we need to provide an element of [[ ty ]](w'')
            
            -- one possible option is to just choose w ⨂ w'
            w'' : ob W 
            w'' =  (_⨂_ .F-ob (w , w'))

            f : W [ w'' , (_⨂_ .F-ob (w , w')) ]
            f = W .id 

            open SemicartesianStrictMonCat semimon
            g : W [ w'' , w ]
            g = f ⋆⟨ W ⟩ proj₁

            h : W [ w'' , w' ]
            h = f ⋆⟨ W ⟩ proj₂

            ty' : SynTy' 
            ty' = (snd w σ₁)
       
            -- we can then lift element e into world w''
            lift-e : tys ty' .F-ob w'' .fst
            lift-e = tys ty' .F-hom g e

            -- we can also lift the tags / case symbols
            lift-σ₁ : w'' .fst .fst .fst 
            lift-σ₁ = g .fst .fst .fst σ₁

            lift-σ₂ : w'' .fst .fst .fst 
            lift-σ₂ = h .fst .fst .fst σ₂

            -- and the proof into world w''
            _ = {! g .snd  !}


            M : value Termᵛ (Case ty)
            M = {! tys ty .F-hom g   !}
            _ = OSumElim {ty} {Termᵛ}{(F .F-ob (tys ty ⊹p Termᵛ))} {!   !} {!   !} {!   !} {!   !}
            
            _ : w .fst .fst .fst
            _ = σ₁

            _ : w' .fst .fst .fst
            _ = σ₂
            

            _ : tys ty' .F-ob w .fst
            _ = e

            _ : snd w' σ₂ ≡ ty
            _ = prf .lower

            goal : tys ty .F-ob w'' .fst
            goal = {!   !}
            
        
