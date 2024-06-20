{-# OPTIONS --allow-unsolved-metas  --lossy-unification #-}

module src.Models.WithoutWeakening.Denotation {ℓS} where
    
    open import Cubical.Foundations.HLevels hiding (extend)
    open import Cubical.Foundations.Prelude    
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

    open import src.Models.WithoutWeakening.Base {ℓS}
    
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

        inremb : {ℓ : Level}{A B : Type ℓ} → isEmbedding (inr {ℓ}{ℓ}{A}{B})
        inremb = {!   !}
        
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

        -- function type
        fun : ob 𝒱 → ob 𝒞 → ob 𝒞 
        fun A B .F-ob w = (SET ℓ)[ A .F-ob w , B .F-ob w ] , (SET ℓ) .isSetHom
        fun A B .F-hom f g Ay = (B .F-hom f) (g ((A .F-hom f) Ay)) 
        fun A B .F-id = funExt λ g → funExt λ a → 
            B .F-hom (id W) (g (A .F-hom (id W) a)) ≡⟨ funExt⁻  (B .F-id) _ ⟩
            (g (A .F-hom (id W) a)) ≡⟨ cong g (funExt⁻ (A .F-id) _) ⟩ 
            g a ∎
        fun A B .F-seq f g = funExt λ h → funExt λ Az → funExt⁻ (B .F-seq f g) _ ∙ 
            cong (λ x → seq' (SET ℓ) (F-hom B f) (F-hom B g) (h x)) (funExt⁻ (A .F-seq _ _) _)

        -- separating function type
        sep : ob 𝒱 → ob 𝒞 → ob 𝒞 
            -- should be an end ?
        sep A B .F-ob w = (∀ (w' : ob W) → (SET ℓ)[ A .F-ob w' , B .F-ob (_⨂_ .F-ob (w , w')) ]) , isSetΠ  λ _ → (SET ℓ) .isSetHom
        sep A B .F-hom {w₁}{w₂} w₁→w₂ end w₃ Aw₃ = B .F-hom (_⨂_ .F-hom (w₁→w₂ , W .id)) (end w₃ Aw₃)
        sep A B .F-id = funExt λ end → funExt λ w₃  → funExt λ Aw₃ → cong (λ x → (B .F-hom x) (end w₃ Aw₃) ) (_⨂_ .F-id) ∙ funExt⁻ (B .F-id) ((end w₃ Aw₃))
        sep A B .F-seq f g = funExt λ end → funExt λ w₃  → funExt λ Aw₃ → {! funExt⁻ (B .F-seq _ _) _ ∙ ?  !}
        -- cong (λ x → (B .F-hom x) (end w₃ Aw₃) ) {! _⨂_ .F-seq _ _  !} ∙ funExt⁻ (B .F-seq _ _ ) ((end w₃ Aw₃))

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
            goal w₁ Γw₁ = B .F-hom w₁→w₁⊗w₂ (α w₁⊗w₂ ((SetCoequalizer.inc ((w₁ , w₂) , ((W .id , Γw₁) , casew₂)))) )where
                -- this still doesnt work 
                -- α w₁ (SetCoequalizer.inc ((w₁ , w₂) , (({!   !} , Γw₁) , casew₂))) where
                -- since 
                -- w₁⊎w₂ → w₁ DNE

                w₂ : ob W 
                w₂ = (Unit*Fin , tt*) , (λ{tt* → ty})

                w₁⊗w₂ : ob W 
                w₁⊗w₂ = _⨂_ .F-ob (w₁ , w₂)

                w₁→w₁⊗w₂ : W [ w₁ , w₁⊗w₂ ]
                w₁→w₁⊗w₂ = ((inl , inlemb) , refl) , refl

                casew₂ : fst (Case ty ⟅ w₂ ⟆)
                casew₂ = tt* , (lift refl) 

        -- fun Intro
        funIntro : {Γ A : ob 𝒱}{B : ob 𝒞} → computation (Γ ×P A) B → computation Γ (fun A B) 
        funIntro {Γ} {A} {B} record { α = α } = record { α = λ w Γw Aw → α w (Γw , Aw) }

        funElim : {Γ Δ A : ob 𝒱}{B : ob 𝒞} → 
            computation Γ (fun A B) → 
            value Δ A → 
            computation (Γ ×P Δ) B 
        funElim record { α = α } (natTrans N-ob N-hom) = record { α = λ{ w (Γw , Δw) → α w Γw (N-ob w Δw) }}

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
        sepProdElim₁ M = M ⋆⟨ 𝒱 ⟩ {!   !}  -- no longer have semicartesian projection

        sepIntro :  {Γ A : ob 𝒱}{B : ob 𝒞} → computation (Γ ⨂ᴰᵥ A) B → computation Γ (sep A B) 
        sepIntro record { α = α } = record { α = λ w Γw w' Aw' → α (_⨂_ .F-ob (w , w')) (SetCoequalizer.inc ((w , w') , (((((λ x → x) , snd (id↪ _)) , refl) , refl) , Γw) , Aw')) }

        -- morphism in the day convolution is the wrong direction..?
        -- day convolution needed in the computation category?
        sepElim : {Γ Δ A : ob 𝒱}{B : ob 𝒞} → 
            computation Γ (sep A B) → 
            value Δ A → 
            computation (Γ ⨂ᴰᵥ Δ) B 
        sepElim {Γ}{Δ}{A}{B} record { α = α } (natTrans N-ob N-hom) = record { α = goal } where 

            goal : (w : ob W) → SET ℓ [ (Γ ⨂ᴰᵥ Δ) .F-ob w , B .F-ob w ] 
            goal w (SetCoequalizer.inc ((w₂ , w₃) , (w₂⊗w₃→w , Γw₂) , Δw₃)) = goal' where
                -- (SetCoequalizer.inc ((w₂ , w₃) , (w→w₂⊗w₃ , Γw₂) , Δw₃))
                w₂→w : W [ w₂ , w ]
                w₂→w = (((inl , inlemb) , refl) , refl) ⋆⟨ W ⟩ w₂⊗w₃→w

                w₃→w : W [ w₃ , w ]
                w₃→w = (((inr , inremb) , refl) , refl) ⋆⟨ W ⟩ w₂⊗w₃→w

                -- still an arbitrary choice
                w→w⊗w : W [ w , (_⨂_ .F-ob (w , w)) ]
                w→w⊗w  = ((inl , inlemb) , refl) , refl

                goal' : fst (B .F-ob w)
                goal' = B .F-hom w→w⊗w (α w (Γ .F-hom w₂→w Γw₂) w (N-ob w (Δ .F-hom w₃→w Δw₃))) 
                     -- B .F-hom w⊗w→w (α w (Γ .F-hom w→w₂ Γw₂) w (N-ob w (Δ .F-hom w→w₃ Δw₃)))
                
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
            α : N-ob-Type (F .F-ob (Γ ⨂ᴰᵥ Δ)) B
            α w (w₂ , w₂→w , SetCoequalizer.inc ((w₃ , w₄) , (w₂→w₃⊗w₄ , Γw₃) , Δw₄)) = goal' where 
                {-}
                a1 : fst (F .F-ob Γ .F-ob w₂ )
                a1 = w₂ , ((W .id) , (Γ .F-hom (w₂→w₃⊗w₄ ⋆⟨ W ⟩ proj₁) Γw₃))

                a2 : fst( A .F-ob w₂ )
                a2 = N-ob-v w₂ (Δ .F-hom (w₂→w₃⊗w₄ ⋆⟨ W ⟩ proj₂) Δw₄)
                -}
                goal' : fst (B .F-ob w) 
                goal' = {!   !} -- B .F-hom (proj₁ ⋆⟨ W ⟩ w₂→w) (N-ob-c w₂ a1 w₂ a2 )

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
                goal : (w₂ : ob W) → W [ w , w₂ ] →  B .F-ob w₂ .fst 
                goal w₂ w→w₂ = N-ob w₂ (w₂ , (W .id , Γ .F-hom w→w₂ Γw))
              --goal w₂ w₂→w = N-ob w₂ (w₂ , (W .id , Γ .F-hom w₂→w Γw))

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
 
            
