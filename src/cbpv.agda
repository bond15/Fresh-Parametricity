-- for enriched functor def
module src.cbpv where 
    open import Cubical.Categories.Category
    open import Cubical.Foundations.Prelude
    open import Cubical.Foundations.HLevels 
    open import Cubical.Categories.Monoidal.Base
    open import Cubical.Categories.Monoidal.Enriched
    open import Cubical.Categories.Presheaf
    open import Cubical.Categories.Presheaf.Constructions
    open import Cubical.Categories.NaturalTransformation
    open import Cubical.Categories.Functor
    open import Cubical.Categories.Instances.Sets
    open import Cubical.Categories.Constructions.BinProduct
    open import Cubical.Categories.Bifunctor.Redundant
    open import Cubical.Data.Unit
    open Category     
    open Functor
    open NatTrans
    open MonoidalCategory
    open MonoidalStr
    open TensorStr 
    open EnrichedCategory

    module _ (𝓒 : Category ℓ-zero ℓ-zero) where 

        𝓟 : Category (ℓ-suc ℓ-zero) ℓ-zero
        𝓟 = PresheafCategory 𝓒 ℓ-zero

        ⨂' : Bifunctor 𝓟 𝓟 𝓟
        ⨂' = PshProd {ℓ-zero}{ℓ-zero}{𝓒}{ℓ-zero}{ℓ-zero}

        ⨂ : Functor (𝓟 ×C 𝓟) 𝓟
        ⨂ = BifunctorToParFunctor {ℓ-suc ℓ-zero}{ℓ-zero}{𝓟}{ℓ-suc ℓ-zero}{ℓ-zero}{𝓟}{ℓ-suc ℓ-zero}{ℓ-zero}{𝓟} ⨂'
            --BifunctorToParFunctor {! PshProd  !}
            -- BifunctorToParFunctor

        𝟙 : ob 𝓟 
        𝟙 .F-ob _ = Unit , isSetUnit
        𝟙 .F-hom = λ _ _ → tt
        𝟙 .F-id = refl
        𝟙 .F-seq _ _ = refl

        𝓟Ten :  TensorStr 𝓟
        𝓟Ten . ─⊗─ = ⨂
        𝓟Ten .unit = 𝟙

        𝓟Mon' : MonoidalStr 𝓟 
        𝓟Mon' .tenstr = 𝓟Ten
        𝓟Mon' .α = {!   !}
        𝓟Mon' .η = {!   !}
        𝓟Mon' .ρ = {!   !}
        𝓟Mon' .pentagon = {!   !}
        𝓟Mon' .triangle = {!   !}

        𝓟Mon : MonoidalCategory _ _ 
        𝓟Mon .C = 𝓟
        𝓟Mon .monstr = 𝓟Mon'


        module cbpvsyn where 
            Ctx = ob 𝓒
            mutual 
                data CTy : Set where 
                    fun : VTy → CTy → CTy 
                    F : VTy → CTy 

                data VTy : Set where 
                    u : VTy 
                    prod : VTy → VTy → VTy 
                    U : CTy → VTy

            mutual 
                data _⊢v_  : Ctx → VTy →  Set where 

                data _⊢c_ : Ctx → CTy → Set where 
                    
                data _◂_⊢k_ : Ctx → CTy → CTy → Set where
                    varc : {Γ : Ctx}{B : CTy} → Γ ◂ B ⊢k B

            ksubCtx : {Γ Δ : Ctx}{B B' : CTy} → 𝓒 [ Δ , Γ ] → Γ ◂ B ⊢k B' → Δ ◂ B ⊢k B' 
            ksubCtx {Γ} {Δ} {B} {.B} γ varc = varc

            csubCtx : {Γ Δ : Ctx}{B : CTy} → 𝓒 [ Δ , Γ ] → Γ ⊢c B → Δ ⊢c B
            csubCtx = {!   !} 

        open cbpvsyn
        open import Cubical.Data.Prod

        stacks : CTy → CTy → ob 𝓟 
        stacks B B' .F-ob Γ = (Γ ◂ B ⊢k B') , {!   !}
        stacks B B' .F-hom {Γ}{Δ}= ksubCtx
        stacks B B' .F-id = {!   !}
        stacks B B' .F-seq = {!   !}

        -- uhm... why Agda..?
        {-# TERMINATING #-}
        id𝓔 : {B : CTy} → NatTrans 𝟙 (stacks B B) 
        id𝓔 .N-ob Γ tt = varc
        id𝓔 .N-hom {Γ}{Δ} γ = funExt λ{ tt → refl } -- basically, ksubCtx should be identity on 'varc'

        --stack composition
        stackcomp : {B₁ B₂ B₃ : CTy} → 𝓟 [ ⨂ .F-ob ((stacks B₁ B₂) , (stacks B₂ B₃)) , stacks B₁ B₃ ]
        stackcomp {B₁}{B₂}{B₃} .N-ob Γ = {! goal  !} where 
            -- the goal is essentially this.. just using stupid shitty SET hom with hlevels
            goal : (Γ ◂ B₁ ⊢k B₂) × (Γ ◂ B₂ ⊢k B₃) → Γ ◂ B₁ ⊢k B₃
            goal (k , k') = {!   !}
        stackcomp {B₁}{B₂}{B₃} .N-hom = {!   !}

        plug : {Γ : Ctx}{B B' : CTy} → Γ ◂ B ⊢k B' → Γ ⊢c B → Γ ⊢c B' 
        plug = {!   !}


        𝓔 : EnrichedCategory 𝓟Mon ℓ-zero
        𝓔 .ob = CTy
        𝓔 .Hom[_,_] = stacks
        𝓔 .id = id𝓔
        𝓔 .seq _ _ _ = stackcomp
        𝓔 .⋆IdL B B' = {!   !}
        𝓔 .⋆IdR = {!   !}
        𝓔 .⋆Assoc = {!   !}

        -- now for computation judgements Γ ⊢ M : B  

        open import src.Data.PresheafCCC

        open Bifunctor
        -- select the identity morphism on an object P
        {-# TERMINATING #-} -- again.. why
        selfid : {P : ob 𝓟} → NatTrans 𝟙 (ExpOb P P) 
        selfid {P} .N-ob Γ tt = natTrans (λ Δ → λ{(_ , x) → x}) λ _ → refl
        selfid {P} .N-hom γ = funExt λ {tt → makeNatTransPath refl}

        open import Cubical.Data.Sigma hiding(_×_)
        eval : (A B : ob 𝓟) → PshProd ⟅ ExpOb B A , B ⟆b ⇒ A
        eval A B = natTrans
                (λ{x (B→A , Bx) → B→A .N-ob x (lift (𝓒 .id) , Bx)}) 
                (λ f → funExt λ{(B→A , Bx) → 
                        cong₂ (B→A .N-ob) refl (≡-× (cong lift ((𝓒 .⋆IdL f) ∙(sym (𝓒 .⋆IdR f)))) refl) 
                        ∙ funExt⁻ (B→A .N-hom f) (lift (𝓒 .id) , Bx)})

        {-
            missing abstractions

            note 
                B^A x C^B  
            is iso to 
                C^B x B^A 
            and 
                C^B x B^A -> C^A 
            is iso to    
                C^B x B^A x A-> C

            this map is definable using eval      
                C^B x B^A x A -- id x eval --> C^B x B --eval --> C

        -}
        selfcomp : {P Q R : ob 𝓟} → 𝓟 [ PshProd ⟅ ExpOb P Q , ExpOb Q R ⟆b , ExpOb P R ] 
        selfcomp {P}{Q}{R} .N-ob Γ (f , g) = natTrans (λ Δ → λ{(γ , PΔ) → g .N-ob Δ (γ , f .N-ob Δ (γ , PΔ)) }) λ γ → funExt λ {(γ , px) → {! refl  !}}
        selfcomp .N-hom = {!   !}
        
        -- this should be a general constuction.. 
        -- if the carrier of the monoidal category if cartesian closed.. 
        -- then we have a self enrichment
        self : EnrichedCategory 𝓟Mon (ℓ-suc ℓ-zero)
        self .ob = ob 𝓟
        self .Hom[_,_] P Q = ExpOb {C = 𝓒} {ℓ-zero} P Q
        self .id = selfid
        self .seq P Q R = selfcomp
        self .⋆IdL = {!   !}
        self .⋆IdR = {!   !}
        self .⋆Assoc = {!   !}

        -- Γ ⊢ M : B
        TmB' : CTy → ob 𝓟 
        TmB' B .F-ob Γ = (Γ ⊢c B) , {!   !}
        TmB' B .F-hom = csubCtx
        TmB' B .F-id = {!   !}
        TmB' B .F-seq = {!   !}

        huh : (B B' : CTy) → NatTrans (stacks B B') (ExpOb (TmB' B) (TmB' B'))
        huh B B' .N-ob Γ Γ◂B⊢kB' = goal where 


            goal' : (Δ : ob 𝓒) → ((Lift (𝓒 [ Δ , Γ ] )) × Δ ⊢c B) → Δ ⊢c B'
            goal' Δ (γ , Δ⊢cB) = this where 

                -- note now we have 

                _ : Γ ◂ B ⊢k B' 
                _ = Γ◂B⊢kB'

                _ : Δ ⊢c B
                _ = Δ⊢cB 

                -- and we need this

                hm : Δ ◂ B ⊢k B' 
                hm = ksubCtx (γ .lower) Γ◂B⊢kB'

                this : Δ ⊢c B' 
                this = plug hm Δ⊢cB

                -- which is given by the plug operation..
                -- but we need to say that pluging and substitution commute in some way

            goal : (ExpOb (TmB' B) (TmB' B')) .F-ob Γ .fst
                --𝓟 [ PshProd ⟅ LiftF ∘F {!   !} , TmB' B ⟆b , TmB' B' ]
            goal = natTrans {!   !} {!   !}

            _ : (𝓟 [ PshProd ⟅ LiftF  ∘F ( 𝓒 [-, Γ ]) , (TmB' B) ⟆b , (TmB' B') ])
            _ = goal
            
        huh B B' .N-hom = {!   !}

        open EnrichedFunctor
        TmB : EnrichedFunctor 𝓟Mon ℓ-zero (ℓ-suc ℓ-zero) 𝓔 self 
        TmB .F₀ = TmB'
        TmB .F₁ {B} {B'} = huh B B'
        TmB .Fid = {!   !}
        TmB .Fseq = {!   !}


 