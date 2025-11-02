{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --lossy-unification #-}
{-# OPTIONS --type-in-type #-}
module src.cbpvmodel where 
    open import Cubical.Categories.Category
    open import Cubical.Foundations.Prelude
    open import Cubical.Foundations.HLevels 
    open import Cubical.Categories.Monoidal.Base
    open import Cubical.Categories.Monoidal.Enriched
    open import Cubical.Categories.Presheaf
    open import Cubical.Categories.Presheaf.Constructions
    open import src.Data.PresheafCCC
    open import Cubical.Categories.Limits.Terminal
    open import Cubical.Categories.NaturalTransformation
    open import Cubical.Categories.Functor
    open import Cubical.Categories.Instances.Sets
    open import Cubical.Categories.Constructions.BinProduct
    open import Cubical.Categories.Bifunctor.Redundant
    open import Cubical.Categories.Limits.BinProduct
    open import Cubical.Foundations.Isomorphism
    open import Cubical.Data.Unit
    open import Cubical.Data.Sigma 
    open import src.cbpv
    open import PshMonoidal

    open Category     
    open Functor
    open Bifunctor
    open NatTrans
    open MonoidalCategory
    open StrictMonCategory
    open MonoidalStr
    open StrictMonStr
    open TensorStr 
    open EnrichedCategory
    open BinProduct

    yo : {C : Category ℓ-zero ℓ-zero} → ob C → Presheaf C ℓ-zero 
    yo {C} X = C [-, X ] 

    record CBPVModel : Set₂ where 
        field 
            𝓒 : Category ℓ-zero ℓ-zero 
        open model 𝓒 {ℓ-zero}
        field
            𝓔 : EnrichedCategory 𝓟Mon ℓ-zero
            vTy : Set 
            vTm : vTy → Presheaf 𝓒 ℓ-zero
            TmB : EnrichedFunctor 𝓟Mon  𝓔 self

            emp : Terminal 𝓒
            _×c_ : ob 𝓒 → vTy → ob 𝓒
            up×c : (Γ : ob 𝓒)(A : vTy) → yo {𝓒} (Γ ×c A) ≅ᶜ (yo {𝓒} Γ ×p vTm A)

    
    module _ {M N : CBPVModel} where 
        private module M = CBPVModel M 
        private module N = CBPVModel N
        open model M.𝓒 {ℓ-zero}

        open EnrichedFunctor
        foo : (ctx : Functor M.𝓒 N.𝓒) → EnrichedFunctor 𝓟Mon (BaseChange ctx (model.self N.𝓒))(model.self M.𝓒)
        foo ctx .F₀ = _∘F (ctx ^opF)
        foo ctx .F₁ = natTrans (λ{m f → natTrans (λ{ m' (g , h) → {! h m !}} ) {!   !}}) {!   !}
        foo ctx .Fid = {!   !}
        foo ctx .Fseq = {!   !}

    record CBPVModelHom (M N : CBPVModel) : Set₂ where 
        private module M = CBPVModel M 
        private module N = CBPVModel N
        field 
            ctx : Functor M.𝓒 N.𝓒
            ty : M.vTy → N.vTy
            tm : (A : M.vTy) → NatTrans (M.vTm A) (N.vTm (ty A) ∘F (ctx ^opF)) 
        open model M.𝓒 {ℓ-zero}
        field
            stk : EnrichedFunctor 𝓟Mon M.𝓔 (BaseChange ctx N.𝓔 )
            cmp : EnrichedNatTrans M.TmB (ecomp 𝓟Mon stk (ecomp 𝓟Mon (BaseChangeF ctx N.TmB) (foo {M}{N} ctx)))
            -- goal EnrichedFunctor (model.𝓟Mon M.𝓒) ℓ-zero ℓ-zero         M.𝓔 (model.self M.𝓒)
            -- have EnrichedFunctor (model.𝓟Mon N.𝓒) ℓ-zero (ℓ-suc ℓ-zero) N.𝓔 (model.self N.𝓒)
            --      EnrichedFunctor 𝓟Mon             ℓ-zero ℓ-zero        (BaseChange ctx N.𝓔) (BaseChange ctx (model.self N.𝓒))
            -- BaseChangeF ctx N.TmB not quite

            {-
                composition of enriched functors ..?
                    ctx : Functor M.𝓒 N.𝓒 
                Can we derive enriched functors
                    L : EFunctor M M.𝓔 (BaseChange ctx N.𝓔)
                        this is stk

                    R : EFunctor M (BaseChange ctx (model.self N.𝓒)) (model.self M.𝓒)

                    C : EFunctor M (BaseChange ctx N.𝓔) (BaseChange ctx (model.self N.𝓒))
                        this is (BaseChangeF ctx N.TmB)

                    then goal is 
                        L ∙ C ∙ R 
            -}


    𝓒 : Category ℓ-zero ℓ-zero 
    𝓒 .ob = Ctx
    𝓒 .Hom[_,_] = Sub[_,_]
    𝓒 .id = idsub
    𝓒 ._⋆_ = compsub
    𝓒 .⋆IdL γ = compsubid -- compsub idsub f ≡ f
    𝓒 .⋆IdR γ = refl -- compsub f idsub ≡ f
    𝓒 .⋆Assoc = compsubseq -- compsub (compsub γ δ) ρ ≡ compsub γ (compsub δ ρ)
    𝓒 .isSetHom = {!   !}

    open model 𝓒 {ℓ-zero}

    stacks : CTy → CTy → ob 𝓟 
    stacks B B' .F-ob Γ = (Γ ◂ B ⊢k B') , {!   !}
    stacks B B' .F-hom {Γ}{Δ}= ksubCtx
    stacks B B' .F-id = funExt λ x → ksubid -- ksubCtx idsub ≡ (λ x → x)
    stacks B B' .F-seq {Γ}{Δ}{Θ} γ δ = funExt λ _ → sym ksubseq
        -- ksubCtx (δ ∘ γ) ≡  ksubCtx δ ∘ ksubCtx γ

    -- uhm... why Agda..?
    {-# TERMINATING #-}
    id𝓔 : {B : CTy} → NatTrans 𝟙 (stacks B B) 
    id𝓔 .N-ob Γ tt* = varc
    id𝓔 .N-hom {Γ}{Δ} γ = funExt λ{ tt* → refl } 

    stackcomp : {B₁ B₂ B₃ : CTy} → 𝓟 [ ⨂ .F-ob ((stacks B₁ B₂) , (stacks B₂ B₃)) , stacks B₁ B₃ ]
    stackcomp .N-ob Γ (k , k')= scomp k k'
    stackcomp {B₁}{B₂}{B₃} .N-hom {Γ} γ  = funExt goal where 
        
        -- stack composition commutes with value context substitution
        goal : ((k , k') : (Γ ◂ B₁ ⊢k B₂) × (Γ ◂ B₂ ⊢k B₃)) →
                scomp (ksubCtx γ k) (ksubCtx γ k') ≡ ksubCtx γ (scomp k k')
        goal (k , k') = {!   !} 

    𝓔 : EnrichedCategory 𝓟Mon ℓ-zero
    𝓔 .ob = CTy
    𝓔 .Hom[_,_] = stacks
    𝓔 .id = id𝓔
    𝓔 .seq _ _ _ = stackcomp
    𝓔 .⋆IdL B B' = makeNatTransPath (funExt λ Γ → funExt λ {(tt* , Γ◂B⊢kB') → scompid}) -- Γ◂B⊢kB' ≡ scomp varc Γ◂B⊢kB' 
    𝓔 .⋆IdR B B' = makeNatTransPath (funExt λ Γ → funExt λ{(Γ◂B⊢kB' , tt*) → refl}) -- Γ◂B⊢kB' ≡ scomp Γ◂B⊢kB' varc
    𝓔 .⋆Assoc B₁ B₂ B₃ B₄ = makeNatTransPath (funExt λ Γ → funExt λ {(k₁ , (k₂ , k₃)) → scompseq {Γ}{B₁}{B₂}{B₃}{B₄}{k₁}{k₂}{k₃}}) -- scomp (scomp k₁ k₂) k₃ ≡ scomp k₁ (scomp k₂ k₃)


    -- now for computation judgements Γ ⊢ M : B  

    -- Γ ⊢ M : B
    TmB' : CTy → ob 𝓟 
    TmB' B .F-ob Γ = (Γ ⊢c B) , {!   !}
    TmB' B .F-hom = csub
    TmB' B .F-id = funExt λ _ → csubid
    TmB' B .F-seq {Γ}{Δ}{θ} γ δ = funExt λ Γ⊢cB → sym csubseq
        -- csub (δ ∘ γ) Γ⊢cB ≡ csub δ (csub γ Γ⊢cB)

    open EnrichedFunctor

    huh : (B B' : CTy) → NatTrans (stacks B B') ((TmB' B') ^ (TmB' B))
    huh B B' .N-ob Γ Γ◂B⊢kB' .N-ob Δ (lift γ , Δ⊢cB) = plug (ksubCtx γ Γ◂B⊢kB') Δ⊢cB
    huh B B' .N-ob Γ Γ◂B⊢kB' .N-hom {Δ}{θ} δ = funExt λ{ (lift γ , Δ⊢cB ) → {!   !}}
        -- plug (ksubCtx (δ ∘ γ) Γ◂B⊢kB') (csub δ Δ⊢cB) 
        --   ≡ 
        -- csub δ (plug (ksubCtx γ Γ◂B⊢kB') Δ⊢cB)
    huh B B' .N-hom {Γ}{Δ} γ = 
        funExt λ Γ◂B⊢kB' → makeNatTransPath (funExt λ θ → funExt λ{ (lift δ , θ⊢cB) → 
            cong (λ h → plug h θ⊢cB ) ksubseq })

           --  ksubCtx δ (ksubCtx γ Γ◂B⊢kB') ≡ ksuCtx (δ ∘ γ) Γ◂B⊢kB'
            

    TmB : EnrichedFunctor 𝓟Mon  𝓔 self 
    TmB .F₀ = TmB'
    TmB .F₁ {B} {B'} = huh B B' 
    TmB .Fid {B} = 
        makeNatTransPath (funExt λ Γ → funExt λ {tt* → 
            makeNatTransPath (funExt λ Δ → funExt λ{(lift γ , Δ⊢cB ) → refl })})
    TmB .Fseq {B₁}{B₂}{B₃} = 
        makeNatTransPath (funExt λ Γ → funExt λ{(k , k') → 
            makeNatTransPath (funExt λ Δ  → funExt λ{(lift γ , Δ⊢cB₁)→ {! funExt⁻ ?  Δ⊢cB₁  !}})})
    --  plug (ksubCtx γ k')
    --    (plug (ksubCtx γ k) Δ⊢cB₁)
    -- ≡ 
    --  plug (ksubCtx γ (scomp k k')) Δ⊢cB₁
    open import Cubical.Data.Fin.Recursive
    cbpv : CBPVModel 
    cbpv = record{ 
        𝓒 = 𝓒; 
        𝓔 = 𝓔; 
        vTy = VTy; 
        vTm = λ A → 
            record { 
                F-ob = λ Γ → (Γ ⊢v A) , {!   !} ; 
                F-hom = vsub; 
                F-id = funExt λ _ → vsubid ; 
                F-seq = λ f g  → funExt λ x → sym (vsubseq {γ = g}{f}{x}) }; 
        TmB = TmB; 
        emp = ⊘ , λ y → (λ () ), λ{x → {! x  !}} ; 
        _×c_ = _,,_; 
        up×c = λ Γ A → 
            record { 
                trans = natTrans (λ Δ → projC) λ f → refl ; 
                nIso = λ Δ → isiso pairC refl (funExt λ {γ → funExt λ {zero → refl
                                                                     ; (suc x) → refl}}) }}

 