-- for enriched functor def
module src.cbpvmodel where 
    open import Cubical.Categories.Category
    open import Cubical.Foundations.Prelude
    open import Cubical.Foundations.HLevels 
    open import Cubical.Categories.Monoidal.Base
    open import Cubical.Categories.Monoidal.Enriched
    open import Cubical.Categories.Presheaf
    open import Cubical.Categories.Presheaf.Constructions
    open import src.Data.PresheafCCC
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


    𝓒 : Category ℓ-zero ℓ-zero 
    𝓒 .ob = Ctx
    𝓒 .Hom[_,_] = Sub[_,_]
    𝓒 .id = idsub
    𝓒 ._⋆_ = compsub
    𝓒 .⋆IdL f = {! csubid  !} -- compsub idsub f ≡ f
    𝓒 .⋆IdR f = {!   !} -- compsub f idsub ≡ f
    𝓒 .⋆Assoc γ δ ρ = {!   !} -- compsub (compsub γ δ) ρ ≡ compsub γ (compsub δ ρ)
    𝓒 .isSetHom = {!   !}

    open model 𝓒 {ℓ-zero}

    stacks : CTy → CTy → ob 𝓟 
    stacks B B' .F-ob Γ = (Γ ◂ B ⊢k B') , {!   !}
    stacks B B' .F-hom {Γ}{Δ}= ksubCtx
    stacks B B' .F-id = {!   !} -- ksubCtx idsub ≡ (λ x → x)
    stacks B B' .F-seq {Γ}{Δ}{Θ} γ δ = {!   !}
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
        goal = {!   !} 

    𝓔 : EnrichedCategory 𝓟Mon ℓ-zero
    𝓔 .ob = CTy
    𝓔 .Hom[_,_] = stacks
    𝓔 .id = id𝓔
    𝓔 .seq _ _ _ = stackcomp
    𝓔 .⋆IdL B B' = makeNatTransPath (funExt λ Γ → funExt λ {(tt* , Γ◂B⊢kB') → scompid}) -- Γ◂B⊢kB' ≡ scomp varc Γ◂B⊢kB' 
    𝓔 .⋆IdR B B' = makeNatTransPath (funExt λ Γ → funExt λ{(Γ◂B⊢kB' , tt*) → refl}) -- Γ◂B⊢kB' ≡ scomp Γ◂B⊢kB' varc
    𝓔 .⋆Assoc _ _ _ _ = makeNatTransPath (funExt λ Γ → funExt λ {(k₁ , (k₂ , k₃)) → {!   !}}) -- scomp (scomp k₁ k₂) k₃ ≡ scomp k₁ (scomp k₂ k₃)


    -- now for computation judgements Γ ⊢ M : B  

    -- Γ ⊢ M : B
    TmB' : CTy → ob 𝓟 
    TmB' B .F-ob Γ = (Γ ⊢c B) , {!   !}
    TmB' B .F-hom = csub
    TmB' B .F-id = funExt λ _ → csubid
    TmB' B .F-seq {Γ}{Δ}{θ} γ δ = funExt λ Γ⊢cB → {!   !}
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
            {!   !} })
        -- plug (ksubCtx δ (ksubCtx γ Γ◂B⊢kB')) θ⊢cB 
        --  ≡
        -- plug (ksubCtx (δ ∘ γ) Γ◂B⊢kB') θ⊢cB


    TmB : EnrichedFunctor 𝓟Mon ℓ-zero (ℓ-suc ℓ-zero) 𝓔 self 
    TmB .F₀ = TmB'
    TmB .F₁ {B} {B'} = huh B B' 
    TmB .Fid {B} = 
        makeNatTransPath (funExt λ Γ → funExt λ {tt* → 
            makeNatTransPath (funExt λ Δ → funExt λ{(lift γ , Δ⊢cB ) → refl })})
    TmB .Fseq {B₁}{B₂}{B₃} = 
        makeNatTransPath (funExt λ Γ → funExt λ{(k , k') → 
            makeNatTransPath (funExt λ Δ  → funExt λ{(lift γ , Δ⊢cB₁)→ {!   !}})})
    --  plug (ksubCtx (λ i → vsub var (γ i)) k')
    --    (plug (ksubCtx (λ i → vsub var (γ i)) k) Δ⊢cB₁)
    -- ≡ 
    --  plug (ksubCtx γ (scomp k k')) Δ⊢cB₁
