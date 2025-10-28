{-# OPTIONS --type-in-type #-}
-- being lazy
module src.cbpvopsem where 
    open import Cubical.Categories.Instances.Sets
    open import Cubical.Categories.Category
    open import Cubical.Foundations.Prelude
    open import Cubical.Foundations.HLevels 
    open import Cubical.Categories.Monoidal.Base
    open import Cubical.Categories.Monoidal.Enriched
    open import Cubical.Data.Graph    
    open import Cubical.Categories.Functor
    open import Cubical.Categories.Displayed.Base   
    open import Cubical.Data.Fin.Recursive 
    open import Cubical.Categories.Instances.Sets
    open import Cubical.Categories.NaturalTransformation


    open import src.cbpv
    open import src.cbpvmodel using (CBPVModel )
    open import PshMonoidal 
    open EnrichedCategory 

    {-
        Question.. do we have initiality give the operational semantics...?
            and define the category with the structure in mind?

        or 
            define the structure of the category generically
            and expliclty give an small step as a functor...?
    -}
    open Categoryᴰ

    open import Cubical.Data.Unit
    open import Cubical.Data.Sigma

-- term operational semantics

    clvTy : VTy → Set 
    clvTy A = ⊘ ⊢v A

    clcTy : CTy → Set 
    clcTy B = ⊘ ⊢c B

    clCtx : Ctx → Set 
    clCtx = Sub[ ⊘ ,_]
    --(n , Γ) = (x : Fin n) → clvTy (Γ x)

    -- should this be defined for open terms..?
    data _↦_ : {B : CTy} → clcTy B → clcTy B → Set where 
        beta-lam : {B : CTy}{A : VTy}{v : ⊘ ⊢v A}{m : (⊘ ,, A) ⊢c B } → 
            app (lam m) v ↦ csub (λ {zero → v}) m
        beta-bind : {B : CTy}{A : VTy}{v : ⊘ ⊢v A}{m : (⊘ ,, A) ⊢c B } → 
            bind (ret v) m ↦ csub (λ{zero → v}) m
        beta-thunk : {B : CTy}{m : ⊘ ⊢c B} → 
            force (thunk m) ↦ m
        -- etc..


    -- missing cong rule
    -- options, E[force thunk m] ↦ E[m]
    -- or staging
    data _E↦_ : {B : CTy} → clcTy B → clcTy B → Set where 
        e-cong : {B B' : CTy}{k : ⊘ ◂ B ⊢k B'}{m n : ⊘ ⊢c B} → 
            m ↦ n → plug k m E↦ plug k n


    dyn : CTy → Graph _ _ 
    dyn B = record { Node = clcTy B ; Edge = _E↦_ }

    prf : {B B' : CTy}{k : ⊘ ◂ B ⊢k B'}{m n : clcTy B} → m E↦ n → plug k m E↦ plug k n 
    prf {B₁} {B₂} {k} (e-cong {B₃}{B₁}{k'} x) = {! subst  !}
       -- plug k (plug k' m) E↦ plug k (plug k' n)
    

    com : (B B' : CTy)( k : ⊘ ◂ B ⊢k B') → GraphHom (dyn B) (dyn B') 
    com B B' k = record { _$g_ = plug k ; _<$g>_ = prf }

    open CBPVModel
    open Category
    open Functor

    -- subcategory of closed contexts..?
    C : Category ℓ-zero ℓ-zero 
    C .ob = Σ[ Γ ∈ Ctx ] clCtx Γ 
    C .Hom[_,_] (γ , γ• )(δ , δ•) = {!   !}
    C .id = {!   !}
    C ._⋆_ = {!   !}
    C .⋆IdL γ = {!   !} -- compsub idsub f ≡ f
    C .⋆IdR γ = {!   !} -- compsub f idsub ≡ f
    C .⋆Assoc = {!   !} -- compsub (compsub γ δ) ρ ≡ compsub γ (compsub δ ρ)
    C .isSetHom = {!   !}

    Ehom : Graph _ _ → Graph _ _ → Functor (C ^op) (SET ℓ-zero) 
    Ehom G H .F-ob (Γ , Γ•)= GraphHom G H , {!   !}
    Ehom G H .F-hom = {!   !}
    Ehom G H .F-id = {!   !}
    Ehom G H .F-seq = {!   !}

    const : {C D : Category _ _ } → (X : ob D) → Functor C D 
    const X .F-ob _ = X
    const {C} {D} X .F-hom f = D .id
    const X .F-id = refl
    const {C} {D} X .F-seq _ _ = sym (⋆IdL D _)
    

    -- doesn't use the enrichment?
    E : EnrichedCategory (model.𝓟Mon C) ℓ-zero
    E .ob = Graph _ _
    E .Hom[_,_] G H = const (GraphHom G H , {!   !})
    E .id {G} = natTrans (λ {_ tt* → IdHom}) λ _ → refl
    E .seq G H I = natTrans (λ{_ (f , g ) → f ⋆GrHom g }) λ f → refl
    E .⋆IdL G H = makeNatTransPath refl
    E .⋆IdR G H = makeNatTransPath refl
    E .⋆Assoc G H I J = makeNatTransPath refl

    
    opsem : CBPVModel 
    opsem .𝓒 = C -- SET ℓ-zero
    opsem .𝓔 = {! E  !} --E
    opsem .vTy = {!   !} --Set
    opsem .vTm = {!   !}
    opsem .TmB = {!   !}
    opsem .emp = {!   !}
    opsem ._×c_ = {!   !}
    opsem .up×c = {!   !}
 

    {-


    --dyn : CTy → Graph _ _ 
   -- dyn (fun x x₁) = record { Node = {!   !} ; Edge = {!   !} }
   -- dyn (F x) = {!   !}
    
    mutual 
        elvty : VTy → Set 
        elvty one = Unit
        elvty (prod A A') = elvty A × elvty A'
        elvty (U B) = {!   !} 
        -- need syntax to be able to define reductions
        elcty : CTy → Graph _ _
        elcty (fun A B) = record { Node = {!   !} ; Edge = {!   !} }
        elcty (F A) = {!   !}

    𝓒+ : Categoryᴰ 𝓒 ℓ-zero ℓ-zero
    𝓒+ .ob[_] Γ = {!   !}
    𝓒+ .Hom[_][_,_] = {!   !}
    𝓒+ .idᴰ = {!   !}
    𝓒+ ._⋆ᴰ_ = {!   !}
    𝓒+ .⋆IdLᴰ  = {!   !}
    𝓒+ .⋆IdRᴰ = {!   !}
    𝓒+ .⋆Assocᴰ = {!   !}
    𝓒+ .isSetHomᴰ  = {!   !}
   -- C = SET ℓ-zero 

-}

{-}    open model C


    open CBPVModel
    open Functor

    huh : Functor (C ^op) C
    huh .F-ob = {!   !}
    huh .F-hom = {!   !}
    huh .F-id = {!   !}
    huh .F-seq = {!   !}

    E : EnrichedCategory (model.𝓟Mon C) ℓ-zero 
    E  .ob = Graph _ _
    E .Hom[_,_] G H = huh
    E .id = {!   !}
    E .seq = {!   !}
    E .⋆IdL = {!   !}
    E .⋆IdR = {!   !}
    E .⋆Assoc = {!   !}
    
    opsem : CBPVModel 
    opsem .𝓒 = C
    opsem .𝓔 = {!   !}
    opsem .vTy = {!   !}
    opsem .vTm = {!   !}
    opsem .TmB = {!   !}
    opsem .emp = {!   !}
    opsem ._×c_ = {!   !}
    opsem .up×c = {!   !}
    -}

