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
            and expliclty give a small step operational semantics as a functor...?
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

    lemma : {B₁ B₂ B₃ : CTy}{k : ⊘ ◂ B₁ ⊢k B₂}{k' : ⊘ ◂ B₂ ⊢k B₃} → 
        plug (scomp k k') ≡ (plug k ∘s plug k')
    lemma {k' = varc} = refl
    lemma {B₁}{B₂}{B₃}{k}{∙V x k'} = funExt λ m → cong₂ app (funExt⁻ (lemma{k = k}{k'}) m) refl
    lemma {B₁}{B₂}{B₃}{k}{k' = x←∙:M k' x} = funExt λ m → cong₂ bind (funExt⁻ (lemma{k = k}{k'}) m) refl
    
    prf : {B B' : CTy}{k : ⊘ ◂ B ⊢k B'}{m n : clcTy B} → m E↦ n → plug k m E↦ plug k n 
    prf {B₁} {B₂} {k} (e-cong {B₃}{B₁}{k'}{m}{n} x) = goal where 
        goal' : plug (scomp k' k) m E↦ plug (scomp k' k) n
        goal' = e-cong {k = scomp k' k} x

        goal : plug k (plug k' m) E↦ plug k (plug k' n) 
        goal = subst2 (_E↦_) (funExt⁻ (lemma {k = k'}{k}) m) ((funExt⁻ (lemma {k = k'}{k}) n)) goal' 
    

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
    C .⋆IdL γ = {!   !} 
    C .⋆IdR γ = {!   !} 
    C .⋆Assoc = {!   !} 
    C .isSetHom = {!   !}

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
    opsem .𝓒 = {!   !} -- C 
    opsem .𝓔 = {!   !} --E 
    opsem .vTy = {!   !} 
    opsem .vTm = {!   !}
    opsem .TmB = {!   !}
    opsem .emp = {!   !}
    opsem ._×c_ = {!   !}
    opsem .up×c = {!   !}
 
 