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
    open import src.cbpvmodel using (CBPVModel ; CBPVModelHom ; cbpv)
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
    

    com : (B B' : CTy)(Γ : Ctx)( k : Γ ◂ B ⊢k B')(Γ∙ : clCtx Γ) → GraphHom (dyn B) (dyn B') 
    com B B' Γ k γ = record { _$g_ = plug (ksubCtx γ k) ; _<$g>_ = prf }

    open CBPVModel
    open Category
    open Functor
    open NatTrans
    open EnrichedFunctor
    open CBPVModelHom 

    semtm : Type → Functor (SET ℓ-zero ^op) (SET ℓ-zero) 
    semtm A .F-ob (Γ , _)= (Γ → A) , {!   !}
    semtm A .F-hom  = _∘s_
    semtm A .F-id = refl
    semtm A .F-seq _ _ = refl

    semstk : (G H : Graph ℓ-zero ℓ-zero) → Functor (SET ℓ-zero ^op) (SET ℓ-zero) 
    semstk G H .F-ob (X , _)= (X → GraphHom G H) , {!   !}
    semstk G H .F-hom = _∘s_
    semstk G H .F-id = refl
    semstk G H .F-seq _ _ = refl
    
    E : EnrichedCategory (model.𝓟Mon (SET ℓ-zero)) ℓ-zero
    E .ob = Graph _ _
    E .Hom[_,_] = semstk
    E .id {G} =  natTrans (λ x x₁ x₂ → IdHom) λ _ → refl
    E .seq G H I = natTrans (λ{x (f , g) x₂ → f x₂ ⋆GrHom g x₂}) λ _ → refl
    E .⋆IdL G H = makeNatTransPath refl
    E .⋆IdR G H = makeNatTransPath refl
    E .⋆Assoc G H I J = makeNatTransPath refl

    semctm' : Graph ℓ-zero ℓ-zero → Functor (SET ℓ-zero ^op) (SET ℓ-zero) 
    semctm' G .F-ob (X , _) = (X → G .Node) , {!   !}
    semctm' G .F-hom = _∘s_
    semctm' G .F-id = refl
    semctm' G .F-seq _ _ = refl
    
    open import src.Data.PresheafCCC

    hrm : {G H : Graph ℓ-zero ℓ-zero} → NatTrans (semstk G H) (ExpOb (semctm' G) (semctm' H)) 
    hrm .N-ob (X , _) f = natTrans (λ {(Y , _) (g , h) y → f (lower g y) $g h y}) λ _ → refl
        -- f : X → GraphHom G H 
        -- h : Y → G .Node
        -- g : Y → X
        -- construct Y → H .Node
        -- use f (g y) : GraphHom G H 
        -- on  h y : G .Node
    hrm .N-hom f = funExt λ x → makeNatTransPath refl


    semctm : EnrichedFunctor (model.𝓟Mon (SET ℓ-zero)) ℓ-zero (ℓ-suc ℓ-zero) E (model.self (SET ℓ-zero))
    semctm .F₀ = semctm'
    semctm .F₁ = hrm
    semctm .Fid = makeNatTransPath refl
    semctm .Fseq = makeNatTransPath {!   !}

    sem : CBPVModel 
    sem .𝓒 = SET ℓ-zero
    sem .𝓔 = {!   !} --E
    sem .vTy = Set
    sem .vTm = semtm
    sem .TmB = {!   !} --semctm
    sem .emp = {!   !}
    sem ._×c_ = {!   !}
    sem .up×c = {!   !}

    denctx : Functor (𝓒 cbpv) (SET ℓ-zero) 
    denctx .F-ob Γ = clCtx Γ , {!   !}
    denctx .F-hom δ x = x ⋆⟨ (𝓒 cbpv) ⟩ δ
    denctx .F-id = refl
    denctx .F-seq f g = {! vsubseq  !}

    denty : vTy cbpv → Type 
    denty A = ⊘ ⊢v A

    dentm : (A : vTy cbpv) → NatTrans (vTm cbpv A) (semtm (denty A) ∘F (denctx ^opF)) 
    dentm A .N-ob Γ Γ⊢vA Γ∙ = vsub Γ∙ Γ⊢vA
    dentm A .N-hom γ = {!   !}

{-}
    denstk : EnrichedFunctor (model.𝓟Mon (𝓒 cbpv)) ℓ-zero ℓ-zero (𝓔 cbpv) (BaseChange denctx E)
    --(𝓔 sem))
    denstk .F₀ = dyn
    denstk .F₁ {B}{B'} = natTrans (com B B') λ f → {! refl  !}
    denstk .Fid = {!   !}
    denstk .Fseq = {!   !} 
    -}

    
    opsem : CBPVModelHom cbpv sem
    opsem .ctx = denctx
    opsem .ty = denty
    opsem .tm = dentm
    opsem .stk = {!   !} -- denstk
