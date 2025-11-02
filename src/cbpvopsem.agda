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
    

    com : (B B' : CTy)( k : ⊘ ◂ B ⊢k B') → GraphHom (dyn B) (dyn B') 
    com B B' k = record { _$g_ = plug k ; _<$g>_ = prf }

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
    hrm .N-ob (X , _) f = natTrans (λ {(Y , _) (g , h) x₂ → f (lower g x₂) $g h x₂}) λ _ → refl
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

    mutual
        denvtm' : {A : VTy}{Γ : Ctx} → Γ ⊢v A → clCtx Γ → clvTy A 
        denvtm' (var i) γ = γ i
        denvtm' u γ = u
        denvtm' (pair x y) γ = pair (denvtm' x γ) ((denvtm' y γ))
        denvtm' (thunk x) γ = thunk (denctm' x γ)

        denctm' : {B : CTy}{Γ : Ctx} → Γ ⊢c B → clCtx Γ → clcTy B 
        denctm' (ret x) γ = ret (denvtm' x γ)
        denctm' (force x) γ = force (denvtm' x γ)
        denctm' (lam x) = {!   !}
        denctm' (app x y) γ = app (denctm' x  γ) (denvtm' y γ)
        denctm' (rec× x y) γ = rec× (denvtm' x γ) {! denctm'  !}
        denctm' (x >>=λx, y) = {!   !}

    dentm : (A : vTy cbpv) → NatTrans (vTm cbpv A) (semtm (denty A) ∘F (denctx ^opF)) 
    dentm A .N-ob Γ = denvtm' {A} {Γ}
    dentm A .N-hom = {!   !}

{-}
    denstk : EnrichedFunctor (model.𝓟Mon (𝓒 cbpv)) ℓ-zero ℓ-zero (𝓔 cbpv) (BaseChange denctx E)
    --(𝓔 sem))
    denstk .F₀ = dyn
    denstk .F₁ {B}{B'} = natTrans (λ Γ Γ◂B⊢kB' Γ∙ → {!  com B B'   !}) {!   !}
    denstk .Fid = {!   !}
    denstk .Fseq = {!   !} -}
    

    
    opsem : CBPVModelHom cbpv sem
    opsem .ctx = denctx
    opsem .ty = denty
    opsem .tm = dentm
    opsem .stk = {!   !} -- denstk

    {-
       record CBPVModelHom (M N : CBPVModel) : Set₂ where 
        private module M = CBPVModel M 
        private module N = CBPVModel N
        field 
            ctx : Functor M.𝓒 N.𝓒
            ty : M.vTy → N.vTy
            tm : (A : M.vTy) → NatTrans (M.vTm A) (N.vTm (ty A) ∘F (ctx ^opF)) 
        open model M.𝓒 {ℓ-zero}
        field
            stk : EnrichedFunctor 𝓟Mon ℓ-zero ℓ-zero  M.𝓔  (BaseChange ctx N.𝓔 )
    -}

{-
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
    E : {C : Category ℓ-zero ℓ-zero } → EnrichedCategory (model.𝓟Mon C) ℓ-zero
    E .ob = Graph _ _
    E .Hom[_,_] G H = const (GraphHom G H , {!   !})
    E .id {G} = natTrans (λ {_ tt* → IdHom}) λ _ → refl
    E .seq G H I = natTrans (λ{_ (f , g ) → f ⋆GrHom g }) λ f → refl
    E .⋆IdL G H = makeNatTransPath refl
    E .⋆IdR G H = makeNatTransPath refl
    E .⋆Assoc G H I J = makeNatTransPath refl


    open import Cubical.Categories.Presheaf

    semtm : Set → Presheaf (SET ℓ-zero) ℓ-zero 
    semtm A .F-ob Γ = (Γ .fst → A) , {!   !}
    semtm A .F-hom γ = γ ∘s_
    semtm A .F-id = {!   !}
    semtm A .F-seq = {!   !}


    semstk : Set → Set → Functor (SET ℓ-zero ^op) (SET ℓ-zero)
    semstk X Y .F-ob Γ = {! Graph  !}
    semstk X Y .F-hom = {!   !}
    semstk X Y .F-id = {!   !}
    semstk X Y .F-seq = {!   !}

{-}
    E : EnrichedCategory (model.𝓟Mon (SET ℓ-zero)) ℓ-zero 
    E .ob = Set
    E .Hom[_,_] = semstk
    E .id {X} = {!   !}
    E .seq X Y Z = {!   !}
    E .⋆IdL X Y = {!   !}
    E .⋆IdR X Y = {!   !}
    E .⋆Assoc X Y Z W = {!   !}
    -}
    
    sem : CBPVModel 
    sem .𝓒 = SET ℓ-zero -- C 
    sem .𝓔 = {! E  !} --E 
    sem .vTy = Set 
    sem .vTm = semtm
    sem .TmB = {!   !}
    sem .emp = {!   !}
    sem ._×c_ = {!   !}
    sem .up×c = {!   !}

    open import Cubical.Data.Nat
    open import Cubical.Data.Empty

    denty : vTy cbpv → Set 
    denty t = {!   !}

    denctx' : Ctx → hSet ℓ-zero 
    denctx' (zero , Γ) = ⊥ , {!  !}
    denctx' (suc n , Γ) = denctx' {! projC   !} .fst × denty (Γ (toFin n)) , {!   !}
    
    denctx : Functor (𝓒 cbpv) (SET ℓ-zero)
    denctx .F-ob = denctx'
    denctx .F-hom = {!   !}
    denctx .F-id = {!   !}
    denctx .F-seq = {!   !}

    open NatTrans

    dentm : (A : vTy cbpv) → NatTrans (vTm cbpv A) (semtm (denty A) ∘F (denctx ^opF))
    dentm A .N-ob Γ = {!   !}
    dentm A .N-hom = {!   !}

    open CBPVModelHom 
    opsem : CBPVModelHom cbpv sem 
    opsem .ctx = denctx
    opsem .ty = denty
    opsem .tm = dentm
    opsem .stk = {!   !}
 -}
  