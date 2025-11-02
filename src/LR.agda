{-# OPTIONS --type-in-type #-}
-- only used in LR 
module src.LR where
    -- compare this to src.Data.STLC in this repo 


    open import Cubical.Data.Unit 
    open import Cubical.Data.Sigma
    open import Cubical.Categories.Category
    open import Cubical.Foundations.Prelude
    open import Cubical.Foundations.HLevels 
    open import Cubical.Categories.Functor
    open import Cubical.Categories.Instances.Sets
    open import Cubical.Categories.Profunctor
    open import Cubical.Categories.Constructions.BinProduct
    open import Cubical.Categories.NaturalTransformation hiding (_⟦_⟧)
    open import Cubical.Categories.NaturalTransformation.Base hiding (_⟦_⟧)
    open import Cubical.Categories.Presheaf
    open import Cubical.Categories.Presheaf.Constructions
    open import Cubical.Categories.Limits.Terminal 
    open import Cubical.Categories.Displayed.Base   
    open import Cubical.Categories.Constructions.TotalCategory 
    open Category     
    open Functor
    open NatTrans
    open NatIso
    open isIso
    _⋆'_ : {A B C : Set} → (A  → B) → (B → C) → (A → C)
    _⋆'_ = λ z z₁ z₂ → z₁ (z z₂)

    yo : {C : Category ℓ-zero ℓ-zero} → ob C → Presheaf C ℓ-zero 
    yo {C} X = C [-, X ] 

    _×p_ : {C : Category ℓ-zero ℓ-zero} → Presheaf C ℓ-zero → Presheaf C ℓ-zero → Presheaf C ℓ-zero
    _×p_ P Q .F-ob c =  F-ob P c .fst × F-ob Q c .fst , isSet× (F-ob P c .snd) (F-ob Q c .snd)
    _×p_ P Q .F-hom f (p , q) = (P .F-hom f p) , (Q .F-hom f q)
    _×p_ P Q .F-id = funExt λ{(p , q) → ΣPathP (funExt⁻ (P .F-id ) p , funExt⁻ (Q .F-id) q)}
    _×p_ P Q .F-seq f g = {!   !} -- funExt λ{ (p , q ) → ≡-× {!   !}  {!   !} } -- funExt λ{ (p , q) → ΣPathP {!   !}}

    -- \b1 
    𝟙 : {C : Category ℓ-zero ℓ-zero} → Presheaf C ℓ-zero 
    𝟙 .F-ob _ = Unit , isSetUnit
    𝟙 .F-hom = λ _ _ → tt
    𝟙 .F-id = refl
    𝟙 .F-seq _ _ = refl

    record scwf : Set₁ where 
        field 
            C : Category ℓ-zero ℓ-zero
            emp : Terminal C
            Ty : Set
            Tm :  Ty → Presheaf C ℓ-zero
            _×c_ : ob C → Ty → ob C
            up×c : (Γ : ob C)(A : Ty) → yo {C} (Γ ×c A) ≅ᶜ (yo {C} Γ ×p Tm A)

        Tm[_,_] : ob C → Ty → Set
        Tm[_,_] Γ A = Tm A .F-ob  Γ .fst

        _⟦_⟧ : {Γ Δ : ob C}{A : Ty} → Tm[ Γ , A ] → C [ Δ , Γ ] → Tm[ Δ , A ]
        _⟦_⟧ {A = A} m γ = Tm A .F-hom γ m
        

            -- somehow we know this is unique ..?

           {-} -- but we also know these equations should hold
            eq₁ : {Δ : ob C}{γ : C [ Δ , Γ ]}{a : Tm[ Δ , A ]} →
                 bkwd (γ , a) ⋆⟨ C ⟩ π₁ ≡ γ 
            eq₁ = {!   !}

            eq₂ : {Δ : ob C}{γ : C [ Δ , Γ ]}{a : Tm[ Δ , A ]} → 
                Tm A .F-hom {! bkwd ? !} a ≡ a
            eq₂ = {!   !}-}


        -- get the data from the UP 
        proj×c : {Γ Δ : ob C}{A : Ty} → C [ Δ , (Γ ×c A) ] → C [ Δ , Γ ] × Tm[ Δ , A ]
        proj×c {Γ}{Δ}{A} = up×c Γ A .trans .N-ob Δ

        π₁ : {Γ : ob C}{A : Ty} → C [ Γ ×c A , Γ ] 
        π₁ {Γ}{A} =  up×c Γ A .trans .N-ob (Γ ×c A) (C .id) .fst 
            
        π₂ : {Γ : ob C}{A : Ty} → Tm[ Γ ×c A , A ]
        π₂ {Γ}{A} = up×c Γ A .trans .N-ob (Γ ×c A) (C .id ) .snd

        pair×c  : {Γ Δ : ob C}{A : Ty} → C [ Δ , Γ ] × Tm[ Δ , A ] → C [ Δ , (Γ ×c A) ]
        pair×c {Γ}{Δ}{A} = up×c Γ A .nIso Δ .inv

        ⟪_,_⟫ : {Γ Δ : ob C}{A : Ty} → C [ Δ , Γ ] → Tm[ Δ , A ] → C [ Δ , (Γ ×c A) ]
        ⟪_,_⟫ {Γ}{Δ}{A} γ a = pair×c (γ , a)


        η×c' : {Γ Δ : ob C}{A : Ty} → proj×c ⋆' pair×c ≡ λ x → x
        η×c' {Γ}{Δ}{A} =  up×c Γ A .nIso Δ .ret 


        η×c : {Γ Δ : ob C}{A : Ty} → ⟪ π₁ , π₂ ⟫ ≡ C .id {Γ ×c A} 
        η×c {Γ}{Δ}{A} = funExt⁻ η×c' _

        --β×c 

    --Can : Categoryᴰ

    record scwfHom (S T : scwf) : Set where 
        private module S = scwf S 
        private module T = scwf T
        field 
            Fc : Functor S.C T.C
            Fty : S.Ty → T.Ty
            Ftm : (A : S.Ty) → NatTrans (S.Tm A) (T.Tm (Fty A) ∘F (Fc ^opF))
            presTerm : Fc .F-ob (S.emp .fst) ≡ T.emp .fst
            presExt : {Γ : ob (S.C)}{A : S.Ty} → Fc .F-ob (Γ S.×c A) ≡ (Fc .F-ob Γ T.×c Fty A)
            presSub : {Γ Δ : ob (S.C)}{A : S.Ty}{γ : (S.C) [ Δ , Γ ]}{a : S.Tm[ Γ , A ]} → 
                Ftm A .N-ob Δ (S.Tm A .F-hom γ a) ≡ T.Tm (Fty A) .F-hom (Fc .F-hom γ) (Ftm A .N-ob Γ a)
--            presProj : Fc . F-hom S.π₁ ≡ {! T.π₁ {?} {?}  !}

    -- type structure
    module types (S : scwf) where 
        open scwf S  

        record unitType : Set₁ where 
            field 
                one : Ty 
                up1 : Tm one ≅ᶜ 𝟙

            tt' : {Γ : ob C} → Tm[ Γ , one ]
            tt' {Γ} = up1 .nIso Γ .inv tt

            module huh (Γ Δ : ob C)(γ : C [ Δ , Γ ]) where 


                fwrd : Tm[ Γ , one ] → Unit
                fwrd = up1 .trans .N-ob  Γ

                -- the backwards map
                bkwd : Unit → Tm[ Γ  , one ]
                bkwd = up1 .nIso Γ .inv
                {-
                    natrual transformation Tm one to 𝟙 is 
                    γ : Δ → Γ 

                    Tm[ Γ , one] ------> Tm[ Δ , one]
                     |                      |
                     |                      |
                     |                      |
                    𝟙(Γ) = Unit  ------> 𝟙(Δ) = Unit
                -}
                _ : (fwrd ⋆' 𝟙 {C} .F-hom γ) ≡ (Tm one .F-hom γ ⋆' up1 .trans .N-ob Δ)
                _ = up1 .trans .N-hom γ

                _ : (fwrd ⋆' bkwd) ≡ λ x → x
                _ = up1 .nIso Γ  .ret

                _ : (bkwd ⋆' fwrd) ≡ λ x → x 
                _ = up1 .nIso Γ .sec
        
        record prodTypes : Set₁ where 
            field 
                _×'_ : Ty → Ty → Ty 
                up× : {A B : Ty} →  Tm (A ×' B) ≅ᶜ (Tm A ×p Tm B)

            
            module _ {A B : Ty}{Γ : ob C} where 

                proj : Tm[ Γ , A ×' B ] → Tm[ Γ , A ] × Tm[ Γ , B ] 
                proj = up× {A}{B} .trans .N-ob Γ
                
                p₁ : Tm[ Γ , A ×' B ] → Tm[ Γ , A ] 
                p₁ f = proj f .fst

                p₂ : Tm[ Γ , A ×' B ] → Tm[ Γ , B ] 
                p₂ f = proj f .snd

                pair :  Tm[ Γ , A ] × Tm[ Γ , B ] → Tm[ Γ , A ×' B ]
                pair = up× .nIso Γ .inv

                η× : {p : Tm[ Γ , A ×' B ]} → pair (p₁ p , p₂ p) ≡ p 
                η×  {p} = funExt⁻ η' p where
                    η' : (proj ⋆' pair) ≡ λ x → x
                    η' =  up× {A}{B} .nIso Γ .ret

                βproj : {a : Tm[ Γ , A ]}{b : Tm[ Γ , B ]} → proj (pair (a , b)) ≡ (a , b)
                βproj {a}{b} = funExt⁻ β' (a , b) where 
                    β' : (pair ⋆' proj) ≡ λ x → x 
                    β' = up× {A} {B} .nIso Γ .sec

                β×₁ : {a : Tm[ Γ , A ]}{b : Tm[ Γ , B ]} → p₁ (pair (a , b)) ≡ a
                β×₁ = cong fst βproj 

                β×₂ : {a : Tm[ Γ , A ]}{b : Tm[ Γ , B ]} → p₂ (pair (a , b)) ≡ b
                β×₂ = cong snd βproj

            module huh (A B : Ty)(Γ Δ : ob C)(γ : C [ Δ , Γ ]) where 

                fwrd : (Γ : ob C) → Tm[ Γ , A ×' B ] → Tm[ Γ , A ] × Tm[ Γ , B ]
                fwrd Γ = up× {A} {B} .trans .N-ob Γ

                {-
                    Tm[ Γ , A ×' B ] ----------------> Tm[ Δ , A ×' B ]
                            |                                   |
                            |                                   |
                    Tm[ Γ , A] x Tm [ Γ , B ] ------> Tm[ Δ , A] × Tm[Δ , B]
                -}
                square : ((Tm (A ×' B)) .F-hom γ ⋆' fwrd Δ) ≡ (fwrd Γ ⋆' (Tm A ×p Tm B) .F-hom γ) 
                square = up× {A} {B} .trans .N-hom γ


        Cont : Ty → Ty → Presheaf C ℓ-zero  
        Cont A B .F-ob Γ = Tm[ Γ ×c A  , B ] , Tm B .F-ob (Γ ×c A) .snd
        Cont A B .F-hom γ = Tm B .F-hom (⟪ π₁ ⋆⟨ C ⟩ γ , π₂ ⟫)
        Cont A B .F-id {Γ}= cong (λ h → Tm B .F-hom (⟪ h , π₂ ⟫)) (C .⋆IdR _) ∙ cong (λ h → Tm B .F-hom h) (η×c {Γ} {Γ ×c A} {A}) ∙ Tm B  .F-id
        Cont A B .F-seq γ δ = {!   !}

        record funTypes : Set₁ where 
            field 
                fun : Ty → Ty → Ty 
                up→ : {A B : Ty} → Tm (fun A B) ≅ᶜ Cont A B

            module _ {Γ : ob C}{A B : Ty} where 

                lamInv : Tm[ Γ , fun A B ] → Tm[ Γ ×c A , B ] 
                lamInv = up→ {A} {B} .trans .N-ob Γ

                lam : Tm[ Γ ×c A , B ] → Tm[ Γ , fun A B ] 
                lam = up→ {A} {B} .nIso  Γ .inv

                ap : Tm[ Γ , fun A B ] × Tm[ Γ , A ] → Tm[ Γ , B ]
                ap (f , a) = lamInv f ⟦ ⟪ C .id , a ⟫ ⟧
                    -- Tm B .F-hom ⟪ C .id , a ⟫ (lamInv f)

        
-- syntactic model
    open import src.Data.STLC

    S : Category ℓ-zero ℓ-zero 
    S .ob = Ctx
    S .Hom[_,_] = CtxMap
    S .id = idCtxMap
    S ._⋆_ = seqCtxMap
    S .⋆IdL _ = ≡CtxMap (funExt λ _ → subId)
    S .⋆IdR _ = ≡CtxMap (funExt λ _ → refl)
    S .⋆Assoc _ _ _ = ≡CtxMap (funExt λ _ → {! subSeq  !})
    S .isSetHom = isSetCtxMap

    open scwf
    open import Cubical.Data.Fin.Recursive
    open import Cubical.Data.Nat

    tm : U → Presheaf S ℓ-zero 
    tm A .F-ob Γ = (Γ ⊢ A) , isSetTerm
    tm A .F-hom = sub
    tm A .F-id = funExt λ _ → subId
    tm A .F-seq _ _ = {!   !}


    ⊘isTerminal : isTerminal S ⊘ 
    ⊘isTerminal Γ = ! , uniq where 
        open CtxMap
        ! : S [ Γ , ⊘ ]
        ! .terms ()

        uniq : (γ : S [ Γ , ⊘ ]) → ! ≡ γ 
        uniq γ = ≡CtxMap (funExt λ ())

    open CtxMap
    STLC : scwf 
    STLC .C = S
    STLC .emp = ⊘ , ⊘isTerminal
    STLC .Ty = U
    STLC .Tm = tm
    STLC ._×c_ = update'
    STLC .up×c Γ A = goal where 

        nt : NatTrans (yo (update' Γ A)) (yo {S} Γ ×p tm A) 
        nt .N-ob Δ = projC
        nt .N-hom γ = refl

        isont : (Δ : Ctx) → isIso (SET ℓ-zero) projC 
        isont Δ .inv = pairC
        isont Δ .sec = funExt λ {(γ , a) → refl}
        isont Δ .ret = funExt λ { record { terms = γ } → ≡CtxMap (funExt λ {zero → refl
                                                                          ; (suc x) → refl})}  
        goal : yo {S} (update' Γ A) ≅ᶜ (yo {S} Γ ×p tm A)
        goal = record { trans = nt ; nIso = isont } 

    module hmm where 
        open scwfHom 
        open import Cubical.Data.Sigma
        open import Cubical.Data.Bool


        what : Type → Presheaf (SET ℓ-zero) ℓ-zero 
        what A .F-ob (Γ , Γset) = (Γ → A) , isSet→ {!   !}
        what A .F-hom γ = γ ∘s_
        what A .F-id = refl
        what A .F-seq γ δ = refl

        sem : scwf 
        sem .C = SET ℓ-zero
        sem .emp = (Unit , isSetUnit) , {!   !}
        sem .Ty = Set
        sem .Tm = what
        sem ._×c_ (Γ , _) A = (Γ × A) , {!   !}
        sem .up×c Γ A = {!   !}
            --record { trans = natTrans (λ x x₁ → {!   !}) {!   !} ; nIso = {!   !} }


        denty : Ty STLC → Type 
        denty unit = Unit
        denty bool = Bool
        denty (prod x y) = denty x × denty y
        denty (arr x y) = denty x → denty y

        {-# TERMINATING #-}
        denctx' : Ctx → hSet ℓ-zero 
        denctx' (zero , Γ) = Unit , isSetUnit
        denctx' (suc n , Γ) = (denty (Γ (toFin n)) × denctx' (n , (peel Γ .snd)) .fst) , {!   !}

        denctx : Functor (C STLC) (SET ℓ-zero) 
        denctx .F-ob  = denctx'
        denctx .F-hom {Δ} {(zero , Γ)} γ _ = tt
        denctx .F-hom {Δ} {(suc n , Γ)} γ d = {!   !} , {! d  !}
        denctx .F-id = {!   !}
        denctx .F-seq = {!   !}

        dentm : {Γ : Ctx}{A : U} → Γ ⊢ A → denctx' Γ .fst → denty A 
        dentm (u x) _ = x
        dentm (b x) _ = x
        dentm (pair x y) Γ = (dentm x Γ) , (dentm y Γ)
        dentm (fun x) Γ a = dentm (x {! a  !}) Γ
        dentm (app x y) Γ = dentm x Γ (dentm y Γ)
        dentm (var i) Γ = {!   !}

        tmnat : (A : Ty STLC) → NatTrans (Tm STLC A) (what (denty A) ∘F (denctx ^opF)) 
        tmnat A .N-ob Γ = dentm
        tmnat A .N-hom = {!   !}

        setmodel : scwfHom STLC sem
        setmodel .Fc = denctx
        setmodel .Fty  = denty
        setmodel .Ftm = tmnat
        setmodel .presTerm = {!   !}
        setmodel .presExt = {!   !}
        setmodel .presSub = {!   !}
          

    open types STLC
    STLC-×Types : prodTypes
    STLC-×Types = record { _×'_ = prod ; up× = goal } where 

        fwrd : {A B : U} → NatTrans (tm (prod A B)) (tm A ×p tm B) 
        fwrd {A} {B} .N-ob = λ Γ → λ p → {!   !} , {!   !}
        fwrd {A} {B} .N-hom = {!   !}
    
        goal : {A B : U} → tm (prod A B) ≅ᶜ (tm A ×p tm B) 
        goal = record { trans = fwrd ; nIso = {!   !} }



    clTy : U → Set 
    clTy A = ⊘ ⊢ A

    clCtx : Ctx → Set 
    clCtx Γ = CtxMap ⊘ Γ 

    open Categoryᴰ
    Sᴰ : Categoryᴰ S ℓ-zero ℓ-zero
    Sᴰ .ob[_] Γ = clCtx Γ → Set
    Sᴰ .Hom[_][_,_] {Γ}{Δ} γ Γ∙ Δ∙ = (x : Fin (Γ .fst)) → (δ : clCtx Δ) → Δ∙ δ → {! γ .terms x  !}
    Sᴰ .idᴰ = {!   !}
    Sᴰ ._⋆ᴰ_ = {!   !}
    Sᴰ .⋆IdLᴰ = {!   !}
    Sᴰ .⋆IdRᴰ = {!   !}
    Sᴰ .⋆Assocᴰ = {!   !}
    Sᴰ .isSetHomᴰ = {!   !}


    LR : scwf 
    LR .C = ∫C Sᴰ
    LR .emp = {!   !}
    LR .Ty = Σ[ A ∈ STLC .Ty ]  (clTy A → Set)
    LR .Tm (A , A∙) = P where 
        P : Presheaf (∫C Sᴰ) ℓ-zero
        P .F-ob (Γ , Γ∙ )= (Σ[ M ∈ Γ ⊢ A ] ((γ : clCtx Γ) → Γ∙ γ → A∙ (sub γ M))) , {!   !}
        P .F-hom {(Δ , Δ∙ )}{(Γ  , Γ∙ )} = {!   !}
        P .F-id = {!   !}
        P .F-seq = {!   !}
    LR ._×c_ = {!   !}
    LR .up×c = {!   !}

    open scwfHom 
    open import Cubical.Data.Sum

    module initiality (𝓒 : scwf) where  
        private module 𝓒 = scwf 𝓒

        Fty' : Ty STLC → 𝓒.Ty
        Fty' = {!   !}

        {-# TERMINATING #-}
        flatten : Ctx → C 𝓒 .ob 
        flatten (zero , Γ) = 𝓒 .emp .fst
        flatten (suc n , Γ) = flatten (n , peel Γ .snd) 𝓒.×c Fty' (Γ (toFin n))

        {-# TERMINATING #-}
        flatMap : {Γ Δ : Ctx} → S [ Γ , Δ ] → 𝓒.C [ flatten Γ , flatten Δ ]
        flatMap {Γ} {zero , Δ} γ = 𝓒 .emp .snd (flatten Γ) .fst
        flatMap {Γ} {suc n , Δ} γ = 𝓒.⟪_,_⟫ (flatMap {Γ}{(n , peel Δ .snd)} {! γ  !}) {!   !}

        Fc' : Functor (C STLC) (C 𝓒)
        Fc' .F-ob = flatten
        Fc' .F-hom = flatMap
        Fc' .F-id = {!   !}
        Fc' .F-seq = {!   !}

        nob' : (A : Ty STLC) → N-ob-Type (tm A) (𝓒.Tm (Fty' A) ∘F (Fc' ^opF))
        nob' .unit Γ (u x) = {!   !}
        nob' .bool Γ (b x) = {!   !}
        nob' .(prod _ _) Γ (pair m m₁) = {!   !}
        nob' .(arr _ _) Γ (fun x) = {!   !}
        nob' A Γ (app m m₁) = {!   !}
        nob' .(snd Γ i) Γ (var i) = {!   !}

        nt : (A : Ty STLC) → NatTrans (Tm STLC A) (𝓒.Tm (Fty' A) ∘F (Fc' ^opF)) 
        nt A .N-ob = nob' A
        nt A .N-hom = {!   !}

        init : scwfHom STLC 𝓒
        init .Fc = Fc'
        init .Fty = Fty'
        init .Ftm = {!   !}
        init .presTerm = {!   !}
        init .presExt = {!   !}
        init .presSub = {!   !}

    -- we get this via initiality!
    -- but i can define it here to see what it looks like
    -- need eliminators in the language to state this
    can : (A : Ty STLC) → clTy A → Set
    can unit _ =  Unit
    can bool m = {!   !} ⊎ {!   !}
    can (prod A B) m = {!   !}
    can (arr A B) m = (n : clTy A) → can A n → can B (app m n)
    
    FL : scwfHom STLC LR 
    FL .Fc = {!   !}
    FL .Fty A = A , can A
    FL .Ftm = {!   !}
    FL .presTerm = {!   !}
    FL .presExt = {!   !}
    FL .presSub = {!   !}
          
      
           