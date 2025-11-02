{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --lossy-unification #-}
module PshMonoidal where

    open import Cubical.Categories.Category
    open import Cubical.Foundations.Prelude
    open import Cubical.Foundations.Isomorphism
    open import Cubical.Categories.Functor
    open import Cubical.Foundations.HLevels 
    open import Cubical.Categories.Monoidal.Base
    open import Cubical.Categories.Monoidal.Enriched
    open import Cubical.Categories.NaturalTransformation
    open import Cubical.Categories.Constructions.BinProduct
    open import Cubical.Categories.Presheaf
    open import Cubical.Categories.Presheaf.Constructions
    open import src.Data.PresheafCCC
    open import Cubical.Categories.Bifunctor.Redundant
    open import Cubical.Categories.NaturalTransformation
    open import Cubical.Data.Unit
    open import Cubical.Categories.Limits.BinProduct
    open MonoidalCategory
    open MonoidalStr 
    open TensorStr
    open Category
    open Functor 
    open NatIso
    open NatTrans
    open BinProduct
    open EnrichedCategory
    open Bifunctor

    private
        variable
            ℓ ℓ' ℓS : Level
    module model (𝓒 : Category ℓ ℓ') {ℓS : Level} where
        ℓm = ℓ-max ℓ' (ℓ-max ℓ ℓS)
        𝓟 = PresheafCategory 𝓒 (ℓm)

        ⨂' : Bifunctor 𝓟 𝓟 𝓟
        ⨂' = PshProd {ℓ}{ℓ'}{𝓒}{ℓm}{ℓm}

        ⨂ : Functor (𝓟 ×C 𝓟) 𝓟
        ⨂ = BifunctorToParFunctor 
            {ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc (ℓm))}{ℓ-max (ℓ-max ℓ ℓ') ℓm}{𝓟}
            {ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc (ℓm))}{ℓ-max (ℓ-max ℓ ℓ') ℓm}{𝓟}
            {ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc (ℓm))}{ℓ-max (ℓ-max ℓ ℓ') ℓm}{𝓟}⨂'

        
        𝟙 : ob 𝓟 
        𝟙 .F-ob _ = Unit* , isSetUnit*
        𝟙 .F-hom = λ _ _ → tt*
        𝟙 .F-id = refl
        𝟙 .F-seq _ _ = refl

        𝓟Ten :  TensorStr 𝓟
        𝓟Ten . ─⊗─ = ⨂
        𝓟Ten .unit = 𝟙

        _^_ : ob 𝓟 → ob 𝓟 → ob 𝓟 
        _^_ B A = ExpOb {C = 𝓒} {ℓS} A B

        _×p_ : ob 𝓟 → ob 𝓟 → ob 𝓟 
        _×p_ A B = PshProd {C = 𝓒} ⟅ A , B ⟆b 

        π₁p : {P Q  : ob 𝓟} → 𝓟 [ P ×p Q , P ]
        π₁p {P}{Q} = (×𝓟 {C = 𝓒}{ℓS}) P Q .binProdPr₁

        π₂p : {P Q  : ob 𝓟} → 𝓟 [ P ×p Q , Q ]
        π₂p {P}{Q} = (×𝓟 {C = 𝓒}{ℓS}) P Q .binProdPr₂

        idl : ⨂ ∘F rinj 𝓟 𝓟 𝟙 ≅ᶜ 𝟙⟨ 𝓟 ⟩ 
        idl .trans = natTrans (λ P → π₂p) λ _ → makeNatTransPath refl 
        idl .nIso P = 
            isiso 
                (natTrans (λ x Px → tt* , Px) λ _ → refl) 
                (makeNatTransPath refl) 
                (makeNatTransPath refl)

        idr : ⨂ ∘F linj 𝓟 𝓟 𝟙 ≅ᶜ 𝟙⟨ 𝓟 ⟩
        idr .trans = natTrans (λ P → π₁p) λ _ → makeNatTransPath refl 
        idr .nIso P = 
            isiso  
                (natTrans (λ x Px → Px , tt*) λ _ → refl) 
                (makeNatTransPath refl) 
                (makeNatTransPath refl)

        assoc : {P Q R : ob 𝓟} → 𝓟 [ P ×p (Q ×p R) , (P ×p Q ) ×p R ]
        assoc .N-ob c (p , (q , r)) = (p , q) , r
        assoc .N-hom f = refl
                
        𝓟Mon' : MonoidalStr 𝓟 
        𝓟Mon' .tenstr = 𝓟Ten
        𝓟Mon' .α = record { trans = natTrans (λ {(P , (Q , R)) → assoc}) λ _ → makeNatTransPath refl ; nIso = λ{ (P , Q , R) → 
            isiso  
                (natTrans (λ{ c ((p , q) , r ) → p , (q , r)}) λ _ → refl) 
                (makeNatTransPath refl) 
                (makeNatTransPath refl) }}
        𝓟Mon' .η = idl
        𝓟Mon' .ρ = idr
        𝓟Mon' .pentagon P Q R S = makeNatTransPath refl
        𝓟Mon' .triangle P Q = makeNatTransPath refl

        𝓟Mon : MonoidalCategory (ℓ-suc ℓm) (ℓm) 
        𝓟Mon .C = 𝓟
        𝓟Mon .monstr = 𝓟Mon'

        adjL : {P Q R : ob 𝓟} → 𝓟 [ P ×p Q , R ] → 𝓟 [ P , R ^ Q ] 
        adjL {P}{Q}{R} nt .N-ob c Pc = 
            natTrans 
                (λ{c' ((lift f) , Qc') → nt .N-ob c' (P .F-hom f Pc , Qc')}) 
                λ {c'}{c''} f → funExt λ {(lift g , Qc') →  cong (λ h → nt .N-ob c'' (h , Q .F-hom f Qc')) (funExt⁻ (P .F-seq _ _) Pc) ∙ funExt⁻ (nt .N-hom f) (P .F-hom g Pc , Qc') }
        adjL {P}{Q}{R} nt .N-hom f = funExt λ Px → makeNatTransPath (funExt λ x → funExt λ{ (g , Qx) → cong (λ h → nt .N-ob x ( h , Qx))  (funExt⁻ (sym (P .F-seq f (g .lower)))  Px)})

        dup : {P : ob 𝓟} → 𝓟 [ P , P ×p P ] 
        dup = natTrans (λ x x₁ → x₁ , x₁) λ _ → refl

        swap : {P Q : ob 𝓟} → 𝓟 [ P ×p Q , Q ×p P ]
        swap = dup ⋆⟨ 𝓟 ⟩  ⨂' .Bif-hom× π₂p π₁p  

        {-# TERMINATING #-}
        selfid : {P : ob 𝓟} → NatTrans 𝟙 (P ^ P)
        selfid {P} .N-ob Γ tt* = π₂p
        selfid {P} .N-hom γ = funExt λ { tt* → makeNatTransPath refl}

        expseq : {P Q R : ob 𝓟} → 𝓟 [ (Q ^ P) ×p (R ^ Q) ,  (R ^ P) ]
        expseq {P}{Q}{R} = 
            adjL (
                swap ⋆⟨ 𝓟 ⟩ 
                assoc ⋆⟨ 𝓟 ⟩ 
                ⨂' .Bif-hom× swap (idTrans _) ⋆⟨ 𝓟 ⟩ 
                ⨂' .Bif-hom× (eval Q P) (idTrans _) ⋆⟨ 𝓟 ⟩ 
                swap ⋆⟨ 𝓟 ⟩ 
                eval R Q )


        self : EnrichedCategory 𝓟Mon (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-suc ℓS))
        self .ob = ob 𝓟
        self .Hom[_,_] P Q = Q ^ P
        self .id = selfid
        self .seq P Q R = expseq
        self .⋆IdL P Q = 
            makeNatTransPath (funExt λ c → funExt λ{(tt* , f) → 
                makeNatTransPath (funExt λ c' → funExt λ {(g , Pc') → 
                    cong (λ h → f .N-ob c' (h , Pc')) (cong lift (sym (𝓒 .⋆IdL _)))})}) 
        self .⋆IdR P Q = 
            makeNatTransPath (funExt λ c → funExt λ{(f , tt*) → 
                makeNatTransPath (funExt λ c' → funExt λ{(g , Pc') → 
                    cong (λ h → f .N-ob c' (h , Pc')) (cong lift (sym ( 𝓒 .⋆IdL _)))})})
        self .⋆Assoc P Q R S = 
            makeNatTransPath (funExt λ c → funExt λ{ (f , g , h) → 
                makeNatTransPath (funExt λ c' → funExt λ{ (j , Pc') → 
                    cong (h .N-ob c') (cong₂ _,_ (cong lift (sym (𝓒 .⋆IdL _))) refl) ∙ 
                   cong (λ e → 
                        h .N-ob c'  
                            (lift ((𝓒 ⋆ id 𝓒) ((𝓒 ⋆ id 𝓒) (lower j))) ,
                            g .N-ob c'
                                (lift ((𝓒 ⋆ id 𝓒) ((𝓒 ⋆ id 𝓒) (lower j))) ,
                                f .N-ob c' (e , Pc')))) (cong lift (cong (𝓒 ⋆ id 𝓒)  (𝓒 .⋆IdL _))) 
                   })})  

    
    module _ {𝓒 𝓓 : Category ℓ ℓ'}(F : Functor 𝓓 𝓒) {ℓS : Level} where 
        open model 𝓒 {ℓ-zero} renaming (𝓟Mon to 𝓒Mon)
        open model 𝓓 {ℓ-zero} renaming (𝓟Mon to 𝓓Mon)


        BaseChange : EnrichedCategory 𝓒Mon ℓS → EnrichedCategory 𝓓Mon ℓS 
        BaseChange C .ob = ob C
        BaseChange C .Hom[_,_] X Y = Hom[_,_] C X Y ∘F (F ^opF) 
        BaseChange C .id {x} = natTrans (λ{d → C .id .N-ob (F .F-ob d) }) λ f  → C .id .N-hom (F-hom F f)
        BaseChange C .seq x y z = natTrans (λ{d  → C .seq x y z .N-ob (F .F-ob d) }) λ f  → C .seq _ _ _  .N-hom (F-hom F f)
        BaseChange C .⋆IdL x y = makeNatTransPath (funExt λ d → funExt λ { (tt* , f) → cong (λ h → h .N-ob d (tt*  , f)) {! C .⋆IdL ? ?  !}})
        BaseChange C .⋆IdR x y = makeNatTransPath (funExt λ d → {! C .⋆IdL x y   !})
        BaseChange C .⋆Assoc = {!   !}


    module _ 
        {𝓒 𝓓 : Category ℓ ℓ'}
        (F : Functor 𝓓 𝓒) 
        {ℓS : Level} where 
        open model 𝓒 {ℓ-zero} renaming (𝓟Mon to 𝓒Mon)
        open model 𝓓 {ℓ-zero} renaming (𝓟Mon to 𝓓Mon)

        module _ 
            {C C' : EnrichedCategory 𝓒Mon ℓ-zero}
            (𝓖 : EnrichedFunctor 𝓒Mon C C' ) where 

            open EnrichedFunctor
            
            BaseChangeF : EnrichedFunctor 𝓓Mon (BaseChange F C) (BaseChange F C') 
            BaseChangeF .F₀ = F₀ 𝓖
            BaseChangeF .F₁ {X} {Y} = natTrans (λ d → 𝓖 .F₁ {X} {Y} .N-ob (F .F-ob d)) λ f → 𝓖 .F₁ {X}{Y} .N-hom (F .F-hom f)
            BaseChangeF .Fid = makeNatTransPath {!   !}
            BaseChangeF .Fseq = {!   !}



         