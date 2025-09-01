module src.Data.learnRep where

    open import Cubical.Categories.Category renaming (isIso to CisIso)
    open import Cubical.Categories.Functor
    open import Cubical.Categories.Presheaf
    open import Cubical.Categories.NaturalTransformation
    open import Cubical.Categories.Instances.Sets

    open import Cubical.Foundations.HLevels
    open import Cubical.Foundations.Prelude

    -- open import Cubical.Categories.Presheaf.Representable

    open import Cubical.Foundations.Isomorphism

    module _ {ℓ ℓ'}(C : Category ℓ ℓ')(P : Presheaf C ℓ') where

        ℓm = ℓ-max ℓ ℓ'
        open Category
        open Functor
        open NatTrans
        open Iso

        Ĉ : Category _ _ 
        Ĉ = PresheafCategory C ℓ'

        yo : ob C → ob Ĉ 
        yo x .F-ob y = (C [ y , x ]) , C .isSetHom
        yo x .F-hom f g = f ⋆⟨ C ⟩ g
        yo x .F-id = funExt λ _ → C .⋆IdL _
        yo x .F-seq _ _ = funExt λ _ → C .⋆Assoc _ _ _

        C[-,_] : ob C → ob Ĉ 
        C[-,_] = yo
        
        yoneda : (x : ob C) → Iso (Ĉ [ C[-, x ] , P ]) (P .F-ob x .fst) 
        yoneda x .fun nt = nt .N-ob x (C .id)
        yoneda x .inv Px .N-ob y y→x = P .F-hom y→x Px
        yoneda x .inv Px .N-hom {y}{z} z→y = funExt λ y→x → funExt⁻ (P .F-seq _ _) Px
        yoneda x .rightInv Px = funExt⁻ (P .F-id) Px
        yoneda x .leftInv nt = makeNatTransPath (funExt λ y → funExt λ y→x → funExt⁻ (sym (nt .N-hom y→x)) (C .id) ∙ cong (λ h → nt .N-ob y h) (C .⋆IdR _))

        Yo : Functor C Ĉ 
        Yo .F-ob = yo
        Yo .F-hom x→y .N-ob z z→x = z→x ⋆⟨ C ⟩ x→y
        Yo .F-hom {x}{y} x→y .N-hom {z}{w} w→z = funExt λ z→x → C .⋆Assoc _ _ _
        Yo .F-id = makeNatTransPath (funExt λ z → funExt λ z→x → C .⋆IdR _)
        Yo .F-seq x→y y→z = makeNatTransPath (funExt λ z → funExt λ z→x → sym (C .⋆Assoc _ _ _))

        -- C [ x , y ] ≡ Ĉ [ C[-, x] , C[-,y]]
        -- via Yo .F-hom
        ff : (x y : ob C) → Iso (C [ x , y ]) (Ĉ [ C[-, x ] , C[-, y ] ])
        ff x y .fun = Yo .F-hom
        ff x y .inv nt = nt .N-ob x (C .id)
        ff x y .rightInv nt = makeNatTransPath (funExt λ z → funExt λ z→x → funExt⁻ (sym (nt .N-hom z→x)) (C .id) ∙ cong (λ h → nt .N-ob z h) (C .⋆IdR _))
        ff x y .leftInv y→x = C .⋆IdL _

        YoFF : isFullyFaithful Yo
        YoFF x y = isoToIsEquiv (ff x y)

        open import Cubical.Data.Sigma
        open NatIso
        MyRepresentable : Set _
        MyRepresentable = Σ[ x ∈ ob C ] NatIso C[-, x ] P

        record MyUnivElem : Set ℓm where 
            field 
                x : ob C
                elem : P .F-ob x .fst
                -- C[-, x ] ≅Ĉ P
                -- via natTrans (λ y y→x → P .F-hom y→x elem) _
                -- via yoneda x .inv elem
                -- or equivalently ∀ y → isEquiv λ (f : C [ y , x ]) → P(f)(elem)
                isUniv : CisIso Ĉ (yoneda x .inv elem)

        theorem : Iso MyRepresentable MyUnivElem 
        theorem .fun (x , ni )= record { x = x ; elem = ni .trans .N-ob x (C .id) ; isUniv = {!  ni .nIso x !} }
        theorem .inv record { x = x ; elem = elem ; isUniv = isUniv } = x , {!   !}
        theorem .rightInv = {!   !}
        theorem .leftInv = {!   !}



    module TermUE {ℓ ℓ'}(C : Category ℓ ℓ') where
        open import Cubical.Categories.Functors.Constant
        open import Cubical.Data.Unit

        termP : Presheaf C _ 
        termP = Constant (C ^op) (SET ℓ') (Unit* , isSetUnit*)
        
        Terminal : Set _ 
        Terminal = MyUnivElem C termP

    module _ {ℓ} where 
        open import Cubical.Data.Unit
        open TermUE
        open MyUnivElem
        
        termSet : Terminal (SET ℓ)
        termSet .x = Unit* , isSetUnit*
        termSet .elem =  tt*
        termSet .isUniv = isiso (natTrans (λ{x tt* x₃ → tt*}) {!   !}) {!   !} {!   !}




