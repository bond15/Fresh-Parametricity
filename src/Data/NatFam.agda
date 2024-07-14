{-# OPTIONS  --lossy-unification #-}
module src.Data.NatFam where 
    open import Cubical.Foundations.HLevels hiding (extend)
    open import Cubical.Foundations.Prelude  
    open import Cubical.Categories.Category
    open import Cubical.Categories.Functor
    open import Cubical.Categories.Instances.Functors
    open import Cubical.Categories.Instances.Sets
    open import Cubical.Data.FinSet.Base
    open import Cubical.Categories.NaturalTransformation
    open import Cubical.Categories.Functors.Constant
    open import Cubical.Categories.Presheaf.Base
    open import Cubical.Categories.Presheaf.Constructions
    open import Cubical.Categories.Bifunctor.Redundant
    open import Cubical.Categories.Monoidal.Base
    open import src.Data.DayConv
    open import src.Data.Semicartesian
    open import Cubical.Foundations.Isomorphism
    open import Cubical.Data.Sigma 
    open import Cubical.HITs.SetCoequalizer
    open import src.Data.Coend
    open import  Cubical.Categories.Constructions.BinProduct

    module _ {ℓ ℓ' ℓS : Level}{SMC  : StrictMonCategory ℓ ℓ'} where
        open StrictMonCategory SMC renaming (C to C) hiding(ob)
        open Category
        open Functor
        open Bifunctor
        open NatTrans
        --open StrictMonStr
        --open TensorStr 
        open Iso        
        open SetCoequalizer 
        open UniversalProperty
        open Bifunctor
        open Coend
        open Cowedge
        private
            ℓm = ℓ-max ℓ (ℓ-max ℓ' ℓS)
            𝓥 : Category _ _ 
            𝓥 = PresheafCategory C ℓS

        _×h_ : hSet ℓS → hSet ℓS → hSet ℓS
        x ×h y = (x .fst × y .fst) , isSet× (x .snd) (y .snd)

        ×Fhom : {X Y X' Y' : ob C}
                (P Q : ob 𝓥)
                (f : C [ X' , X ])
                (g : C [ Y' , Y ]) →  
                (SET ℓS)[ P .F-ob X ×h Q .F-ob Y , P .F-ob X' ×h Q .F-ob Y' ]
        ×Fhom P Q f g (Px , Qy) = P .F-hom f Px , Q .F-hom g Qy

        NF-ob-Type : (P Q R : ob 𝓥) → Set _
        NF-ob-Type P Q R = (X Y : ob C) → (SET _)[ P .F-ob X ×h Q .F-ob Y , R .F-ob  (X ⊗ Y) ]

        NF-hom-Type : (P Q R : ob 𝓥) → NF-ob-Type P Q R → Set _
        NF-hom-Type P Q R η = 
                        {X Y X' Y' : ob C} →
                        (f : C [ X' , X ]) → 
                        (g : C [ Y' , Y ]) → 
                        seq' (SET _) {P .F-ob X ×h Q .F-ob Y}{R .F-ob (X ⊗ Y)}{R .F-ob (X' ⊗ Y')}
                            (η X Y)(R .F-hom (f ⊗ₕ g))  
                            ≡ 
                        seq' (SET _) {P .F-ob X ×h Q .F-ob Y}{P .F-ob X' ×h Q .F-ob Y'}{R .F-ob (X' ⊗ Y')}
                            (×Fhom P Q f g)(η X' Y')

        record NatFam (P Q R : ob 𝓥) : Set (ℓ-suc ℓm) where
            constructor natFam 
            field 
                NF-ob : NF-ob-Type P Q R
                NF-hom : NF-hom-Type P Q R NF-ob

        module _ {P Q R : ob 𝓥}{n m : NatFam P Q R} where 
            open NatFam
            makeNatFamPath : n .NF-ob ≡ m .NF-ob → n ≡ m
            makeNatFamPath p i .NF-ob = p i
            makeNatFamPath p i .NF-hom {X}{Y}{X'}{Y'}f g = prf i where
                l =  seq' (SET ℓS) {P .F-ob X ×h Q .F-ob Y}{R .F-ob (X ⊗ Y)}{R .F-ob (X' ⊗ Y')} (p i X Y) (R .F-hom (f ⊗ₕ g)) 
                prf : PathP 
                        (λ i → seq' (SET ℓS) {P .F-ob X ×h Q .F-ob Y}{R .F-ob (X ⊗ Y)}{R .F-ob (X' ⊗ Y')} (p i X Y) (R .F-hom (f ⊗ₕ g)) 
                             ≡ seq' (SET ℓS) {P .F-ob X ×h Q .F-ob Y}{P .F-ob X' ×h Q .F-ob Y'}{R .F-ob (X' ⊗ Y')} (×Fhom P Q f g) (p i X' Y') )  
                        (n .NF-hom f g) 
                        (m .NF-hom f g)
                prf = toPathP ((SET ℓS) .isSetHom {P .F-ob X ×h Q .F-ob Y} {R .F-ob (X' ⊗ Y')}  _ _ _ _)
