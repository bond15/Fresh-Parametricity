{-# OPTIONS --allow-unsolved-metas --lossy-unification #-}
module src.Data.Worlds where 
    open import Cubical.Foundations.Prelude
    open import Cubical.Foundations.HLevels 
    open import Cubical.Categories.Displayed.Constructions.Comma
    open import Cubical.Categories.Presheaf

    open import Cubical.Categories.Category
    open import Cubical.Categories.Functor
    open import Cubical.Categories.Instances.Sets
    open import Cubical.Categories.Instances.Terminal
    open import Cubical.Data.FinSet

    open import src.Data.FinSet

    module _ {ℓS : Level}(T : hSet ℓS) where 

        open Functor
        
        Inc : Functor (FinSetMono{ℓS}) (SET ℓS)
        Inc .F-ob (ty , fin) = ty , isFinSet→isSet fin 
        Inc .F-hom (f , _) x = f x
        Inc .F-id = refl
        Inc .F-seq (f , _) (g , _) = refl
        
        G : Functor (TerminalCategory {ℓS}) ((SET ℓS))
        G = FunctorFromTerminal T

        -- this variance is used for independence structure and semicartisian day conv
        -- this is essentially a slice category but the Identity functor is replaced with an inclusion functor
        -- so that we have the top maps of the slice homs as injective functions
        World : Category (ℓ-suc ℓS) ℓS
        World = (Comma Inc G) ^op

        ≡world : {!   !}
        ≡world = {!   !}

    module MonoidalStructure {ℓS : Level}(T : hSet ℓS) where 
        open import Cubical.Categories.Monoidal.Base 
        open import Cubical.Categories.Constructions.BinProduct
        open Functor
        open import Cubical.Data.Sigma
        open Category
        open import Cubical.Data.Unit
        open import Cubical.Data.FinSet
        open import Cubical.Data.FinSet.Constructors
        open import Cubical.Data.Sum
        open import Cubical.Categories.Displayed.Base
        open import Cubical.Data.SumFin.Base
        open import Cubical.Data.Empty hiding (rec)
        open import Cubical.HITs.PropositionalTruncation hiding(rec ; map)

        W = World T
        _⨂_ : Functor (W ×C W) W
        _⨂_ .F-ob ((((X , Xfin) , tt* ) , w) , (((Y , Yfin) , tt* ) , w')) = 
            (((X ⊎ Y) , isFinSet⊎ ((X , Xfin)) (Y , Yfin)) , tt*) , rec w w'
        _⨂_ .F-hom {X}{Y}((((f , femb) , _), Δ₁) , (((g , gemb) , _), Δ₂)) = 
            ((map f g , {!   !}) , refl) , funExt λ {(inl x) → {! Δ₁   !}
                                                   ; (inr x) → {! Δ₂  !}}
        _⨂_ .F-id = {! refl  !}
        _⨂_ .F-seq = {!  isSetHom !}

        dumb : isFinSet {ℓS} (Lift ⊥)
        dumb = 0 , ∣ (λ()) , record { equiv-proof = λ() } ∣₁

        emptymap : ob W 
        emptymap = ((Lift (Fin 0 ) , dumb) , tt*) , λ()

        open TensorStr
        
        mon : StrictMonStr (World T)
        mon = record { tenstr = 
                record { ─⊗─ = _⨂_ ; 
                         unit = emptymap } ; 
                    assoc = {!   !} ; 
                    idl = λ{x → {! funExt ? !}} ; 
                    idr = {!   !} }

        strmon : StrictMonCategory (ℓ-suc ℓS) ℓS 
        strmon = record { C = W ; sms = mon }


        
   