{-# OPTIONS --safe #-}
module src.Data.Worlds where 
    open import Cubical.Foundations.Prelude
    open import Cubical.Foundations.HLevels 
    open import Cubical.Categories.Displayed.Constructions.Comma

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