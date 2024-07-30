module src.Data.AltWorld where 
    open import Cubical.Categories.Category
    open import Cubical.Categories.Functor
    open import Cubical.Categories.Functors.Constant
    open import Cubical.Categories.Instances.Sets 
    open import Cubical.Foundations.HLevels hiding (extend)
    open import Cubical.Categories.Displayed.Base
    open import Agda.Primitive

    module _ {ℓS} where
        open Categoryᴰ
        open import Cubical.Categories.Displayed.Constructions.TotalCategory
        open import Cubical.Categories.Constructions.TotalCategory


        module retry {SynTy : hSet ℓS } where 
            open Category
            open import Cubical.Data.Sigma
            open import src.Data.FinSet
            open import Cubical.Data.FinSet
            open import Cubical.Data.FinSet.Constructors
            open import Cubical.Functions.Embedding


            W : Category {!  FinSet !} {!   !} 
            W .ob = Σ (FinSet ℓS) λ X → SynTy .fst → X .fst
            W .Hom[_,_] (X , m1) (Y , m2) = Σ (X .fst ↪ Y .fst) λ i → m1 ≡ {! i ∘S   !}
            W .id = {!   !}
            W ._⋆_ = {!   !}
            W .⋆IdL = {!   !}
            W .⋆IdR = {!   !}
            W .⋆Assoc = {!   !}
            W .isSetHom = {!   !}
            
       {-} module hmm {SynTy : hSet ℓS }{ℓ ℓ'}where 
            open import Cubical.Foundations.HLevels hiding (extend)
            open import Cubical.Foundations.Prelude
            open Categoryᴰ
            SETᴰ : Categoryᴰ (SET ℓ) {!   !} {!   !} 
            SETᴰ .ob[_] X = SynTy .fst → X .fst 
            SETᴰ .Hom[_][_,_] f P Q = ∀ x → P x  →  Q (f x) .fst
            SETᴰ .idᴰ = λ x z → z
            SETᴰ ._⋆ᴰ_ {f = f} {g} fᴰ gᴰ x p = gᴰ (f x) (fᴰ x p)
            SETᴰ .⋆IdLᴰ fᴰ = refl
            SETᴰ .⋆IdRᴰ fᴰ = refl
            SETᴰ .⋆Assocᴰ fᴰ gᴰ hᴰ = refl
            SETᴰ .isSetHomᴰ {yᴰ = Q} = isSetΠ λ x → isSetΠ λ xᴰ → Q _ .snd -}
        open import Cubical.Categories.Displayed.Instances.Sets.Base

        -- we want a subcategory of Setᴰ where the domain is fixed to a specific type
        -- coslice of SET?
        -- what about injectivity constraint?
        SetFam : Category (lsuc ℓS ) ℓS
        SetFam = ∫C (SETᴰ ℓS ℓS )

        open import Cubical.Data.Sigma
        open import Cubical.Data.FinSet.Base
        open import Cubical.Core.Everything
        open import Cubical.Foundations.Prelude

        open import Cubical.Categories.Constructions.FullSubcategory

        -- problem, we want X to be a fixed type - ex SynTy
        World : Category (ℓ-suc ℓS) ℓS 
        World = FullSubcategory SetFam λ{(X , w) → Σ (X .fst) λ x → isFinSet (w x .fst) }

        open Category
        open import Cubical.Data.Bool
        open import Cubical.Data.Unit 
        open import Cubical.Data.Nat
        open import Cubical.Data.FinSet.Properties
        open import Cubical.Data.FinSet
        open import Cubical.Data.Fin renaming (Fin to Finℕ) hiding (isSetFin)
        open import Cubical.Data.Fin.Properties

        Bool** : hSet ℓS 
        Bool** = ((Bool* , isOfHLevelLift 2 isSetBool))

        Unit** : hSet ℓS 
        Unit** = (Unit* , isOfHLevelLift 2 isSetUnit)  
        
        Nat** : hSet ℓS 
        Nat** = (Lift ℕ , isOfHLevelLift 2 isSetℕ) 


        Fin* : ℕ → hSet ℓS
        Fin* n = (Lift (Finℕ n)) , (isOfHLevelLift 2 isSetFin)

        data SynTy' : Type ℓS where 
            u n b : SynTy'

        SynTyisSet : isSet SynTy' 
        SynTyisSet = {!  !}

        SynTy : hSet ℓS 
        SynTy = SynTy' , SynTyisSet

        w₁ : ob World 
        w₁ = (SynTy , {!   !}) , {!   !}
 