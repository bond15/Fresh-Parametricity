{-# OPTIONS --allow-unsolved-metas #-}
-- category of finite sets and embeddings
module src.Data.FinSet where
    open import Cubical.Categories.Category        
    open import Cubical.Foundations.HLevels hiding (extend)
    open import Cubical.Functions.Embedding
    open import Cubical.Foundations.Prelude
    open import Cubical.Data.FinSet
    open import Cubical.Data.FinSet.Constructors

    module _ {ℓ : Level} where 
        open Category
        open import Cubical.Data.Sigma
        
        -- TODO: define compositionally using subcategories of Set
        FinSetMono : Category (ℓ-suc ℓ) ℓ 
        ob FinSetMono = FinSet ℓ
        Hom[_,_] FinSetMono (A , _) (B , _) = A ↪ B
        id FinSetMono {x} = id↪ (fst x)
        _⋆_ FinSetMono f g = compEmbedding g f
        ⋆IdL FinSetMono (f , emb) = Σ≡Prop (λ x → isPropIsEmbedding) refl
        ⋆IdR FinSetMono (f , emb) = Σ≡Prop (λ x → isPropIsEmbedding) refl
        ⋆Assoc FinSetMono f g h = Σ≡Prop (λ x → isPropIsEmbedding) refl
        isSetHom FinSetMono {x} {y} = isSetΣ 
                                (isSetΠ λ _ → isFinSet→isSet (snd y)) 
                                (λ t → isProp→isOfHLevelSuc 1 isPropIsEmbedding)

        module Monoidal where 

            open import Cubical.Categories.Monoidal.Base
            open import Cubical.Categories.Constructions.BinProduct
            open import Cubical.Categories.Functor
            open Functor
            open import Cubical.Data.Sum
            open import Cubical.Data.Empty 
            open import Cubical.HITs.PropositionalTruncation hiding(map)

            emptyFin* : isFinSet {ℓ} (Lift ⊥)
            emptyFin* = 0 , ∣ (λ()) , record { equiv-proof = λ() } ∣₁
            
            Ø : FinSet ℓ 
            Ø = (Lift ⊥  , emptyFin*) 

            ⊕ : Functor (FinSetMono ×C FinSetMono) FinSetMono
            ⊕ .F-ob (x , y) = (x .fst ⊎ y .fst) , isFinSet⊎ x y
            ⊕ .F-hom (f , g) = map (f .fst) (g .fst) , {! !}
            -- isEmbedding-inl
            --injEmbedding
            ⊕ .F-id = Σ≡Prop (λ x → isPropIsEmbedding) (funExt λ{(inl x) → refl
                                                               ; (inr x) → refl })
            ⊕ .F-seq f g = Σ≡Prop (λ x → isPropIsEmbedding) (funExt λ{ (inl x) → refl
                                                                     ; (inr x) → refl })

            open import Cubical.Foundations.Isomorphism
            idl⊕ : (X : FinSet ℓ) → ⊕ .F-ob (Ø , X) ≡ X 
            idl⊕ X = ΣPathP ((isoToPath ⊎-IdL-⊥*-Iso) , λ i → {! isFinSetIsProp  !})
                --Σ≡Prop {! isFinSetIsProp  !} {!   !}
                -- ΣPathP ((isoToPath ⊎-IdL-⊥*-Iso) , {!   !})
                --{! isoToPath (⊎-IdL-⊥*-Iso {ℓ}{X .fst}{ℓ})!}
                --ΣPathP ({! ⊎-IdL-⊥*-Iso  !} , {!   !})

            SMC : StrictMonCategory (ℓ-suc ℓ) ℓ
            SMC = record { 
                    C = FinSetMono ; 
                    sms = record { 
                            tenstr = 
                                record { 
                                    ─⊗─ = ⊕ ; 
                                    unit = Ø } ; 
                            assoc = {!   !} ; 
                            idl = idl⊕ ; 
                            idr = {!   !} } }

