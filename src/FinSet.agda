{-# OPTIONS --safe #-}
-- category of finite sets and embeddings
module src.FinSet where
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

