module src.judge where 

    open import Cubical.Data.Unit 
    open import Cubical.Data.Sigma 
    open import Cubical.Categories.Category
    open import Cubical.Foundations.Prelude
    open import Cubical.Foundations.HLevels 
    open import Cubical.Categories.Functor
    open import Cubical.Categories.Instances.Sets
    open import Cubical.Categories.Profunctor
    open import Cubical.Categories.Constructions.BinProduct
    open import Cubical.Categories.NaturalTransformation
    open Category     
    open Functor
    open NatTrans


{-
    data V₀ : Set where  
        unit : V₀ 
        prod : V₀ → V₀ → V₀  

    el : V₀ → Set 
    el unit = Unit
    el (prod x y) = el x × el y

    isSetV₀ : (v : V₀) → isSet (el v)
    isSetV₀ unit = isSetUnit
    isSetV₀ (prod x y) = isSet× (isSetV₀ _) (isSetV₀ _)

    open Category 

    𝓥 : Category _ _ 
    𝓥 .ob = V₀
    𝓥 .Hom[_,_] x y = el x → el y
    𝓥 .id = λ z → z
    𝓥 ._⋆_ = λ f g z → g (f z)
    𝓥 .⋆IdL _ = refl
    𝓥 .⋆IdR _ = refl
    𝓥 .⋆Assoc _ _ _ = refl
    𝓥 .isSetHom = isSet→ (isSetV₀ _) 
-}

    _⋆'_ : {A B C : Set} → (A  → B) → (B → C) → (A → C)
    _⋆'_ = λ z z₁ z₂ → z₁ (z z₂)

    record Univ : Set₁ where 
        field 
            codes : Set 
            el : codes → Set 
            isSetUniv : (c : codes) → isSet (el c)

    record Judge : Set₁ where 
        field 
            𝓤 : Univ 
            𝓔 : Category ℓ-zero ℓ-zero 
            𝓒 : Functor 𝓔 (SET ℓ-zero)

        open Univ 𝓤 
        
        𝓥 : Category ℓ-zero ℓ-zero 
        𝓥 .ob = codes
        𝓥 .Hom[_,_] x y = el x → el y
        𝓥 .id = λ z → z
        𝓥 ._⋆_ = λ f g z → g (f z)
        𝓥 .⋆IdL _ = refl
        𝓥 .⋆IdR _ = refl
        𝓥 .⋆Assoc _ _ _ = refl
        𝓥 .isSetHom = isSet→ (isSetUniv _) 

        𝓟' : Functor (𝓥 ^op ×C 𝓔) (SET ℓ-zero) 
        𝓟' .F-ob (V , C) = (el V → 𝓒 .F-ob C .fst) , isSet→ (𝓒 .F-ob  C .snd)
        𝓟' .F-hom {(V , C)} {(V' , C')}(f , g) h = (f ⋆'  h) ⋆' 𝓒 .F-hom g -- precompose value morphism, post compose computaiton morphism
        𝓟' .F-id = funExt λ h → funExt λ x → funExt⁻ (𝓒 .F-id) (h x)
        𝓟' .F-seq (f , f') (g , g' )= funExt λ h → funExt λ x →  funExt⁻ (𝓒 .F-seq  _ _) (h (f (g x)))

        -- gives a bunch of notation
        𝓟 : _⊶_ ℓ-zero ℓ-zero 𝓥 𝓔 
        𝓟 = fromFunc 𝓟'
 
    record JudgeHom (J K : Judge) : Set₁ where 
        private module J = Judge J 
        private module K = Judge K 
        field 
            Fv : Functor J.𝓥 K.𝓥
            Fc : Functor J.𝓔 K.𝓥
            Fp : NatTrans J.𝓟' {! K.𝓟'  !} 
