{-# OPTIONS --cubical #-}

module CCCPresheaf where 
    open import Cubical.Foundations.Prelude
    open import Cubical.Foundations.HLevels
    open import Cubical.Categories.Category using (Category)

    open import Cubical.Categories.Functors.HomFunctor

    module exampleWorldCat where 
        open import Cubical.Data.Bool

        𝓟 : Set₀ → Set₀ 
        𝓟 X = X → Bool

        data ⊥ : Set₀ where
        data ⊤ : Set₀ where
            tt : ⊤


        _∈_ : {X : Set₀} → (× : X) → (s : 𝓟 X) → Set₀
        x ∈ s with s x 
        x ∈ s     | true = ⊤
        x ∈ s     | false = ⊥
        
        _⊆_ : {X : Set₀} → 𝓟 X → 𝓟 X → Set₀
        X ⊆ Y = ∀ {x} → x ∈ X → x ∈ Y

        data W : Set₀ where 
            w1 w2 w3 w4 w5 : W

        open Category

        World : Category ℓ-zero ℓ-zero 
        ob World = 𝓟 W 
        Hom[_,_] World = _⊆_
        id World x = x
        _⋆_ World f g x = g (f x)
        ⋆IdL World f = refl
        ⋆IdR World f = refl
        ⋆Assoc World f g h = refl
        isSetHom World  = {! isSetΠ2 ? ? !}

    -- Presheaf category already defined in stdlib
    open import Cubical.Categories.Presheaf.Base
    open exampleWorldCat using (World)

    Psh-World : Category (ℓ-suc ℓ-zero) (ℓ-zero) 
    Psh-World = PresheafCategory World ℓ-zero

    -- Psh-World is Cartesian Closed


    

    


