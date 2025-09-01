module Logic where
    open import Cubical.Foundations.Prelude
    open import Cubical.Data.Sigma 
    open import Cubical.Foundations.HLevels
    open import Cubical.Categories.Category
    open Category

    open import Cubical.Categories.Constructions.Slice.Base
    open SliceOb
    open SliceHom
    open import Cubical.Foundations.Powerset
    open import Cubical.Categories.Morphism
    open import Cubical.Categories.Constructions.SubObject
    open import Cubical.Categories.Instances.Sets

    open import Cubical.Categories.Limits.Pullback 
    open Pullback
    module _ {ℓ ℓ'}(𝓒 : Category ℓ ℓ')(pb : Pullbacks 𝓒)(X : ob 𝓒) where

        subX : Category _ _ 
        subX = SubObjCat 𝓒 X

        open import Cubical.Categories.Functor
        open Functor 
{-}
        CAT : Category _ _ 
        CAT .ob = Category _ _
        CAT .Hom[_,_] X Y = Functor X Y
        CAT .id = Id
        CAT ._⋆_ F G = funcComp G F
        CAT .⋆IdL = {!   !}
        CAT .⋆IdR = {!   !}
        CAT .⋆Assoc = {!   !}
        CAT .isSetHom = {!   !}
            --record\n{ ob = {!   !}\n; Hom[_,_] = {!   !}\n; id = {!   !}\n; _⋆_ = {!   !}\n; ⋆IdL = {!   !}\n; ⋆IdR = {!   !}\n; ⋆Assoc = {!   !}\n; isSetHom = {!   !}\n}

        𝓟 : Functor 𝓒 {! CAT  !} 
        𝓟 .F-ob X = {! subObjCatPreorderStr ?  ? ?  !} , {!   !}
        𝓟 .F-hom = {!   !}
        𝓟 .F-id =  {!   !}
        𝓟 .F-seq = {!   !}
        -}
        -- this itself it a functor into CAT 
        -- this would be the action on objects
        𝓟₀ : ob 𝓒 → Category _ _ 
        𝓟₀ X = SubObjCat 𝓒 X
        
        -- action on morphisms
        𝓟 : {X Y : ob 𝓒}→ (f : 𝓒 [ X , Y ]) → Functor (𝓟₀ Y) (𝓟₀ X) 
        𝓟 {X}{Y} f .F-ob (sliceob {Z} Z→Y , mon) = (sliceob {S-ob = X×yZ} m) , {!   !} where 
            X×yZ : ob 𝓒 
            X×yZ = pb (cospan X Y Z f Z→Y) .pbOb

            m : 𝓒 [ X×yZ , X ]
            m = pb (cospan X Y Z f Z→Y) .pbPr₁
            
        𝓟 {X} {Y} f .F-hom {(sliceob {Z} Z→Y , mon1)}{(sliceob {W} W→Y , mon2)} (slicehom Z→W S-comm₁) = slicehom {!   !} {!   !} where 
            _ = {!   !} --pb (cospan Z W Z Z→W Z→Y) .univProp {!   !} (𝓒 .id) {!   !}
        𝓟 {X}{Y} f .F-id = {!   !}  
        𝓟 {X}{Y} f .F-seq = {!   !} 

        -- object of this category is a morphism into X which is monic
        {-
          isMonic : Hom[ x , y ] → Type (ℓ-max ℓ ℓ')
            isMonic {x} {y} f =
                ∀ {z} {a a' : Hom[ z , x ]} → f ∘ a ≡ f ∘ a' → a ≡ a'
        -}
        module _ (Y : ob 𝓒)(m : 𝓒 [ Y , X ])(mMonic : isMonic 𝓒 m ) where 

            obsub : ob subX 
            obsub = sliceob m , mMonic

        -- morphisms in this category are commuting triangles 
        module _ (Y Z : ob 𝓒) 
                (m : 𝓒 [ Y , X ])(n : 𝓒 [ Z , X ])
                (mMon : isMonic 𝓒 m)(nMon : isMonic 𝓒 n)
            where

            Y' : ob subX 
            Y' = sliceob m , mMon

            Z' : ob subX 
            Z' = sliceob n , nMon

            -- which is a morphism in 𝓒 from Y to Z 
            postulate o : 𝓒 [ Y , Z ]

            -- such that 
            postulate ▵ : o ⋆⟨ 𝓒 ⟩ n ≡ m 
            
            morsub : subX [ Y' , Z' ]
            morsub = slicehom o ▵

            -- but we also know that o is monic 
            -- 
            oMon : isMonic 𝓒 o 
            oMon = subObjMorIsMonic 𝓒 X {Y'}{Z'} morsub

        -- what is the terminal object of this category?
        open import Cubical.Categories.Limits.Terminal

        term : Terminal subX
        term = ((sliceob (𝓒 .id)) , λ {_}{a}{a'} x → sym (𝓒 .⋆IdR a) ∙ x ∙ 𝓒 .⋆IdR a') , λ{(sliceob d , snd₁) → (slicehom d (𝓒 .⋆IdR d)) , {!   !} }
        --λ{(slicehom m mcomm) → SliceHom-≡-intro 𝓒 X {f = d}{m} {!   !} {!   !}}}

        open import Cubical.Categories.Limits.BinProduct 
        open BinProduct
        module _ (b : BinProducts 𝓒) where 
            subX×X : Category _ _ 
            subX×X = SubObjCat 𝓒 (b X X  .binProdOb) 

            postulate diag : 𝓒 [ X , (b X X  .binProdOb) ]
            
            equality : ob subX×X 
            equality = (sliceob diag) , λ x → {!   !}

            
        open import Cubical.Categories.Limits.Pullback 
        open Pullback

        module and (pb : Pullbacks 𝓒)
            (m n : ob subX) where 
{-}
            Y = m .fst .S-ob

            Z = n . fst .S-ob

            d : Cospan 𝓒 
            d = (cospan Y X Z (m .fst .S-arr) (n .fst .S-arr))
            
            Y×xZ : ob 𝓒
            Y×xZ = (pb d) .pbOb 

            -- two equal choices here 
            -- (pb d) .pbPr₁ ⋆⟨ 𝓒 ⟩ (m .fst .S-arr) 
            -- or 
            -- (pb d) .pbPr₂ ⋆⟨ 𝓒 ⟩ (n .fst .S-arr)
            -- which are equal by 
            -- pbCommutes 
            p : 𝓒 [ Y×xZ , X ]
            p = (pb d) .pbPr₁ ⋆⟨ 𝓒 ⟩ (m .fst .S-arr)

            m∧n : ob subX 
            m∧n = (sliceob {S-ob = Y×xZ } p) , {!   !}
                -- and this is monic because post comp with a monic is monic
                --postcompCreatesMonic 𝓒  {! (pb d) .pbPr₁ !} {! (m .fst .S-arr)  !} {!   !}
               -- monicComp 𝓒 ((pb d) .pbPr₁) (m .fst .S-arr) prf (m .snd) where 
               --     prf : isMonic 𝓒 ((pb d) .pbPr₁)
               --     prf = postcompCreatesMonic 𝓒 {!   !} {!   !}  {!   !}

-}
            -- implication is the exponential object?

            subProd : BinProducts subX 
            subProd x y = 
                record{ 
                    binProdOb = X×Y ; 
                    binProdPr₁ = prj₁ ; 
                    binProdPr₂ = prj₂ ; 
                    univProp = {!   !} 
                    }
                where 
                    Y = x .fst .S-ob
                    Z = y .fst .S-ob 

                    YZpb = pb (cospan Y X Z (x .fst .S-arr) (y .fst .S-arr))
                    
                    slicem : 𝓒 [ YZpb .pbOb , X ]
                    slicem = YZpb .pbPr₁ ⋆⟨ 𝓒 ⟩ x .fst .S-arr
                    
                    slicemMonic : isMonic 𝓒 slicem 
                    slicemMonic = {!   !}

                    X×Y : ob subX 
                    X×Y = (sliceob slicem) , slicemMonic 

                    -- by definition, we choce this one
                    prj₁ : subX [ X×Y , x ]
                    prj₁ = slicehom (YZpb .pbPr₁) refl

                    -- the other one is equal by the commuting diagram of pullback 
                    prj₂ : subX [ X×Y , y ]
                    prj₂ = slicehom (YZpb .pbPr₂) (sym (YZpb .pbCommutes))

                    
            open import Cubical.Categories.Exponentials
            open import Cubical.Categories.Presheaf.Representable
            open import Cubical.Categories.Adjoint.2Var
            open import Cubical.Categories.Limits.BinProduct.More
            open import Cubical.Categories.Functor
            
            sub⇒ : Exponentials subX subProd 
            sub⇒ ((sliceob m , mMonic) , (sliceob n , nMonic)) = 
                record { 
                    vertex = (sliceob {!   !}) , {!   !} ; 
                    element = {!   !} ; 
                    universal = {!   !} }


            

    module concrete {ℓ}where 

        data Foo : Set ℓ where 
            bar bax : Foo

        hFoo : hSet ℓ 
        hFoo = Foo , {!   !}

        subFoo×Foo : Category _ _ 
        subFoo×Foo = SubObjCat (SET ℓ) ((Foo × Foo) , {!   !})

        equalityFoo : ob subFoo×Foo 
        equalityFoo = (sliceob {S-ob = hFoo} λ foo → foo , foo) , λ x → funExt λ y → {! funExt⁻  x y  !}


    module _ where 
        open import Cubical.Categories.Displayed.Base
        open import Cubical.Categories.Displayed.Properties
        open import Cubical.Categories.Functor
        open Categoryᴰ
        open import Cubical.Data.Bool
        open import Cubical.Data.Unit

        -- implies 
        _⇒_ : Bool → Bool → Type₀ 
        false ⇒ _ = Bool→Type true
        true ⇒ false = Bool→Type false
        true ⇒ true = Bool→Type true

        Pred' : Categoryᴰ (SET ℓ-zero) {!   !} {!   !} 
        Pred' .ob[_] X = fst X → Bool -- subsets of X
        Pred' .Hom[_][_,_]{X}{Y} f pX pY = ∀ (x : X .fst) → pX x ⇒ pY (f x)
        Pred' .idᴰ x = {! tt  !}
        Pred' ._⋆ᴰ_ f g x = {! f x  !}
        Pred' .⋆IdLᴰ = {!   !}
        Pred' .⋆IdRᴰ = {!   !}
        Pred' .⋆Assocᴰ = {!   !}
        Pred'  .isSetHomᴰ = {!   !}

        -- total category of Pred'
        Pred : Category _ _ 
        Pred = {!   !}

        -- The fibration, projection
        P : Functor Pred (SET ℓ-zero)
        P = {!   !}


        


         
  
   