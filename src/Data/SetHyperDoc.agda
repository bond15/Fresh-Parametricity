{-# OPTIONS --cubical --type-in-type --allow-unsolved-metas #-}

module src.Data.SetHyperDoc where

    open import src.Data.HyperDoctrine    
    open import Cubical.Categories.Instances.Sets
    open import Cubical.Categories.Category hiding (isUnivalent)
    open Category
    open import Cubical.Categories.Functor
    open Functor
    open import Cubical.Categories.Limits.BinProduct
    open import Cubical.Categories.Limits.Terminal
    open import Cubical.Categories.Exponentials
    open import Cubical.Foundations.Isomorphism
    open import Cubical.Algebra.Lattice
    open import Cubical.Foundations.Prelude
    open import Cubical.Foundations.Structure
    open import Cubical.Categories.Instances.Posets.Base
    open import Cubical.Categories.Instances.Sets
    open import Cubical.Categories.Category
    open import Cubical.Categories.Functor
    open import Cubical.Categories.Instances.Preorders.Monotone
    open import Cubical.Foundations.HLevels
    open import Cubical.Data.Empty hiding (⊥ ; rec)
    open import Cubical.Data.Unit
    open import Cubical.Data.Sigma
    
    _ = isContrUnit
    term : Terminal set 
    term = (Unit , λ x y x₁ y₁ i i₁ → tt) , λ y → (λ x → tt) , λ y₁ i x → tt

    bp : BinProducts set 
    bp x y =
        record{ 
            binProdOb = x .fst × y .fst , isSet× (x .snd) (y .snd) ; 
            binProdPr₁ = fst ; 
            binProdPr₂ = snd ; 
            univProp = λ f₁ f₂ → 
                uniqueExists 
                    (λ z → (f₁ z , f₂ z)) 
                    (refl , refl) 
                    (λ a'  → isProp× (set .isSetHom _ _) ((set .isSetHom _ _))) 
                    λ a' x₁  → funExt λ {p → ΣPathP (sym (funExt⁻ (x₁ .fst) p) , (sym (funExt⁻ (x₁ .snd) p)))}
        }

    open import Cubical.Categories.Presheaf.Representable
    exp : Exponentials set bp 
    exp (x , y) = record { 
        vertex = (y .fst → x .fst) , isSet→  (x .snd) ; 
        element = λ{(f , x) → f x} ; 
        universal = {!   !} }
            --λ A → record { equiv-proof = λ{y₁ → ((λ x₁ x₂ → y₁ (x₁ , x₂)) , funExt λ e → cong y₁ ?) , {!   !} }} }
        


    open import Cubical.Relation.Binary.Preorder

    -- the internal heyting algebra
    prop = hProp _

    open import Cubical.Functions.Logic renaming (inl to inL)
    open import Cubical.Algebra.Semilattice.Base
    open import Cubical.Algebra.CommMonoid.Base
    open import Cubical.Algebra.Monoid.Base
    open import Cubical.Algebra.Semigroup.Base
    open import Cubical.HITs.PropositionalTruncation
    open import Cubical.Data.Sum.Base hiding (rec)

    proplat : LatticeStr prop
    proplat = latticestr ⊥ ⊤ _⊔_ _⊓_ 
        (islattice 
            (issemilattice 
                (iscommmonoid 
                    (ismonoid 
                        (issemigroup (isSetHProp) ⊔-assoc) 
                        ⊔-identityʳ ⊔-identityˡ) 
                    ⊔-comm) 
                ⊔-idem) 
            ((issemilattice 
                (iscommmonoid 
                    (ismonoid 
                        (issemigroup (isSetHProp) ⊓-assoc) 
                        ⊓-identityʳ ⊓-identityˡ) 
                    ⊓-comm) 
                ⊓-idem)) 
            λ x y → ⇔toPath (λ{e → rec (x .snd) (λ {(_⊎_.inl x) → x
                                                  ; (_⊎_.inr x) → x .fst}) e}) (λ {e → ∣ _⊎_.inl e ∣₁}) , 
                    ⇔toPath fst  λ x → x , ∣ _⊎_.inl x ∣₁)

    propHA : isHeytingAlg prop
    propHA = record { 
        islat = proplat ; 
        ⇒l = _⇒_ ; 
        l₁ = λ x → ⇔toPath (λ _ → tt*) λ x₁ x₂ → x₂ ; 
        l₂ = λ x y → ⇔toPath (λ p → (p .fst) , (p .snd) (p .fst)) λ {(p , q) → p , λ _ → q} ; 
        l₃ = λ x y → ⇔toPath fst λ z → z , λ _ → z ; 
        l₄ = ⇒-⊓-distrib }


    _≤p_ : prop → prop → Set 
    -- alternative (found on Wiki ..)
    -- This means that it is possible to deduce P from Q?
    -- p ⇒ q ≡ ⊤
    _≤p_ p q = (p ⇒ q) .fst
    -- Why this order?
    -- Sheaves Geo Logic
    --_≤p_ p q = p ⊓ q ≡ p

    propPreorder : ob poset 
    propPreorder = (prop , 
                    (preorderstr _≤p_ 
                        (ispreorder 
                            (λ a b → isProp→ (b .snd)) 
                            (λ a → λ z → z) 
                            λ a b c z z₁ z₂ → z₁ (z z₂)))) , record { univ = {!   !} }


    open PreorderStr
    -- carrier is powerset and order is subset
    funPropPoset : ob set → ob poset 
    funPropPoset X = pre , {!   !} where 

        carrier = X .fst → prop

        -- pointwise order
        prestr : PreorderStr ℓ-zero carrier
        prestr = preorderstr (λ f g → (x : X .fst) → (f x) ≤p (g x)) 
            (ispreorder (λ f g  → isPropΠ λ x → propPreorder .fst .snd .is-prop-valued (f x) (g x)) 
            (λ f x → propPreorder .fst .snd .is-refl (f x)) 
            λ f g h p q x → propPreorder .fst .snd .is-trans _ _ (h x) (p x) (q x))
        
        pre : Preorder _ _ 
        pre = carrier , prestr

    funPropHA : (X : ob set) → isHeytingAlg (funPropPoset X .fst .fst)
    funPropHA X = record { 
        islat = latticestr 
            (λ x → ⊥) 
            (λ x → ⊤) 
            (λ p q x → (p x) ⊔ (q x)) 
            (λ p q x → (p x) ⊓ (q x)) 
            (islattice 
                (issemilattice 
                    (iscommmonoid 
                        (ismonoid 
                            (issemigroup 
                                (isSetΠ (λ _ → isSetHProp)) 
                                λ p q r → funExt λ x → ⊔-assoc (p x) (q x) (r x)) 
                            (λ p → funExt λ x → ⊔-identityʳ (p x)) 
                            {!   !}) 
                        {!   !}) 
                    {!   !}) 
                {!   !} 
                {!   !}); 
        ⇒l = {!   !} ; 
        l₁ = {!   !} ; 
        l₂ = {!   !} ; 
        l₃ = {!   !} ; 
        l₄ = {!   !} }
    
    𝓟 : Functor (set ^op) (POSET ℓ-zero ℓ-zero) 
    𝓟 .F-ob = funPropPoset
    𝓟 .F-hom {X} {Y} f = record { f = λ P y → P (f y) ; isMon = λ {P}{Q} P≤Q y → P≤Q (f y) }
    𝓟 .F-id = eqMon _ _ refl
    𝓟 .F-seq f g = eqMon _ _ refl

    _×s_ : ob set → ob set → ob set 
    _×s_ (X , XisSet)(Y , YisSet) = X × Y , isSetΣ XisSet  λ _ → YisSet
    
    open import  Cubical.HITs.PropositionalTruncation renaming (map to Hmap)
    open import  Cubical.Categories.Adjoint 
    open NaturalBijection
    setFO : FirstOrderHyperDoc set bp 
    setFO = record{ 
        𝓟 = 𝓟; 
        isHA = funPropHA; 
        isHomo = {! opF  !}; 
        -- functor (X → Prop) (X × X → Prop)
        eq = λ {X} → (
            record { 
                -- Predicate P is over X, to convert it to a predicate over X × X
                -- we can demand that given (x , x'), x ≡ x' and that the Predicate is satisfied at x, P x (so also P x')
                f = λ P → λ {(x , x') → x ≡ₚ x' ⊓ P x} ; 
                isMon = λ {P}{Q} P≤Q → λ {(x , x') (x≡x' , Px) → x≡x' , P≤Q x Px } }) 
            , record { 
                fwd = (λ f x Px → f (x , x) (∣ refl ∣₁ , Px)) ; 
                bkwd = λ {_}{Q} → (λ f → λ {(x , x') → λ {(x≡x' , Px) → substₚ (λ h → (Q (x , h)))  x≡x' (f x Px)}})} ;

        quant = λ {Γ} {X} →
            ((record { 
                f = λ P γ → ∃[ x ∶ X .fst ] P (γ , x) ; 
                isMon = λ {P}{Q} P≤Q γ → Hmap λ {(x , Pγx) → x , P≤Q (γ , x) Pγx} }) , 
            (record { 
                fwd = λ {P} {γx} f γ Pγ → ∣ {!  !} , {!   !} ∣₁ ; 
                bkwd = {!   !} })) , 
            {!   !} ;
        beck₁ = {!   !}; 
        beck₂ = {!   !}}
    setHyperDoc : HyperDoctrine set term bp exp 
    setHyperDoc = 
        record { 
            isFO = setFO ; 
            H = (prop , isSetHProp) , {!   !} ; 
            Θ = λ X → idIso }     

    open FirstOrderHyperDoc setFO hiding(𝓟)

    open import Cubical.Data.Bool
    Γ : ob set 
    Γ = (Bool , isSetBool) ×s (Bool , isSetBool)

    PΓ : Category _ _
    PΓ = toCat (𝓟  .F-ob Γ)

    L : ob PΓ 
    L _ = ⊤

    δ : {I J : ob set} → set [ I ×s J , (I ×s J) ×s J ] 
    δ (i , j) = (i , j) , j

    EQ : {I J : ob set} → {!   !}
    EQ {I} {J} = {! =F {I ×s J}  !}

    EQ_,_ : {Γ A : ob set} → (u v : set [ Γ , A ]) → funPropPoset (Γ ×s Γ) .fst .fst
    EQ_,_ {Γ}{A} u v = what where
        -- substitution
        huh : POSET _ _ [ funPropPoset (A ×s A) , funPropPoset (Γ ×s Γ)]
        huh = 𝓟 .F-hom  {A ×s A}{Γ ×s Γ} (bimap u v)

        what : funPropPoset (Γ ×s Γ) .fst .fst
        what = MonFun.f huh (MonFun.f (=F {A} ) λ _ → ⊤)
    

    R : ob PΓ 
    R = EQ_,_ u v where 
        u : set [ (Bool , isSetBool) , (Bool , isSetBool) ]
        u b = b 

        v : set [ (Bool , isSetBool) , (Bool , isSetBool) ]
        v b = b

    R' : ob PΓ 
    R' = MonFun.f (=F {Bool , isSetBool}) (λ _ → ⊤)

        
    prf : PΓ [ L , R' ]
    prf γ = prf' where 
        -- ≤p := ⇒ 
        -- the hole is a proof that the terms are actually equal
        prf' : L γ ≤p R' γ 
        prf' tt* = ∣ {!   !} ∣₁ , tt*