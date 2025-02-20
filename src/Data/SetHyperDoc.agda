{-# OPTIONS --cubical --type-in-type  --allow-unsolved-metas #-}

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
        universal  = λ A → record { equiv-proof = λ f → 
            uniqueExists 
                (λ z y → f (z , y))
                refl 
                ((λ a' x y → set .isSetHom  _ _ x y)) 
                λ Z→Y→X p → funExt λ z → funExt λ y → funExt⁻ (sym p)  (z , y) }}



    open import src.Data.HeytingAlg

    -- Theorem 4.6 a taste of categorical logic
    -- let H be any complete Heyting Algebra, 
    -- Then Set together with a functor Hom_Set[_,H] and generic object H
    -- is a hyperdoctrine
    module HomHyperDoc (H : hSet _) (compHA : isCompleteHeytingAlg H) where
        open import Cubical.Relation.Binary.Preorder 

        open isCompleteHeytingAlg compHA
        open isHeytingAlg isHA renaming (poset to P)
        open PreorderStr (P .fst .snd)

        module homposet (X : hSet _) where 

            _≤f_ : set [ X , H ] → set [ X , H ] → Type ℓ-zero
            _≤f_ f g = (x : X .fst) → f x ≤ g x

            open PosetFromLattice ((H .fst) , islat) (H .snd) using (ref ; trn)

            fpre : IsPreorder _≤f_ 
            fpre = ispreorder 
                    (λ a b  → isPropΠ λ x → H .snd (a x) _) 
                    (λ f x → ref (f x)) 
                    λ f g h p1 p2 x → trn (f x) (g x) (h x) (p1 x) (p2 x)

            pre : PreorderStr ℓ-zero (set [ X , H ])
            pre = preorderstr 
                _≤f_ 
                fpre

            HX : ob poset 
            HX = ((set [ X , H ]) , pre) , {!   !}

        fob : ob set → ob poset 
        fob X = HX where open homposet X

        𝓟 : Functor (set ^op) (POSET ℓ-zero ℓ-zero) 
        𝓟 .F-ob = fob
        𝓟 .F-hom f = record { f = λ P y → P (f y) ; isMon = λ {P}{Q} P≤Q y → P≤Q (f y) }
        𝓟 .F-id = eqMon _ _ refl
        𝓟 .F-seq _ _ = eqMon _ _ refl

        𝓟XisSet : (X : ob set) → isSet (𝓟 .F-ob X .fst .fst)
        𝓟XisSet = {!   !}

        module _ (X : ob set) where 

            homlat : LatticeStr (fob X .fst .fst)
            homlat = 
                latticestr 
                (λ x → {! ⊥  !}) 
                {!   !} 
                {!   !} 
                {!   !} 
                {!   !}
            
        isHAHom : (X : ob set) → isHeytingAlg (𝓟 .F-ob X .fst .fst , 𝓟XisSet X) 
        isHAHom X = record { 
            islat = homlat X ; 
            ⇒l = {!   !} ; 
            l₁ = {!   !} ; 
            l₂ = {!   !} ; 
            l₃ = {!   !} ; 
            l₄ = {!   !} }

        FO : FirstOrderHyperDoc set bp 
        FO = record
            { 𝓟 = 𝓟
            ; 𝓟_isSet = 𝓟XisSet
            ; isHA = isHAHom
            ; isHomo = {!   !}
            ; eq = {!   !}
            ; quant = {!   !}
            ; beck₁ = {!   !}
            ; beck₂ = {!   !}}

        HD : HyperDoctrine set term bp exp
        HD = record { 
            isFO = FO ; 
            H = {!   !} ; 
            Θ = {!   !} }




{-
    -- TODO Complete Heyting Algebra
    open PreorderStr
    
    -- let P be a preorder, the upwards closed subsets of P is a complete Heyting Algebra
    ↑_ : Preorder _ _ → Set 
    ↑_ (X , P) = Σ[ A ∈ ℙ X ] ((x y : X) → x ∈ A → P ._≤_ x y → y ∈ A)
    -- A is a subset of X
    -- such that
    -- for any x ∈ A 
    -- if there is some y ∈ X that is x ≤ y
    -- then y ∈ A
    
    open import Cubical.Foundations.HLevels

    ↑isSet : {P : Preorder _ _ } → isSet (↑ P)
    ↑isSet {P} = isSetΣ isSetℙ λ x → isSetΠ2 λ y z → isSet→ (isSet→ (isProp→isSet (∈-isProp x z)))

    HeytingAlg : Set 
    HeytingAlg = TypeWithStr _ isHeytingAlg where 
        open isHeytingAlg


    power≡ : {X : Set}{A B : ℙ X} → (prf : (x : X) → (x ∈ A → x ∈ B) × ( x ∈ B → x ∈ A)) → A ≡ B 
    power≡ {X}{A}{B} prf = ⊆-extensionality A B ((λ x → prf x .fst) , λ x → prf x .snd)
    
    ↑≡ : {P : Preorder _ _ }{A B : ↑ P} → (prf : A .fst ≡ B .fst) → A ≡ B 
    -- (prf : (x : P .fst) → (x ∈ A .fst → x ∈ B .fst) × ( x ∈ B .fst → x ∈ A .fst)) → A ≡ B 
    ↑≡ {P}{A}{B} prf = Σ≡Prop (λ x → isPropΠ2 λ y z → isProp→ (isProp→ (∈-isProp x z))) prf
    -- (power≡ prf)
        --Σ≡Prop (λ x → isPropΠ2 λ y z → isProp→ (isProp→ (∈-isProp x z))) prf

    open import Cubical.Functions.Logic 
    open import Cubical.Data.Unit
    open import  Cubical.HITs.PropositionalTruncation renaming (map to Hmap ; map2 to Hmap2 ; elim to Helim ; rec to Hrec)
    open import Cubical.Data.Sum renaming (rec to Srec ; map to Smap)
    
    _∪_ : {X : Set} → ℙ X → ℙ X → ℙ X 
    A ∪ B = λ x → A x ⊔ B x

    _∪↑_ : {P : Preorder _ _ } → ↑ P → ↑ P → ↑ P 
    _∪↑_ {P} (A , prfA)(B , prfB) = ((A ∪ B)) , prfA∪B where 
    
        prfA∪B : (x y : fst P) → x ∈ (A ∪ B) → snd P ._≤_ x y → y ∈ (A ∪ B) 
        prfA∪B x y x∈A∪B x≤y = Hmap (Smap (λ x∈A → prfA x y x∈A x≤y) λ x∈B → prfB x y x∈B x≤y) x∈A∪B
    
    _∩_ : {X : Set} → ℙ X → ℙ X → ℙ X 
    A ∩ B = λ x → A x ⊓ B x

    _∩↑_ : {P : Preorder _ _ } → ↑ P → ↑ P → ↑ P 
    _∩↑_ {P} (A , prfA)(B , prfB) = ((A ∩ B)) , prfA∩B where 
    
        prfA∩B : (x y : fst P) → x ∈ (A ∩ B) → snd P ._≤_ x y → y ∈ (A ∩ B) 
        prfA∩B x y (x∈A , x∈B ) x≤y = prfA x y x∈A x≤y , prfB x y x∈B x≤y


    distrib₁ : {P : Preorder _ _ }{X Y : ↑ P} → (_∪↑_{P} X (_∩↑_{P} X Y)) ≡ X
    distrib₁ {P}{X}{Y} = 
        ↑≡ {P} (funExt λ x → 
            ⇔toPath 
                (Hrec (X .fst x .snd) (λ {(_⊎_.inl e) → e
                                        ; (_⊎_.inr (e , _)) → e}))
                λ e → ∣ _⊎_.inl e ∣₁)
    distrib₂ : {P : Preorder _ _ }{X Y : ↑ P} → (_∩↑_{P} X (_∪↑_{P} X Y)) ≡ X
    distrib₂ {P}{X}{Y} = ↑≡ {P} (funExt λ x → ⇔toPath fst λ e → e , ∣ _⊎_.inl e ∣₁)

    ≤Prop : {P : Preorder _ _ } → (x y : P .fst) → hProp _ 
    ≤Prop {P} x y = (P .snd ._≤_ x y) , P .snd .isPreorder .ipv  _ _ where 
        open import Cubical.Relation.Binary.Preorder
        open IsPreorder renaming (is-prop-valued to ipv)

    
    ≤P : (P : Preorder _ _ ) → fst P → fst P → Type
    ≤P P = P .snd ._≤_ 

    ≤-refl : (P : Preorder _ _ )(x : fst P ) → (≤P P x x)
    ≤-refl P = P .snd .isPreorder .(IsPreorder.is-refl)

    ≤-trans : (P : Preorder _ _ )(x y z : fst P ) → ≤P P x y → ≤P P y z → ≤P P x z
    ≤-trans P = P .snd .isPreorder .(IsPreorder.is-trans) 

    _⇒Power_ : {P : Preorder _ _ } → ℙ (P .fst) → ℙ(P .fst) → ℙ(P .fst) 
    _⇒Power_ {P} A B x = ∀[ y ∶ (fst P) ] ≤Prop {P} x y ⇒ (y ∈ A , ∈-isProp A y) ⇒ (y ∈ B , ∈-isProp B y)
    
    _⇒↑_ : {P : Preorder _ _ } → ↑ P → ↑ P → ↑ P 
    _⇒↑_ {P} (A , prfA) (B , prfB) = A ⇒P B , powerup where 


        _⇒P_ = _⇒Power_{P}

       
        powerup : (x y : fst P) → x ∈ (A ⇒P B) → ≤P P x y → y ∈ (A ⇒P B)
        powerup x y x∈A⇒B x≤y = λ z y≤z z∈A → x∈A⇒B z (≤-trans P x y z x≤y y≤z) z∈A

    ∅ : {A : Set} → ℙ A 
    ∅ x = ⊥ 

    upSetHA : Preorder _ _ → HeytingAlg 
    upSetHA P = ↑ P , g where
        open isHeytingAlg


        l : LatticeStr (↑ P) 
        l = latticestr 
            (∅ , λ _ _ ()) -- empty set for 0 
            ((λ x → ⊤) , λ _ _ _ _ → tt*)  -- the full set P for 1
            (_∪↑_{P}) 
            (_∩↑_{P}) 
            (islattice 
                (issemilattice 
                    (iscommmonoid 
                        (ismonoid 
                            (issemigroup 
                                (↑isSet {P})
                                λ X Y Z → ↑≡ {P}(funExt λ x → ⊔-assoc (X .fst x) (Y .fst x) (Z .fst x) )) 
                            (λ _ → ↑≡ {P} (funExt λ _ → ⊔-identityʳ _)) 
                            λ _ → ↑≡ {P} (funExt λ _ → ⊔-identityˡ _)) 
                        λ X Y → ↑≡ {P} (funExt λ x → ⊔-comm (X .fst x) (Y .fst x) )) 
                    λ X → ↑≡ {P} (funExt λ x → ⊔-idem (X .fst x))) 
                (issemilattice 
                    (iscommmonoid 
                        (ismonoid 
                            (issemigroup 
                                (↑isSet {P}) 
                                λ X Y Z → ↑≡ {P}(funExt λ x → ⊓-assoc (X .fst x) (Y .fst x) (Z .fst x) )) 
                            (λ _ → ↑≡ {P} (funExt λ _ → ⊓-identityʳ _)) 
                            λ _ → ↑≡ {P} (funExt λ _ → ⊓-identityˡ _)) 
                        λ X Y → ↑≡ {P} (funExt λ x → ⊓-comm (X .fst x) (Y .fst x) ))
                        λ X → ↑≡ {P} (funExt λ x → ⊓-idem (X .fst x))) 
                λ X Y → distrib₁ {P}{X}{Y} , distrib₂ {P}{X}{Y})

        g : isHeytingAlg (↑ P)
        g .islat = l
        g .⇒l  = _⇒↑_ {P}
        g .l₁ X = ↑≡ {P} (funExt λ x → ⇔toPath (λ _ → tt*) λ x₁ x₂ x₃ x₄ → x₄)
        g .l₂ X Y = ↑≡ {P} (funExt λ x → ⇔toPath (λ {(x∈X , f) → x∈X , f x (≤-refl P x) x∈X}) λ{ (x∈X , x∈Y) → x∈X , (λ y x≤y y∈X → Y .snd x y x∈Y x≤y) })
        g .l₃ X Y = ↑≡ {P} (funExt λ x → ⇔toPath fst λ x∈Y → Y .snd x x x∈Y (≤-refl P x) , λ y x≤y y∈X → Y .snd x y x∈Y x≤y )
        g .l₄ X Y Z = ↑≡ {P} (funExt λ x → 
            ⇔toPath 
                (λ x∈X⇒Y∩Z → (λ y x≤y y∈X → x∈X⇒Y∩Z y x≤y y∈X  .fst) , λ y x≤y y∈X → x∈X⇒Y∩Z y x≤y y∈X  .snd) 
                λ { (x∈X⇒Y , x∈X⇒Z) → λ y x≤y y∈X → x∈X⇒Y y x≤y y∈X , x∈X⇒Z y x≤y y∈X} )

-}
{- 
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

    propHA : isHeytingAlg (prop , {!   !})
    propHA = record { 
        islat = proplat ; 
        ⇒l = _⇒_ ; 
        l₁ = λ x → ⇔toPath (λ _ → tt*) λ x₁ x₂ → x₂ ; 
        l₂ = λ x y → ⇔toPath (λ p → (p .fst) , (p .snd) (p .fst)) λ {(p , q) → p , λ _ → q} ; 
        l₃ = λ x y → ⇔toPath fst λ z → z , λ _ → z ; 
        l₄ = ⇒-⊓-distrib }

    -- same one used in Iris as Upred Entails
    -- https://plv.mpi-sws.org/coqdoc/iris/iris.base_logic.upred.html#uPred_entails
    _≤p_ : prop → prop → Set 
    -- alternative (found on Wiki ..)
    -- This means that it is possible to deduce P from Q?
    -- p ⇒ q ≡ ⊤
    _≤p_ p q = (p ⇒ q) .fst
    -- Why this order?
    -- Sheaves Geo Logic
    --_≤p_ p q = p ⊓ q ≡ p

    propPre : Preorder _ _ 
    propPre = (prop , 
                    (preorderstr _≤p_ 
                        (ispreorder 
                            (λ a b → isProp→ (b .snd)) 
                            (λ a → λ z → z) 
                            λ a b c z z₁ z₂ → z₁ (z z₂))))



    --dumb : (A : Set)(Aprop : isProp A)(x y : A) → isProp(x ≡ y)
    --dumb A p x y = isOfHLevelPlus {1}{_}{A} 1 p x y where 

    open Cubical.Relation.Binary.Preorder.isUnivalent 
    open OrderEquivalent
    propPreorder : ob poset 
    propPreorder = propPre , record { univ = λ p q → record { equiv-proof = λ oe → 
                                uniqueExists 
                                (⇔toPath (oe .left) (oe .right)) 
                                (isPropOrderEquivalent _ _) 
                                (λ p≡q  → isOfHLevelPlus {1}{_}{OrderEquivalent propPre p q} 1 isPropOrderEquivalent (pathToOrderEquiv p≡q) oe)
                                λ p≡q p≡q≡oe → isSetHProp _ _ _ _ } }
                            

    -- instead of powerset, use down


    open PreorderStr
    open import Cubical.Foundations.Powerset
    -- carrier is powerset and order is subset
    funPropPoset : ob set → ob poset 
    funPropPoset X = pre , u where 

        -- X .fst → prop
        carrier = ℙ (X .fst)

        -- pointwise order
        {-prestr : PreorderStr ℓ-zero carrier
        prestr = preorderstr (λ f g → (x : X .fst) → (f x) ≤p (g x)) 
            (ispreorder (λ f g  → isPropΠ λ x → propPreorder .fst .snd .is-prop-valued (f x) (g x)) 
            (λ f x → propPreorder .fst .snd .is-refl (f x)) 
            λ f g h p q x → propPreorder .fst .snd .is-trans _ _ (h x) (p x) (q x))
            -}

        prestr' : PreorderStr ℓ-zero carrier
        prestr' = preorderstr _⊆_ (ispreorder ⊆-isProp ⊆-refl λ X Y Z X⊆Y Y⊆Z x x∈X → Y⊆Z x (X⊆Y x x∈X))
        
        pre : Preorder _ _ 
        pre = carrier , prestr'

        u : Cubical.Relation.Binary.Preorder.isUnivalent pre 
        u = record { univ = λ f g → record { equiv-proof = λ oe → 
                uniqueExists 
                    (funExt (λ x → ⇔toPath (oe .left x) (oe .right x))) 
                    ((isPropOrderEquivalent _ _)) 
                    {!   !}
                    {!   !} }} 

    funPropHA : (X : ob set) → isHeytingAlg (funPropPoset X .fst .fst , {!   !})
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

    all : isRightAdjointMon (𝓟 .F-hom (λ r → fst r)) 
    all = (record { f = {!   !} ; isMon = {!   !} }) , {!   !}
    
    open import  Cubical.HITs.PropositionalTruncation renaming (map to Hmap)
    open import  Cubical.Categories.Adjoint 
    open NaturalBijection
    setFO : FirstOrderHyperDoc set bp 
    setFO = record{ 
        𝓟 = 𝓟; 
        isHA = funPropHA; 
        isHomo = {!   !}; 
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


 -}




{-
    open FirstOrderHyperDoc setFO renaming (𝓟 to 𝓟s)

    open import Cubical.Categories.Instances.EilenbergMoore
    open import Cubical.Categories.Monad.Base
    open import Cubical.Categories.Instances.FunctorAlgebras
    open AlgebraHom
    open Algebra
    module cbpvLogic (M : Monad set) where
        EM : Category _ _ 
        EM = EMCategory M

        𝓕 : Functor set EM 
        𝓕 = FreeEMAlgebra M

        𝓤 : Functor EM set 
        𝓤 = ForgetEMAlgebra M

        -- stupidly long type checking...?
        𝓤op : Functor (EM ^op) (set ^op)
        𝓤op = {!   !} --  𝓤 ^opF  

        propEM : ob EM 
        propEM = (algebra (prop , isSetHProp) (λ x → ⊤)) , (proveEMAlgebra (funExt λ x → {!   !}) {!   !})

        emToPoset : ob EM → ob poset 
        emToPoset X = ((EM [ X , propEM ]) , (preorderstr (λ f g → (x : X .fst .carrier .fst) → {! carrierHom f x   !}) {!   !})) , {!   !}

        𝓟em : Functor (EM ^op) (POSET ℓ-zero ℓ-zero) 
        𝓟em = {!   !} --  𝓟s ∘F ( 𝓤 ^opF)

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



    -}
   