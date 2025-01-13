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
        universal  = λ A → record { equiv-proof = λ f → 
            uniqueExists 
                (λ z y → f (z , y))
                refl 
                ((λ a' x y → set .isSetHom  _ _ x y)) 
                λ Z→Y→X p → funExt λ z → funExt λ y → funExt⁻ (sym p)  (z , y) }}
        


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
                    {!   !} } }

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


    module simplelang where

        data U : Set where 
            unit bool : U
            prod arr : U → U → U

        El : U → Set 
        El unit = Unit 
        El bool = Bool
        El (arr x y) = El x → El y
        El (prod x y) = El x × El y


        -- closed terms
        {-
        data terms : U → Set where 
            var : {t : U} → El t → terms t
            u : El unit → terms unit
            tru : El bool → terms bool
            fls : El bool → terms bool
            pair : {t1 t2 : U} → El t1 → El t2 → terms (prod t1 t2)
            lam : {t1 t2 : U} → (El t1 → terms t2) → terms (arr t1 t2)

        _ : terms (arr unit (arr unit (prod unit unit))) 
        _ = lam λ x → lam λ y → pair x y
        -}
        open import Cubical.Data.List 
        open import Cubical.Data.Fin renaming (elim to felim)
        open import Cubical.Data.Nat
        open import Cubical.Data.FinData.Base renaming (Fin to FinData) hiding (¬Fin0 ; toℕ)
        
        pattern z = (zero , _)
        pattern sc n = (suc n , _)
        
        
        Ctx : Set
        Ctx = Σ[ n ∈ ℕ ] (Fin n → U)

        ctxToU : Ctx → U 
        ctxToU (zero , f) = unit
        ctxToU (suc n , f) = sumFinGen prod unit f

        module demo where 

            -- why doesn't pattern matching pick up on the impossiblity of the last cases here?
            asdfadf : Fin 2 → U 
            asdfadf (zero , snd₁) = unit
            asdfadf (suc zero , snd₁) = bool
            asdfadf (suc (suc zero) , fst₁ , snd₁) = {!   !} 
            asdfadf _ = {!   !}

            -- FinDataIsoFin
            also : Fin 2 → U 
            also = felim (λ _ → U) unit {!   !}

            ctx : Ctx 
            ctx = 2 , asdfadf

            _ = {! ctxToU ctx  !}
            -- {!   !} where
           -- _ : U
           -- _ = felim (λ x → U) unit (λ{k} → λ {fn} → prod (f (k , {!   !}))) {!   !}

        -- We want this to be somethin
        ectx : Ctx 
        ectx = 0 , felim (λ _ → U) unit (λ z → z) {0}
        

        open import Cubical.Data.Nat.Order
        
        upd : {n : ℕ}(f : Fin n → U)(u : U) → (Fin (suc n) → U)
        upd {n} f u (zero , _) = u
        upd {n} f u (suc m , d) = f (m , pred-≤-pred d)


        upd' : Ctx → U → Ctx 
        upd' (n , γ) u = (suc n) , upd γ u
       

        listToCtx : List U → Ctx 
        listToCtx [] = ectx
        listToCtx (x ∷ xs) = (suc (hm .fst)) , (upd (hm .snd) x) where 
            hm : Ctx
            hm = listToCtx xs


           -- m : Fin (suc (length xs)) → U 
           -- m ((length xs), D)= {!   !}
          --  m _ = ?
            --(length xs) , felim  {!   !} {!   !} {!   !} {!   !}

        elCtx : Ctx → Set 
        elCtx (n , γ) = (i : Fin n) → El (γ i)


        fillList : (L : List U) → elCtx (listToCtx L)
        fillList [] = λ i → {!   !}
        fillList (x ∷ L₁) = λ i → {! !}

        open import Cubical.Data.Empty renaming (⊥ to Empty ; rec to emptyrec)
        
        asProd : Ctx → Set 
        asProd (n , Γ) = sumFinGen _×_ Unit λ i → El (Γ i)

        module _ where
            d : asProd (listToCtx (unit ∷ bool ∷ []) )
            d = true , (tt , tt)


        _∘s_ : {A B C : Set} → (A → B) → (B → C) → A → C 
        _∘s_ f g = λ z → g (f z)

        
        open Iso renaming (fun to fwd)
        module _ (n : ℕ)(Γ : Fin (suc n) → U) where 
            
            toProd : ((x : Fin (suc n)) → (Γ ∘s El) x) → (Γ ∘s El) fzero × ((x : Σ ℕ _) → (Γ ∘s El) (fsuc x))
            toProd = CharacΠFinIso n { Γ ∘s El} .fwd
            {- CharacΠFinIso : ∀ {ℓ} (n : ℕ) {B : Fin (suc n) → Type ℓ}
  → Iso ((x : _) → B x) (B fzero × ((x : _) → B (fsuc x)))
   -}

        -- a term is a map from gamma to a type
        -- these are open terms since there is no gamma
        data terms : Ctx → U → Set where 
            u : {Γ : Ctx} → El unit → terms Γ unit
            b : {Γ : Ctx} → El bool → terms Γ bool 
            pair : {Γ : Ctx}{t1 t2 : U} → terms Γ t1 → terms Γ t2 → terms Γ (prod t1 t2)
            fun : {Γ : Ctx}{t1 t2 : U} → (El t1 → terms Γ t2) → terms Γ (arr t1 t2)
            -- this seems like cheatin..
           -- const : {Γ : Ctx}{t : U} → El t → terms Γ t
            var : {(n , Γ) : Ctx} → (i : Fin n) → terms (n , Γ) (Γ i)
            --var : {(n , Γ) : Ctx} → (γ : elCtx Γ → ) → terms (n , Γ) (Γ i)
          --  lam : {γ : Ctx}{t1 t2 : U} →(El t1 → terms γ t2) → terms γ (arr t1 t2)
           -- lam : {γ : Ctx}
        --   lam : {t1 t2 : U} → (El t1 → terms t2) → terms (arr t1 t2)
    {-}    data Singleton {a} {A : Set a} (x : A) : Set a where
            _with≡_ : (y : A) → x ≡ y → Singleton x

        inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
        inspect x = x with≡ refl -}

        denote : {Γ : Ctx}{ty : U} → terms Γ ty → (elCtx Γ → El ty) --set [ elCtx Γ , El ty ] 
        denote (u x) γ = x
        denote (b x) γ = x
        denote (pair M1 M2) γ = denote M1 γ , denote M2 γ
        denote (fun f) γ = λ x → denote (f x) γ
        denote (var i) γ = γ i

        module denoteToCCC where 
            -- really this is just El, but with the extra isSet
            denTy : U → ob set 
            denTy unit = Unit , isSetUnit
            denTy bool = Bool , isSetBool
            denTy (prod d₁ d₂) = denTy d₁ ×s denTy d₂
            denTy (arr d₁ d₂) = (denTy d₁ .fst → denTy d₂ .fst) , {!   !}
            
            -- need to make Γ to product
            den : {Γ : Ctx}{ty : U} → terms Γ ty → set .Hom[_,_] {! denTy Γ  !} {!   !} 
            den = {!   !}


        -- terms that dont use the context
        pure : {Γ : Ctx}{ty : U} → El ty → terms Γ ty 
        pure {Γ} {unit} x = u x
        pure {Γ}{bool} x = b x
        pure {Γ}{prod ty ty₁} (x , y) = pair (pure x) (pure y)
        pure {Γ}{arr ty ty₁} f = fun λ x → pure (f x)


    {-}
        lft : {Γ : Ctx}{ty : U} → (elCtx Γ → El ty) → terms Γ ty 
        lft {Γ} {unit} f = u (f λ i → {!   !})
        lft {Γ} {bool} f = {!   !}
        lft {Γ} {prod ty ty₁} f = {!   !}
        lft {Γ} {arr ty ty₁} f = {!   !}

-}

        _ : terms (listToCtx (unit ∷ bool ∷ [])) (prod unit bool) 
        _ = pair (var 0) (var 1)

        module _ {a b} {A : Set a} {B : A → Set b} where

            data Graph (f : ∀ x → B x) (x : A) (y : B x) : Set b where
                ingraph : f x ≡ y → Graph f x y

            inspect : (f : ∀ x → B x) (x : A) → Graph f x (f x)
            inspect _ _ = ingraph refl

        closedTerm : {Γ : Ctx}{t : U} → (M : terms Γ t) → elCtx Γ → terms ectx t
        closedTerm {n , Γ} {.unit} (u x) γ = u x
        closedTerm {n , Γ} {.bool} (b x) γ = b x
        closedTerm {n , Γ} {_} (pair x y) γ = pair (closedTerm x γ) (closedTerm y γ) 
        closedTerm {n , Γ} {_} (fun f) γ = fun λ x → closedTerm (f x) γ

        -- Heres where we eliminate variables using the context
        closedTerm {n , Γ} {.(Γ i)} (var i) γ with (Γ i) | inspect Γ i
        closedTerm {n , Γ} {.(Γ i)} (var i) γ | unit | ingraph p = pure (subst El p (γ i))
        closedTerm {n , Γ} {.(Γ i)} (var i) γ | bool | ingraph p = pure (subst El p (γ i))
        closedTerm {n , Γ} {.(Γ i)} (var i) γ | prod t1 t2 | ingraph p  = pure (((subst El p (γ i)) .fst) , ((subst El p (γ i)) .snd))
        closedTerm {n , Γ} {.(Γ i)} (var i) γ | arr t1 t2 | ingraph p = pure (subst El p (γ i))  


        example : terms (listToCtx (unit ∷ bool ∷ [])) (arr unit (prod bool unit)) 
        example = fun λ x → pair (var 1) (pure x)

        
        _ = {! upd' ectx bool  !}

        pattern z = (zero , _)
        pattern sc n = (suc n , _)

        module foo where 
            ctx : Ctx 
            ctx = listToCtx ( bool ∷ unit ∷ [])

            filled : elCtx ctx 
            filled z = true 
            filled (sc n) = {! tt  !}

        _ = closedTerm example {!   !}

        homadj : {Γ : List U}{A B : U} → Iso (terms (listToCtx (Γ ++ [ A ])) B) (terms (listToCtx Γ) (arr A B)) 
        homadj = iso 
                    (λ x → fun λ a → {!   !} )--pure (denote x {!   !})) 
                    (λ x → pure (denote x {!   !} {!   !})) 
                    {!   !} 
                    {!   !}

       -- closedTerm {(n , Γ)}{t} M γ with (Γ i) | inspect ? ? 
     --   closedTerm {(n , Γ)}{t} M γ | unit | _ = ?

        

      --  closedTerm (const x) γ = const x
        
        {-closedTerm {(n , Γ)} (var i) γ with inspect (Γ i)
        closedTerm {n , Γ} (var i) γ | (unit with≡ p)= goal where 
            goal : terms ectx unit 
            goal = {!   !}
        
        --subst (λ u → terms ectx u) (sym p) {! u (γ i)  !}
        closedTerm {n , Γ} (var i) γ | (bool with≡ p) = {!   !}
        closedTerm {n , Γ} (var i) γ | (prod d d₁) with≡ p = {!   !}
        closedTerm {n , Γ} (var i) γ | (arr d d₁) with≡ p = {!   !} -}

        _ : terms ectx unit
        _ = u tt

        -- no.. we want to distinguist this from arr
       -- _ : terms ectx (arr unit unit)
       -- _ = const λ x → x
{-
        adjl : (γ : Ctx)(t1 t2 : U)(M : terms γ (arr t1 t2)) → terms (upd' γ t1) t2 
        adjl γ t1 t2 M = {! M  !}
        
        _ : terms ectx unit
        _ = u tt

        _ : terms (listToCtx (bool ∷ unit ∷ [])) unit
        _ = var (fromNat 1)

        _ = {! lam ?  !}

-}
  

        
  