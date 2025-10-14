{-# OPTIONS --cubical --type-in-type --allow-unsolved-metas #-}
module src.Data.HyperDoctrine where 

    open import Cubical.Algebra.Lattice
    open import Cubical.Foundations.Prelude
    open import Cubical.Foundations.Structure
    open import Cubical.Categories.Instances.Posets.Base
    open import Cubical.Categories.Instances.Sets
    open import Cubical.Categories.Category
    open import Cubical.Categories.Functor
    open import Cubical.Categories.Instances.Preorders.Monotone hiding (_≤X_ ; _≤Y_)
    open import Cubical.Categories.Limits.BinProduct
    open BinProduct
    open import Cubical.Foundations.Powerset
    open Category
    open Functor
    open import Cubical.Algebra.Semilattice
    open import Cubical.Algebra.CommMonoid
    open import Cubical.Algebra.Monoid
    open import Cubical.Algebra.Semigroup
    open import Cubical.Data.Sigma
    open import Cubical.Relation.Binary.Preorder
    open import Cubical.Foundations.Isomorphism
    open import Cubical.Relation.Binary.Preorder renaming (isUnivalent to isUniv)
    open import Cubical.Data.Sigma
    open import Cubical.Categories.Limits.Terminal
    open import Cubical.Categories.Exponentials
    open import Cubical.Categories.Adjoint
    open import Cubical.Data.Sigma
    open import Cubical.Foundations.HLevels

    
    module bpOps (𝓒 : Category _ _ )(bp : BinProducts 𝓒)  where 
        _×𝓒_ : ob 𝓒 → ob 𝓒 → ob 𝓒 
        _×𝓒_ x y = bp x y .binProdOb


        π₁ : {X Y : ob 𝓒} → 𝓒 [ X ×𝓒 Y , X ]
        π₁  {X} {Y} = bp X Y .binProdPr₁

        π₂ : {X Y : ob 𝓒} → 𝓒 [ X ×𝓒 Y , Y ]
        π₂  {X} {Y} = bp X Y .binProdPr₂

        Δ : (X : ob 𝓒) → 𝓒 [ X , bp X X .binProdOb ]
        Δ X = bp X X .univProp (𝓒 .id{X}) (𝓒 .id{X}) .fst .fst

        bimap : {X Y Z W : ob 𝓒} → 𝓒 [ X , Z ] → 𝓒 [ Y , W ] → 𝓒 [ bp X Y .binProdOb , bp Z W .binProdOb ]
        bimap {X}{Y}{Z}{W} f g = bp Z W .univProp (π₁ {X} {Y} ⋆⟨ 𝓒 ⟩ f) (π₂ {X} {Y} ⋆⟨ 𝓒 ⟩ g) .fst .fst

    module bptOps (𝓒 : Category _ _ )(bp : BinProducts 𝓒)(term : Terminal 𝓒)  where

        open bpOps 𝓒 bp

        𝟙 : ob 𝓒 
        𝟙 = term .fst

        binop : {H : ob 𝓒} → 𝓒 [ H ×𝓒 H , H ] → (x y : 𝓒 [ 𝟙 , H ]) → 𝓒 [ 𝟙 , H ]
        binop op x y =  Δ 𝟙 ⋆⟨ 𝓒 ⟩ bimap x y ⋆⟨ 𝓒 ⟩ op


    open PreorderStr
    open NaturalBijection

    poset = POSET _ _ 
    set = SET _

   -- isPoset : Set → Set 
   -- isPoset X = Σ[ P ∈ PreorderStr _ X ] isUniv (X , P)
    
    open import src.Data.HeytingAlg
            
    record IsHAHom 
        {A : hSet _} {B : hSet _} 
        (L : isHeytingAlg A) 
        (f : A .fst → B .fst) 
        (M : isHeytingAlg B) : Set where
        open isHeytingAlg 
        field 
            islatHom : IsLatticeHom (L .islat) f (M .islat)
            presImp : (x y : A .fst) → f (L .⇒l x y) ≡ M .⇒l (f x) (f y)

            


    -- This is just a Galois connection?
    record adjMon {X Y : ob poset} (f : poset [ X , Y ])(g : poset [ Y , X ]) : Set where 
        Xob = X .fst .fst
        Yob = Y .fst .fst 
        _≤X_ = X .fst .snd ._≤_ 
        _≤Y_ = Y .fst .snd ._≤_ 
        f' = MonFun.f f 
        g' = MonFun.f g
        
        field 
            -- the iso, the section and retraction don't matter (prop valued)
            fwd : {x : Xob}{y : Yob} → (f' x) ≤Y y → x ≤X (g' y)
            bkwd : {x : Xob}{y : Yob} → x ≤X (g' y) → (f' x) ≤Y y
            -- neither do 
            --adjNatInD
            --adjNatInC

    isLeftAdjointMon : {X Y : ob poset} → poset [ X , Y ] → Set 
    isLeftAdjointMon {X} {Y} f = Σ[ g ∈ poset [ Y , X ] ] adjMon {X} {Y} f g
    
    isRightAdjointMon : {X Y : ob poset} → poset [ Y , X ] → Set 
    isRightAdjointMon {X} {Y} g = Σ[ f ∈ poset [ X , Y ] ] adjMon {X} {Y} f g

    record FirstOrderHyperDoc (𝓒 : Category _ _ )(bp : BinProducts 𝓒) : Set where 
        open bpOps 𝓒 bp
        field 
            𝓟 : Functor (𝓒 ^op) (POSET _ _)
            𝓟_isSet : (X : ob 𝓒) → isSet (𝓟 .F-ob X .fst .fst) 
            isHA : (X : ob 𝓒) → isHeytingAlg (𝓟 .F-ob X  .fst .fst , 𝓟_isSet X )
            isHomo : {X Y : ob 𝓒} → (f : 𝓒 [ X , Y ]) → IsHAHom  (isHA Y) (MonFun.f (𝓟 .F-hom f)) (isHA X)

            eq : {X : ob 𝓒} → isRightAdjointMon  {𝓟 .F-ob X}{𝓟 .F-ob (X ×𝓒 X)} (𝓟 .F-hom (Δ X))

            quant : {Γ X : ob 𝓒} → 
                    (isLeftAdjointMon  {𝓟 .F-ob Γ} {𝓟 .F-ob (Γ ×𝓒 X)}(𝓟 .F-hom π₁))
                × 
                    (isRightAdjointMon  {𝓟 .F-ob (Γ ×𝓒 X)}{𝓟 .F-ob Γ} (𝓟 .F-hom π₁))

                    
        ∃F : {Γ X : ob 𝓒} → MonFun (𝓟 .F-ob ( Γ ×𝓒 X) .fst) ((𝓟 .F-ob Γ) .fst)
        ∃F {Γ} {X} = quant .fst .fst

        ∀F : {Γ X : ob 𝓒} → MonFun (𝓟 .F-ob ( Γ ×𝓒 X) .fst) ((𝓟 .F-ob Γ) .fst)
        ∀F {Γ} {X} = quant .snd .fst

        =F : {X : ob 𝓒} → MonFun ((𝓟 .F-ob X) .fst) (𝓟 .F-ob ( X ×𝓒 X) .fst)
        =F {X}  = eq  .fst
        
        field
            beck₁ : {Γ Γ' X : ob 𝓒}{s : 𝓒 [ Γ , Γ' ]} → 
                    (∃F {Γ'} {X}) 
                        ⋆⟨ poset ⟩ 
                    𝓟 .F-hom s 
                 ≡ 
                    𝓟 .F-hom (bimap s (𝓒 .id)) 
                        ⋆⟨ poset ⟩ 
                    (∃F {Γ} {X} )
            beck₂ : {Γ Γ' X : ob 𝓒}{s : 𝓒 [ Γ , Γ' ]} → 
                    (∀F {Γ'} {X}) 
                        ⋆⟨ poset ⟩ 
                    𝓟 .F-hom s 
                 ≡ 
                    𝓟 .F-hom (bimap s (𝓒 .id)) 
                        ⋆⟨ poset ⟩ 
                    (∀F {Γ} {X})

    module InternalHADef
        (𝓒 : Category _ _ )
        (term : Terminal 𝓒)
        (bp : BinProducts 𝓒) where 
        
        open bpOps 𝓒 bp
        open bptOps 𝓒 bp term

        -- what about completeness
        record InternalHA (H : ob 𝓒): Set where 
            field 
                top bot : 𝓒 [ 𝟙 , H ]
                and or imp : 𝓒 [ H ×𝓒 H , H ]

            and' : (x y  : 𝓒 [ 𝟙 , H ]) → 𝓒 [ 𝟙 , H ]
            and' x y = binop and x y

            or' : (x y  : 𝓒 [ 𝟙 , H ]) → 𝓒 [ 𝟙 , H ]
            or' x y = binop or x y

            imp' : (x y  : 𝓒 [ 𝟙 , H ]) → 𝓒 [ 𝟙 , H ]
            imp' x y = binop imp x y
            
            field 

                and-assoc : (x y z : 𝓒 [ 𝟙 , H ]) → and' x (and' y z) ≡ and' (and' x y) z
                and-comm : (x y : 𝓒 [ 𝟙 , H ]) → and' x y ≡ and' y x
                and-idem : (x : 𝓒 [ 𝟙 , H ]) → and' x x ≡ x
                and-unit : (x : 𝓒 [ 𝟙 , H ]) → and' x top ≡ x 

                or-assoc : (x y z : 𝓒 [ 𝟙 , H ]) → or' (or' x y) z ≡ or' x (or' y z)
                or-comm : (x y : 𝓒 [ 𝟙 , H ]) → or' x y ≡ or' y x
                or-idem : (x : 𝓒 [ 𝟙 , H ]) → or' x x ≡ x
                or-unit : (x : 𝓒 [ 𝟙 , H ]) → or' x bot ≡ x

                abs₁ : (x y : 𝓒 [ 𝟙 , H ]) → and' x (or' y x) ≡ x
                abs₂ : (x y : 𝓒 [ 𝟙 , H ]) → or' (and' x y) x ≡ x

                l₁ : (x : 𝓒 [ 𝟙 , H ]) → imp' x x ≡ top
                l₂ : (x y : 𝓒 [ 𝟙 , H ]) → and' x (imp' x y) ≡ and' x y
                l₃ : (x y : 𝓒 [ 𝟙 , H ]) → and' y (imp' x y) ≡ y 
                l₄ : (x y z : 𝓒 [ 𝟙 , H ]) → imp' x (and' y z) ≡ and' (imp' x y) (imp' x z) 


    record HyperDoctrine 
        (𝓒 : Category _ _ ) 
        (term : Terminal 𝓒)
        (bp : BinProducts 𝓒)
        (exp : Exponentials 𝓒 bp ) : Set where    
        
        open FirstOrderHyperDoc 
        open InternalHADef 𝓒 term bp

        field 
            isFO : FirstOrderHyperDoc 𝓒 bp
            H : Σ[ H ∈ ob 𝓒 ] InternalHA H
            -- should be "natural bijection"
            Θ : (X : ob 𝓒) → Iso (isFO .𝓟 .F-ob X .fst .fst) (𝓒 [ X , H .fst ]) 


{-     -- Theorem 4.6 a taste of categorical logic
    -- let H be any complete Heyting Algebra, 
    -- Then Set together with a functor Hom_Set[_,H] and generic object H
    -- is a hyperdoctrine
    
    record HomHyperDoc 
        (𝓒 : Category _ _ ) 
        (term : Terminal 𝓒)
        (bp : BinProducts 𝓒)
        (exp : Exponentials 𝓒 bp ) : Set where -}




    --    (Ω : ob 𝓒)
       -- (≤Hom : (X : ob 𝓒) → isPoset (𝓒 [ X , Ω ])) : Set where    
{-}
        open FirstOrderHyperDoc
        𝓟' : Functor (𝓒 ^op) (POSET ℓ-zero ℓ-zero)
        𝓟' .F-ob X = ((𝓒 [ X , Ω ]) , ≤Hom X .fst) , ≤Hom X .snd
        𝓟' .F-hom f  = record { f = λ g → f ⋆⟨ 𝓒 ⟩ g ; isMon = λ x₁ → {!   !} } where 
            open import Cubical.Categories.Instances.Preorders.Monotone
        𝓟' .F-id = {!   !}
        𝓟' .F-seq = {!   !}

        fo : FirstOrderHyperDoc 𝓒 bp 
        fo .𝓟 = {! HomFunctor  !}
        fo .isHA = {!   !}
        fo .isHomo = {!   !}
        fo .eq = {!   !}
        fo .quant = {!   !}
        fo .beck₁ = {!   !}
        fo .beck₂ = {!   !}

-}



{-
    -- Cruft, posets as categories

    
    toCat : ob poset → Category _ _ 
    toCat P .ob = P .fst .fst
    toCat P .Hom[_,_] = P .fst .snd ._≤_
    toCat P .id = P .fst .snd .is-refl _
    toCat P ._⋆_ = P .fst .snd .is-trans _ _ _
    toCat P .⋆IdL f = P .fst .snd .is-prop-valued _ _ _ _
    toCat P .⋆IdR f = P .fst .snd .is-prop-valued _ _ _ _
    toCat P .⋆Assoc f g h = P .fst .snd .is-prop-valued _ _ _ _
    toCat P .isSetHom = isProp→isSet (P .fst .snd .is-prop-valued _ _)

    toFun : {x y : ob poset}→ (f : poset [ x , y ]) → Functor (toCat x) (toCat y)
    toFun f .F-ob = MonFun.f f
    toFun {x} {y} f .F-hom g = MonFun.isMon {_}{_}{x .fst} {y .fst} f g
    toFun {x}{y} f .F-id {x'}=  y .fst .snd .is-prop-valued _ _ _ _
    toFun {x}{y} f .F-seq g h = y .fst .snd .is-prop-valued _ _ _ _

    open import Cubical.Foundations.Isomorphism

    open MonFun

    toMon : {x y : ob poset} → Functor (toCat x) (toCat y) → MonFun (x .fst) (y .fst)
    toMon F .f = F .F-ob
    toMon F .isMon = F .F-hom

    MonFunIso : {x y : ob poset} → Iso (poset [ x , y ]) (Functor (toCat x) (toCat y)) 
    MonFunIso {x} {y} = 
        iso 
            (toFun {x} {y}) 
            (toMon {x} {y}) 
            (λ F → Functor≡ (λ _ → refl) λ _ → refl) 
            λ f → eqMon _ _  refl



    -- adjMon is enough
    module example {X Y : ob poset} (f : poset [ X , Y ])(g : poset [ Y , X ])(adj : adjMon {X}{Y} f g) where 

        open adjMon
        prf : toFun {X} {Y} f ⊣ toFun {Y} {X} g
        prf = record { 
                adjIso = 
                    iso 
                    (adj .fwd) 
                    (adj .bkwd) 
                    (λ _ → X .fst .snd .is-prop-valued _ _ _ _) 
                    (λ _ → Y .fst .snd .is-prop-valued _ _ _ _) ; 
                adjNatInD = λ _ _ → (X .fst .snd .is-prop-valued _ _ _ _) ; 
                adjNatInC = λ _ _ → (Y .fst .snd .is-prop-valued _ _ _ _) } 

    
            

        ∃F : {Γ X : ob 𝓒} → (π : 𝓒 [ Γ ×𝓒 X , Γ ]) → Functor (toCat (𝓟 .F-ob ( Γ ×𝓒 X))) (toCat (𝓟 .F-ob Γ)) 
        ∃F π  = quant π .fst .fst

        ∀F : {Γ X : ob 𝓒} → (π : 𝓒 [ Γ ×𝓒 X , Γ ]) → Functor (toCat (𝓟 .F-ob ( Γ ×𝓒 X))) (toCat (𝓟 .F-ob Γ))
        ∀F π = quant π .snd .fst

        =F : {X : ob 𝓒} → (Δ : 𝓒 [ X , X ×𝓒 X ]) → Functor (toCat (𝓟 .F-ob X)) (toCat (𝓟 .F-ob ( X ×𝓒 X))) 
        =F Δ = eq  Δ .fst

        π₁ : {X Y : ob 𝓒} → 𝓒 [ X ×𝓒 Y , X ]
        π₁ {X} {Y} = bp X Y .binProdPr₁

        field
            bimap : {X Y W Z : ob 𝓒} → 𝓒 [ X , Y ] → 𝓒 [ W , Z ] → 𝓒 [ X ×𝓒 W , Y ×𝓒 Z ]       
            beck₁ : {Γ Γ' X : ob 𝓒}{s : 𝓒 [ Γ , Γ' ]} → 
                    toMon {𝓟 .F-ob (Γ' ×𝓒 X)} {𝓟 .F-ob Γ'} (∃F {Γ'} {X} (π₁ {Γ'} {X})) 
                        ⋆⟨ poset ⟩ 
                    𝓟 .F-hom s 
                 ≡ 
                    𝓟 .F-hom (bimap s (𝓒 .id)) 
                        ⋆⟨ poset ⟩ 
                    toMon {𝓟 .F-ob (Γ ×𝓒 X)} {𝓟 .F-ob Γ} (∃F {Γ} {X} (π₁ {Γ} {X}))

            beck₂ : {Γ Γ' X : ob 𝓒}{s : 𝓒 [ Γ , Γ' ]} → 
                    toMon {𝓟 .F-ob (Γ' ×𝓒 X)} {𝓟 .F-ob Γ'} (∀F {Γ'} {X} (π₁ {Γ'} {X})) 
                        ⋆⟨ poset ⟩ 
                    𝓟 .F-hom s 
                 ≡ 
                    𝓟 .F-hom (bimap s (𝓒 .id)) 
                        ⋆⟨ poset ⟩ 
                    toMon {𝓟 .F-ob (Γ ×𝓒 X)} {𝓟 .F-ob Γ} (∀F {Γ} {X} (π₁ {Γ} {X}))
-}