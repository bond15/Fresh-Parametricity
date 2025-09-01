{-# OPTIONS --type-in-type #-}
module src.Data.HoffmanStreicher where
    open import Cubical.Categories.Instances.Sets
    open import Cubical.Categories.Category hiding (isUnivalent)
    open Category
    open import Cubical.Categories.Functor
    open Functor
    open import Cubical.Categories.Instances.Functors
    open import Cubical.Functions.Logic
    open import Cubical.Foundations.HLevels
    open import Cubical.Data.Sigma
    open import Cubical.Foundations.Prelude
    open import Cubical.Categories.Presheaf.Base
    open import Cubical.Categories.Presheaf.Constructions
    open import Cubical.Categories.Displayed.Constructions.Comma
    open import Cubical.Categories.NaturalTransformation renaming (_⇒_ to _⇒nat_ )
    open import Cubical.Categories.Functor.Properties
    open import Cubical.Categories.Functors.Constant
    open import Cubical.Categories.Displayed.Base
    open import src.Data.HyperDoctrine
    open NatTrans
    open import Cubical.Data.Sum renaming (map to map⊎ ; rec to rec⊎ ; inl to inl⊎ ; inr to inr⊎)
    open import Cubical.HITs.PropositionalTruncation
    open import Cubical.Categories.Instances.Posets.Base
    open import Cubical.Relation.Binary.Preorder
    open isUnivalent
    open import Cubical.Data.Unit 
    open import Cubical.Foundations.Isomorphism
    open import Cubical.Categories.Instances.Preorders.Monotone
    open import Cubical.Algebra.Lattice
    open import Cubical.Algebra.Semilattice 
    open import Cubical.Algebra.CommMonoid
    open import Cubical.Algebra.Monoid
    open import Cubical.Algebra.Semigroup
    
    PropCat : Category _ _ 
    PropCat .ob = hProp _
    PropCat .Hom[_,_] (x , _) (y , _)= x → y
    PropCat .id x = x
    PropCat ._⋆_ = λ f g z → g (f z) 
    PropCat .⋆IdL _ = refl
    PropCat .⋆IdR _ = refl
    PropCat .⋆Assoc _ _ _ = refl
    PropCat .isSetHom {x}{y} = isProp→isSet (isProp→ (snd y))

    module foo (𝒞 : Category _ _ ) where 

        open import src.Data.PresheafCCC
        open import Cubical.Categories.Limits.Terminal
        open import Cubical.Categories.Limits.BinProduct
        open BinProduct

        -- covarient presheaves category
        Psh : Category _ _ 
        Psh = PresheafCategory (𝒞 ^op) _

        termPsh : Terminal Psh
        termPsh = ⊤𝓟 {C = 𝒞 ^op} {_}

        bpPsh : BinProducts Psh
        bpPsh = ×𝓟 {C = 𝒞 ^op} {_}

        open Ops Psh termPsh bpPsh
        
        -- coslice
        _↓𝒞 : (X : ob 𝒞) → Category _ _ 
        _↓𝒞 X = Comma (Constant 𝒞 𝒞 X) 𝟙⟨ 𝒞 ⟩

        -- "change of base" coslice category
        com : {x y : ob 𝒞} → (f : 𝒞 [ x , y ]) → Functor (y ↓𝒞) (x ↓𝒞)
        -- just precompose with f
        com {x} {y} f .F-ob ((z1 , z2) , y→z2) = (z1 , z2) , f ⋆⟨ 𝒞 ⟩ y→z2
        com {x} {y} f .F-hom {y→z₁} {y→z₂} ◀yz₁z₂ = (doesntmatter , z₁→z₂) , goal where 

            z₁ : ob 𝒞 
            z₁ = y→z₁ .fst .snd

            z₂ : ob 𝒞 
            z₂ = y→z₂ .fst .snd 

            z₁→z₂ : 𝒞 [ z₁ , z₂ ]
            z₁→z₂ = ◀yz₁z₂ .fst .snd

            doesntmatter = ◀yz₁z₂ .fst .fst

            prf : (snd y→z₂) ≡ snd y→z₁ ⋆⟨ 𝒞 ⟩ z₁→z₂
            prf = sym (𝒞 .⋆IdL _ ) ∙ ◀yz₁z₂ .snd

            goal : (𝒞 ⋆ id 𝒞) ((𝒞 ⋆ f) (snd y→z₂)) ≡ (𝒞 ⋆ (𝒞 ⋆ f) (snd y→z₁)) (◀yz₁z₂ .fst .snd)
            goal = 𝒞 .⋆IdL _ ∙ cong (λ h → f ⋆⟨ 𝒞 ⟩ h) prf ∙ sym (𝒞 .⋆Assoc _ _ _ )
           
        com f .F-id = ΣPathP (refl , 𝒞 .isSetHom _ _ _ _)
        com f .F-seq = λ f g → ΣPathP (refl , 𝒞 .isSetHom _ _ _ _)

        lem1 : { x : ob 𝒞} → com (𝒞 .id{x}) ≡ 𝟙⟨ (x ↓𝒞) ⟩ 
        lem1 = Functor≡ (λ c→x → ΣPathP ((ΣPathP (refl , refl)) , 𝒞 .⋆IdL _)) λ f →  ΣPathP (refl , {!   !})
        
        --lem1 : {x : ob 𝒞}{F : Functor (x ↓𝒞) PropCat} → F ∘F (com (id 𝒞)) ≡ F
        --lem1 {x} {F} = {!   !}

        Prop𝓒 : ob Psh 
        Prop𝓒 .F-ob X = ob (FUNCTOR (_↓𝒞 X) PropCat) , isSetFunctor isSetHProp
        Prop𝓒 .F-hom {x}{y} f F = F ∘F (com f)
        -- is true
        Prop𝓒 .F-id = funExt λ F → cong (λ h → F ∘F h ) lem1 ∙ F-lUnit
           -- Functor≡  (λ _ →  {!   !})  {!   !}
        Prop𝓒 .F-seq = {!   !}


        -- IS (FUNCTOR (_↓𝒞 X) PropCat) a thin category / poset?
        cosliceFunEq : {x : ob 𝒞}{F G : Functor (x ↓𝒞) PropCat} → (∀ (o : (x ↓𝒞) .ob ) → F .F-ob o ≡ G .F-ob o) → F ≡ G 
        cosliceFunEq p = Functor≡ p (λ {c} {c'} f → isProp→PathP (λ i → isProp→ (p c' i .snd)) _ _)


        andProp𝓒 :  Psh [ Prop𝓒 ×𝓒 Prop𝓒 , Prop𝓒 ]
        andProp𝓒  .N-ob = λ{ x (F , G) → 
            record { 
                -- The important part is here, the pointwise AND of propositions
                F-ob = λ x→_ → (F .F-ob x→_) ⊓ (G .F-ob x→_) ; 
                F-hom = λ {x}{y} f → map-× (F .F-hom f) (G .F-hom f) ;
                F-id = cong₂ map-× (F .F-id) (G .F-id)  ; 
                F-seq = λ f g → cong₂ map-× (F .F-seq _ _) (G .F-seq _ _) }}
        andProp𝓒 .N-hom f = funExt λ _ → cosliceFunEq λ _ → refl

        map-⊔ : {a b c d : ob PropCat } → 
                (f : PropCat [ a , c ]) → 
                (g : PropCat [ b , d ]) → 
                PropCat [ a ⊔ b , c ⊔ d ] 
        map-⊔ {a} {b}{c}{d} f g = rec (snd (c ⊔ d)) λ{(inl⊎ x) → inl (f x)
                                                    ; (inr⊎ x) → inr (g x)}


        orProp𝓒 :  Psh [ Prop𝓒 ×𝓒 Prop𝓒 , Prop𝓒 ]
        orProp𝓒  .N-ob = λ{ x (F , G) → 
            record { 
                -- The important part is here, the pointwise OR of propositions
                F-ob = λ x→_ → (F .F-ob x→_) ⊔ (G .F-ob x→_) ; 
                F-hom = λ {x}{y} f → map-⊔ {F .F-ob x}{G .F-ob x}{F .F-ob y}{G .F-ob y} (F .F-hom f) (G .F-hom f) ; 
                F-id = cong₂ map-⊔ (F .F-id) (G .F-id) ∙ funExt λ _ → squash₁ _ _  ; 
                F-seq = λ f g → cong₂ map-⊔ (F .F-seq f g) (G .F-seq f g) ∙ funExt λ _ → squash₁ _ _ }}
        orProp𝓒 .N-hom f = funExt λ _ → cosliceFunEq λ _ → refl 

        impProp𝓒 :  Psh [ Prop𝓒 ×𝓒 Prop𝓒 , Prop𝓒 ]
        impProp𝓒  .N-ob = λ{ x (F , G) → 
            record { 
                -- The important part is here, the pointwise AND of propositions
                F-ob = λ x→_ → (F .F-ob x→_) ⇒ (G .F-ob x→_) ; 
                -- can't pre and post compose here, variance  mismatch
                F-hom = λ {x}{y} f → λ g  → {! F .F-hom f  !} ⋆⟨ PropCat ⟩ g ⋆⟨ PropCat ⟩ G .F-hom f ;-- map-× (F .F-hom f) (G .F-hom f) ;
                F-id = {!   !} ;--cong₂ map-× (F .F-id) (G .F-id)  ; 
                F-seq = λ f g → {!   !} }} --cong₂ map-× (F .F-seq _ _) (G .F-seq _ _) }}
        impProp𝓒 .N-hom f = funExt λ _ → cosliceFunEq λ _ → refl
        
        ⊤Prop𝓒 : Psh [ 𝟙 , Prop𝓒 ]
        ⊤Prop𝓒 = natTrans 
                (λ{x tt* → Constant _ _ ⊤}) 
                (λ f  → funExt λ {tt* → Functor≡ (λ c → refl) λ f → refl})

        open InternalHA

        Prop𝓒InternalHA : InternalHA Prop𝓒 
        Prop𝓒InternalHA .top = ⊤Prop𝓒
        Prop𝓒InternalHA .bot = natTrans 
                (λ{x tt* → Constant _ _ ⊥}) 
                λ f → funExt λ {tt* → Functor≡ (λ c → refl) λ f → refl}
        Prop𝓒InternalHA .and = andProp𝓒
        Prop𝓒InternalHA .or = orProp𝓒
        Prop𝓒InternalHA .imp = {!   !}
        Prop𝓒InternalHA .and-assoc x y z = 
            makeNatTransPath (funExt λ _ → funExt λ _ → 
                cosliceFunEq (λ _ → {!   !} )) -- and-assoc being annoying here
        Prop𝓒InternalHA .and-comm x y = 
            makeNatTransPath (funExt λ _ → funExt λ _ → 
                cosliceFunEq λ _ → ⊓-comm _ _)
        Prop𝓒InternalHA .and-idem x = 
            makeNatTransPath (funExt λ c → funExt λ _ → 
                cosliceFunEq λ _ → ⊓-idem _)
        Prop𝓒InternalHA .and-unit x = 
            makeNatTransPath (funExt λ c → funExt λ{tt* → 
                cosliceFunEq λ c→_ → ⊓-identityʳ _})
        Prop𝓒InternalHA .or-assoc = {!   !}
        Prop𝓒InternalHA .or-comm x y = 
            makeNatTransPath (funExt λ _ → funExt λ _ → 
                cosliceFunEq λ _ → ⊔-comm _ _)
        Prop𝓒InternalHA .or-idem x = 
            makeNatTransPath (funExt λ _ → funExt λ _ → 
                cosliceFunEq λ _ → ⊔-idem _)
        Prop𝓒InternalHA .or-unit x = 
            makeNatTransPath (funExt λ _ → funExt λ _ → 
                cosliceFunEq λ _ → ⊔-identityʳ _)
        Prop𝓒InternalHA .abs₁ = {!   !}
        Prop𝓒InternalHA .abs₂ = {!   !}
        Prop𝓒InternalHA .l₁ = {!   !}
        Prop𝓒InternalHA .l₂ = {!   !}
        Prop𝓒InternalHA .l₃ = {!   !}
        Prop𝓒InternalHA .l₄ = {!   !}


        ap : {a b c : ob Psh} → Psh [ a , b ] → Psh [ a , c ] → Psh [ a , b ×𝓒 c ]
        ap {a} f g = Δ a ⋆⟨ Psh ⟩ bimap f g

        module _ (X : ob Psh) where 
            ⊥hom = termPsh .snd X .fst ⋆⟨ Psh ⟩ Prop𝓒InternalHA .bot
            ⊤hom = termPsh .snd X .fst ⋆⟨ Psh ⟩ Prop𝓒InternalHA .top

            ∨hom : Psh [ X , Prop𝓒 ] → Psh [ X , Prop𝓒 ] → Psh [ X , Prop𝓒 ]
            ∨hom f g = ap f g ⋆⟨ Psh ⟩ Prop𝓒InternalHA .or  

            ∧hom : Psh [ X , Prop𝓒 ] → Psh [ X , Prop𝓒 ] → Psh [ X , Prop𝓒 ]
            ∧hom f g = ap f g ⋆⟨ Psh ⟩ Prop𝓒InternalHA .and 

                -- this is a hack that doesn't make use of the internal HA's laws
                -- Notice that it is the same proof the internal HA uses.. just different types
              --  makeNatTransPath (funExt λ c → funExt λ Xc → cosliceFunEq (λ c→_ → ⊓-identityʳ _))
                {- 
                Prop𝓒InternalHA .and-unit x = 
                    makeNatTransPath (funExt λ c → funExt λ{tt* → 
                        cosliceFunEq λ c→_ → ⊓-identityʳ _}) .. this is just the same law.. 
                -}
            ∨semiG : IsSemigroup ∨hom 
            ∨semiG = issemigroup 
                        (Psh .isSetHom) 
                        {!   !}

            ∨mon : IsMonoid ⊥hom ∨hom 
            ∨mon = ismonoid 
                    ∨semiG 
                    (λ f → makeNatTransPath (funExt λ c → funExt λ Xc → cosliceFunEq (λ c→_ → ⊔-identityʳ _))) 
                    (λ f → makeNatTransPath (funExt λ c → funExt λ Xc → cosliceFunEq (λ c→_ → ⊔-identityˡ _))) 

            ∨cmon : IsCommMonoid ⊥hom ∨hom 
            ∨cmon = iscommmonoid 
                        ∨mon 
                        ((λ f g → makeNatTransPath (funExt λ c → funExt λ Xc → cosliceFunEq (λ c→_ → ⊔-comm _ _))))

            ∨semiL : IsSemilattice ⊥hom ∨hom 
            ∨semiL = issemilattice 
                        ∨cmon 
                        (λ f → makeNatTransPath (funExt λ c → funExt λ Xc → cosliceFunEq (λ c→_ → ⊔-idem _)))

            ∧semiG : IsSemigroup ∧hom 
            ∧semiG = issemigroup 
                        (Psh .isSetHom) 
                        {!   !}

            ∧mon : IsMonoid ⊤hom ∧hom 
            ∧mon = ismonoid 
                    ∧semiG 
                    (λ f → makeNatTransPath (funExt λ c → funExt λ Xc → cosliceFunEq (λ c→_ → ⊓-identityʳ _))) 
                    (λ f → makeNatTransPath (funExt λ c → funExt λ Xc → cosliceFunEq (λ c→_ → ⊓-identityˡ _))) 

            ∧cmon : IsCommMonoid ⊤hom ∧hom 
            ∧cmon = iscommmonoid 
                        ∧mon 
                        ((λ f g → makeNatTransPath (funExt λ c → funExt λ Xc → cosliceFunEq (λ c→_ → ⊓-comm _ _))))

            ∧semiL : IsSemilattice ⊤hom ∧hom 
            ∧semiL = issemilattice 
                        ∧cmon
                        (λ f → makeNatTransPath (funExt λ c → funExt λ Xc → cosliceFunEq (λ c→_ → ⊓-idem _)))

            lat : IsLattice ⊥hom ⊤hom ∨hom ∧hom 
            lat = islattice 
                    ∨semiL 
                    ∧semiL
                    {!   !}

            lathom : LatticeStr (Psh [ X , Prop𝓒 ])
            lathom = latticestr 
                        ⊥hom
                        ⊤hom 
                        ∨hom 
                        ∧hom 
                        lat

            {- 
                    cosliceFunEq : {x : ob 𝒞}{F G : Functor (x ↓𝒞) PropCat} → (∀ (o : (x ↓𝒞) .ob ) → F .F-ob o ≡ G .F-ob o) → F ≡ G 
        cosliceFunEq p = Functor≡ p (λ {c} {c'} f → isProp→PathP (λ i → isProp→ (p c' i .snd)) _ _)
            -}

            hm : (c : ob 𝒞)(F G : Functor (c ↓𝒞) PropCat) → isProp(F ≡ G)
            hm c F G = {!   !}

            -- need a notion of internal preorder ?? 
            -- can't define an ordering on Prop𝓒 since Prop𝓒 is not a set!
            propOrder : Σ[ Pre ∈ Preorder _ _ ] isUnivalent Pre
            propOrder = ({! Prop𝓒  !} , {!   !}) , {!   !}

            pre : Σ[ Pre ∈ Preorder _ _ ] isUnivalent Pre
            -- Is this pointwise ordering?
            -- NO! this is discrete ordering! 
            pre = ((Psh [ X , Prop𝓒 ]) , 
                    preorderstr (λ F G → ∀ (c : ob 𝒞 )(Xc : X .F-ob c .fst) → F .N-ob c Xc ≡ G .N-ob c Xc)
                    (ispreorder (λ a b  → isPropΠ λ c → isPropΠ λ Xc → hm c _ _) (λ a c Xc  → refl) λ F G H prf1 prf2 c Xc  → prf1 c Xc ∙ prf2 c Xc)) , {!   !}

        PshHomsHA : (X : ob Psh) → isHeytingAlg (Psh [ X , Prop𝓒 ])
        PshHomsHA X = 
            record { 
                islat = lathom X ; 
                ⇒l = {!   !} ; 
                l₁ = {!   !} ; 
                l₂ = {!   !} ; 
                l₃ = {!   !} ; 
                l₄ = {!   !} }
        
        𝓟 : Functor (Psh ^op) (POSET ℓ-zero ℓ-zero)
        𝓟 .F-ob  = pre
        𝓟 .F-hom {F}{G} nGF = record { f = λ nFProp → nGF ⋆⟨ Psh ⟩ nFProp ; isMon = λ {P}{Q} P≤Q c Xc → P≤Q c (nGF .N-ob c Xc) }
        𝓟 .F-id = eqMon _ _ (funExt λ x → Psh .⋆IdL x)
        𝓟 .F-seq f g = eqMon _ _ (funExt λ h → Psh .⋆Assoc g f h )

        PshFO : FirstOrderHyperDoc Psh bpPsh
        PshFO = record{ 
                    𝓟 = 𝓟; 
                    isHA = PshHomsHA; 
                    isHomo = {!   !}; 
                    eq = record { f = {!   !} ; isMon = {!   !} } , {!   !}; 
                    quant = {!   !}; 
                    beck₁ = {!   !}; 
                    beck₂ = {!   !}}


{-
        poset : Set 
        poset = Σ[ P ∈  Preorder _ _ ] isUnivalent P
        -- cannonical hyperdoc with internal HA for presheaves
        𝓟 : Functor (Psh ^op) (POSET _ _) 
        𝓟 .F-ob F = {!   !} , {!   !} where 

            prestr : PreorderStr ℓ-zero (Psh [ F , Prop𝓒 ]) 
            prestr = preorderstr {!   !} {!   !}
            
            pre : Preorder _ _ 
            pre = (Psh [ F , Prop𝓒  ]) , prestr 

        𝓟 .F-hom = {!   !}
        𝓟 .F-id = {!   !}
        𝓟 .F-seq = {!   !}
   
        -- B to be the internal poset of PropW-valued co-presheaves 
        -- on the partial commutative monoid pH under extension ordering

        -- break up definition

        -- internal poset
            -- def on page 199 of Sheaves in Geo & Logic
        -- need equalizers
        -- construct equalizers from pullback and products
        -- https://math.stackexchange.com/questions/1184111/equalizers-by-pullbacks-and-products
        
        open import Cubical.Categories.Limits.Pullback
        open Pullback
        module _ (pull : Pullbacks Psh) where 
            Equalizer : {A B : ob Psh} → (f g : Psh [ A , B ]) → Σ[ E ∈ ob Psh ] (Psh [ E , A ])
            Equalizer {A} {B} f g = (pb .pbOb) , pb .pbPr₁ where 

                co : Cospan Psh 
                co = cospan A (B ×Psh B) B {!   !} (dup B)

                pb : Pullback Psh co
                pb = pull co


         Max :
            Sℓ​ is the category of functors from worlds to types.
            PropW​ is a poset internal to Sℓ
            pH is a pcm internal to Sℓ, which can be viewed as a poset internal to Sℓ​ usings its extension ordering
            B is defined to be the (Sℓ​-internal) poset of monotone functions from pH to PropW​
        
        ℬ : ob Psh 
        ℬ .F-ob X = (ob (FUNCTOR {!   !} {! Prop𝓒 .F-ob X  !})) , (isSetFunctor {!   !})
        ℬ .F-hom = {!   !}
        ℬ .F-id = {!   !}   
        ℬ .F-seq = {!   !}    
        -}


{-

        module GenOp 
            (op : hProp _ → hProp _ → hProp _) 
            (opmap : 
                    {a b c d : ob PropCat} → 
                    (f : PropCat [ a , c ]) → 
                    (g : PropCat [ b , d ]) → 
                    PropCat [ op a b , op c d ]
                 )
            (opmapid : (x y : ob PropCat) → opmap {x}{y}{x}{y} (PropCat .id {x}) (PropCat .id {y}) ≡ (PropCat .id {op x y}) )
            (opmapseq : 
                {a1 a2 b1 b2 c1 c2 d1 d2 : ob PropCat}→ 
                {!   !} ≡ opmap {!   !} {!   !} ⋆⟨ PropCat ⟩ opmap {!   !} {!   !} )where
        
            genProp𝓒 : Psh [ Prop𝓒 ×Psh Prop𝓒 , Prop𝓒 ]
            genProp𝓒  .N-ob = λ{ x (F , G) → 
                record { 
                    -- The important part is here, the pointwise AND of propositions
                    F-ob = λ x→_ → op (F .F-ob x→_) (G .F-ob x→_) ; 
                    F-hom = λ {x}{y} f → opmap (F .F-hom f) (G .F-hom f) ;
                    F-id = cong₂ opmap (F .F-id) (G .F-id) ∙ opmapid _ _ ; 
                    F-seq = λ f g → cong₂ opmap (F .F-seq _ _) (G .F-seq _ _) ∙ {!   !} }}
            genProp𝓒  .N-hom f = funExt λ _ → cosliceFunEq λ _ → refl 

-}