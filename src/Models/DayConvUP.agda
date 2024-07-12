{-# OPTIONS --type-in-type --lossy-unification #-}
module src.Models.DayConvUP where 
    
    open import Cubical.Foundations.HLevels hiding (extend)
    open import Cubical.Foundations.Prelude  
    open import Cubical.Categories.Category
    open import Cubical.Categories.Functor
    open import Cubical.Categories.Instances.Functors
    open import Cubical.Categories.Instances.Sets
    open import Cubical.Data.FinSet.Base
    open import Cubical.Categories.NaturalTransformation
    open import Cubical.Categories.Functors.Constant
    open import Cubical.Categories.Presheaf.Base
    open import Cubical.Categories.Presheaf.Constructions
    open import Cubical.Categories.Bifunctor.Redundant
    open import Cubical.Categories.Monoidal.Base
    open import src.Data.DayConv
    open import src.Data.Semicartesian
    open import Cubical.Foundations.Isomorphism
    open import Cubical.Data.Sigma 
    open import Cubical.HITs.SetCoequalizer
    open import src.Data.Coend
    open import  Cubical.Categories.Constructions.BinProduct

    -- global parameters
    -- day instead of inc
    -- use ⊗.F-hom then use fact
    -- diag 
    module _ {ℓ ℓ' ℓS : Level}{SMC  : StrictMonCategory ℓ ℓ'} where 
        ℓm = ℓ-max ℓ (ℓ-max ℓ' ℓS)
        
        open StrictMonCategory SMC renaming (C to C) hiding(ob)
        
        𝓥 : Category _ _ 
        𝓥 = PresheafCategory C ℓ'

        open Category
        open Functor
        open Bifunctor
        open NatTrans
        open StrictMonStr
        open TensorStr 
        open Iso        
        open SetCoequalizer 
        open UniversalProperty
        open Bifunctor
        open Coend
        open Cowedge

        _×p_ : ob 𝓥 → ob 𝓥 → ob 𝓥
        A ×p B = PshProd .Bif-ob A B

        _⨂_ : ob C → ob C → ob C 
        x ⨂ y = sms .tenstr .─⊗─ .F-ob (x , y)

        _⨂₁_ : {q r s t : ob C}(f : C [ q , s ])(g : C [ r , t ])→ C [ q ⨂ r , s ⨂ t ]
        f ⨂₁ g = sms .tenstr .─⊗─  .F-hom ( f , g)


        _⨂ᴰᵥ_ : ob 𝓥 → ob 𝓥 → ob 𝓥
        A ⨂ᴰᵥ B =  _⊗ᴰ_  {MC = SMC} A B

        _×h_ : hSet ℓm → hSet ℓm → hSet ℓm 
        x ×h y = (x .fst × y .fst) , isSet× (x .snd) (y .snd)

    
        ×Fhom : {X Y X' Y' : ob C}
                (P Q : ob 𝓥)
                (f : C [ X' , X ])
                (g : C [ Y' , Y ]) →  
                (SET ℓS)[ P .F-ob X ×h Q .F-ob Y , P .F-ob X' ×h Q .F-ob Y' ]
        ×Fhom P Q f g (Px , Qy) = P .F-hom f Px , Q .F-hom g Qy

        NF-ob-Type : (P Q R : ob 𝓥) → Set _
        NF-ob-Type P Q R = (X Y : ob C) → (SET _)[ P .F-ob X ×h Q .F-ob Y , R .F-ob  (X ⨂ Y) ]

        NF-hom-Type : (P Q R : ob 𝓥) → NF-ob-Type P Q R → Set _
        NF-hom-Type P Q R η = 
                        {X Y X' Y' : ob C} →
                        (f : C [ X' , X ]) → 
                        (g : C [ Y' , Y ]) → 
                        seq' (SET _) {P .F-ob X ×h Q .F-ob Y}{R .F-ob (X ⨂ Y)}{R .F-ob (X' ⨂ Y')}
                            (η X Y)(R .F-hom (f ⨂₁ g))  
                            ≡ 
                        seq' (SET _) {P .F-ob X ×h Q .F-ob Y}{P .F-ob X' ×h Q .F-ob Y'}{R .F-ob (X' ⨂ Y')}
                            (×Fhom P Q f g)(η X' Y')

        record NatFam (P Q R : ob 𝓥) : Set (ℓ-suc ℓm) where
            constructor natFam 
            field 
                NF-ob : NF-ob-Type P Q R
                NF-hom : NF-hom-Type P Q R NF-ob

        module _ {P Q R : ob 𝓥}{n m : NatFam P Q R} where 
            open NatFam
            makeNatFamPath : n .NF-ob ≡ m .NF-ob → n ≡ m
            makeNatFamPath p i .NF-ob = p i
            makeNatFamPath p i .NF-hom {X}{Y}{X'}{Y'}f g = {!   !} 
               -- prf : PathP (λ i → {!   !} ≡ {!   !}) (n .NF-hom f g) ((m .NF-hom f g)) 
                --prf = {! (SET _) .isSetHom !}

        
        module fresh (P Q R : ob 𝓥) where
            open NatFam
            day-fact : {x y z y' z' : ob C}{f : C [ y' , y ]}{g : C [ z' , z ]}{h : C [ x , (y' ⨂ z') ]}{py : P .F-ob y .fst}{qz : Q .F-ob z .fst} → 
                {fgh : C [ x , (y ⨂ z) ]}(p : fgh ≡ (h ⋆⟨ C ⟩ (f ⨂₁ g))) → 
                day {MC = SMC} P Q fgh py qz ≡ day {MC = SMC} P Q h (P .F-hom f  py) (Q .F-hom g qz)
            day-fact {x}{y}{z}{y'}{z'}{f}{g}{h}{py}{qz}{fgh} p = 
                inc ((y , z) , (fgh , py) , qz) 
                    ≡⟨ day-ap {MC = SMC} P Q p (sym (funExt⁻ (P .F-id ) py)) ((sym (funExt⁻ (Q .F-id ) qz))) ⟩ 
                inc ((y , z) , ((h ⋆⟨ C ⟩ (f ⨂₁ g)) , P .F-hom (C .id) py) ,  Q .F-hom (C .id ) qz) 
                    ≡⟨ coeq ((y , z) , ((y' , z') , (f , g) , (h , py) , qz)) ⟩ -- This is the tricky step
                inc ((y' , z') , ((h ⋆⟨ C ⟩ ((C .id) ⨂₁ (C .id))) , P .F-hom f py) ,  Q .F-hom g qz) 
                    ≡⟨ day-ap {MC = SMC} P Q  (cong (λ hole → h ⋆⟨ C ⟩ hole) (sms .tenstr .─⊗─ .F-id) 
                    ∙ C .⋆IdR _) refl refl ⟩ 
                inc ((y' , z') , (h , P .F-hom f py) , Q .F-hom g qz) ∎

            fwd : 𝓥 [ P ⨂ᴰᵥ Q , R ] → NatFam P Q R
            fwd nt .NF-ob x y (Px , Qy) = nt .N-ob (x ⨂ y) (inc ((x , y) , (((C .id) , Px) , Qy)))
            fwd nt .NF-hom {X}{Y}{X'}{Y'}f g = 
                funExt λ{(Px , Qy) → funExt⁻ (sym (nt .N-hom (f ⨂₁ g))) _ 
                ∙ cong (λ h → nt .N-ob ( X' ⨂ Y') h) (day-fact (C .⋆IdR _ ∙ sym(C .⋆IdL _)))}

            diag : ob C → Bifunctor ((C ×C C) ^op) (C ×C C) (SET ℓ-zero)
            diag = diagram {MC = SMC} P Q
            
            Diag : (x : ob C) → Set _
            Diag x = Σ[ (y , z) ∈ (ob C × ob C)] (fst (diag x ⟅ (y , z) , (y , z) ⟆b))

            Day' : (c : ob C) → Coend (diag c)
            Day' = Day  {MC = SMC} P Q
            
            DayCoe : (c : ob C) → hSet ℓS
            DayCoe c = Day' c .cowedge .nadir
            
            DayMap : {x y : ob C}(f : C [ x , y ])→ (SET ℓm)[ DayCoe y , DayCoe x ]
            DayMap f = _⊗ᴰ_ {MC = SMC} P Q .F-hom f


            mapout : (nf : NatFam P Q R) → 
                (x : ob C) → Diag x → R .F-ob x .fst  
            mapout nf x ((y , z) , (x→y⊗z , Py) , Qz) = R .F-hom x→y⊗z (nf .NF-ob y z (Py , Qz)) 
            
            mapoutcoeq : (m : NatFam P Q R)
                (x : ob C)
                (a : Σ[ X ∈ (ob C × ob C) ] 
                     Σ[ Y ∈ (ob C × ob C) ] 
                     Σ[ (f , g) ∈ ((C ×C C) [ Y , X ]) ] 
                     ((diag x ⟅ (X , Y) ⟆b ) .fst) ) → 
                mapout m x (lmap (diag x) a) 
                 ≡
                mapout m x (rmap (diag x) a)
            mapoutcoeq 
                record { NF-ob = m ; NF-hom = natfam } 
                x 
                ((y , z) , (y' , z') , (f , g) , (x→y'⊗z' , Py) , Qz) = 
                    funExt⁻ (R .F-seq _ _)  (m y z (F-hom P (C . id) Py , F-hom Q (C . id) Qz)) 
                    ∙ cong (λ h →  F-hom R x→y'⊗z' h) 
                        (((cong₂ (λ h1 h2 → F-hom R ((f ⨂₁ g)) (m _ _ (h1 , h2))) (funExt⁻ (P .F-id) _) ((funExt⁻ (Q .F-id) _)) 
                        ∙ funExt⁻ (natfam f g) _ )  -- using naturality of the family 
                        ∙ funExt⁻ (sym (R .F-id )) (m _ _(F-hom P f Py , F-hom Q g Qz))) 
                        ∙ cong (λ h → R .F-hom h (m _ _(F-hom P f Py , F-hom Q g Qz))) (sym (sms .tenstr .─⊗─ . F-id)))
                    ∙ funExt⁻ (sym (R .F-seq _ _)) (m _ _ (F-hom P f Py , F-hom Q g Qz)) 
                
            bkwd : NatFam P Q R → 𝓥 [ P ⨂ᴰᵥ Q , R ] 
            bkwd nf = natTrans η ηnat where 
                η : N-ob-Type (P ⨂ᴰᵥ Q) R 
                η x = inducedHom 
                        (R .F-ob x .snd) 
                        (mapout nf x) 
                        (mapoutcoeq nf x)

                ηnat : N-hom-Type (P ⨂ᴰᵥ Q) R η 
                ηnat {x}{y} f = goal where 
                    -- to get rid the dumb isSet obligations, explicity use seq'
                    goal :
                            seq' (SET _) {(P ⨂ᴰᵥ Q) .F-ob x}{(P ⨂ᴰᵥ Q) .F-ob y}{R .F-ob y}
                            ((P ⨂ᴰᵥ Q) .F-hom f) (η y) 
                         ≡ seq' (SET _){(P ⨂ᴰᵥ Q) .F-ob x}{R .F-ob x}{R .F-ob y}
                            (η x) (R .F-hom f)
                    goal = funExt pointwise where 

                        observe : η x ≡ inducedHom (R .F-ob x .snd) (mapout nf x) (mapoutcoeq nf x) 
                        observe = refl
                        
                        pointwise : (coe : fst ((P ⨂ᴰᵥ Q) .F-ob x)) →
                             (η y)  (((P ⨂ᴰᵥ Q) .F-hom f) coe ) ≡ (R .F-hom f) ((η x) coe)
                        pointwise coe = {!   !}
                
                    -- {! Day' x .cowedge .nadir  !}

            UP : Iso (𝓥 [ P ⨂ᴰᵥ Q , R ]) (NatFam P Q R)
            UP = iso 
                    fwd 
                    bkwd 
                    (λ b → makeNatFamPath (funExt λ x → funExt λ y → funExt λ{(Px , Qy) → funExt⁻ (R .F-id) _ }) )
                    (λ b → makeNatTransPath (funExt λ x → 
                        sym (uniqueness 
                                (lmap (diagram P Q x)) 
                                (rmap (diagram P Q x)) 
                                (R .F-ob x .snd) 
                                (mapout (fwd b) x) 
                                (mapoutcoeq (fwd b) x) 
                                (b .N-ob x) 
                                λ {((y , z) , (x→y⊗z , Py) , Qz) → 
                                    funExt⁻ (sym (b .N-hom _)) _ 
                                    ∙ cong (λ h → b .N-ob x h) (day-apₘ {MC = SMC} P Q (C .⋆IdR _))} )))
