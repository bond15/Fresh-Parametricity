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
            makeNatFamPath p i .NF-hom {X}{Y}{X'}{Y'}f g = prf i where
                l =  seq' (SET ℓS) {P .F-ob X ×h Q .F-ob Y}{R .F-ob (X ⨂ Y)}{R .F-ob (X' ⨂ Y')} (p i X Y) (R .F-hom (f ⨂₁ g)) 
                prf : PathP 
                        (λ i → seq' (SET ℓS) {P .F-ob X ×h Q .F-ob Y}{R .F-ob (X ⨂ Y)}{R .F-ob (X' ⨂ Y')} (p i X Y) (R .F-hom (f ⨂₁ g)) 
                             ≡ seq' (SET ℓS) {P .F-ob X ×h Q .F-ob Y}{P .F-ob X' ×h Q .F-ob Y'}{R .F-ob (X' ⨂ Y')} (×Fhom P Q f g) (p i X' Y') )  
                        (n .NF-hom f g) 
                        (m .NF-hom f g)
                prf = toPathP ((SET ℓS) .isSetHom {P .F-ob X ×h Q .F-ob Y} {R .F-ob (X' ⨂ Y')}  _ _ _ _)
        
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
            
            Dom : (x : ob C) → Set _
            Dom x = Σ[ X ∈ (ob C × ob C) ] 
                     Σ[ Y ∈ (ob C × ob C) ] 
                     Σ[ (f , g) ∈ ((C ×C C) [ Y , X ]) ] 
                     ((diag x ⟅ (X , Y) ⟆b ) .fst)
                     

            Diag : (x : ob C) → Set _
            Diag x = Σ[ (y , z) ∈ (ob C × ob C)] (fst (diag x ⟅ (y , z) , (y , z) ⟆b))
            {-
              Dom ==(lmap (diag x))=(rmap (diag x))==> Diag --inc--> Day' x = SetCoequalizer (lmap (diag x)) (rmap (diag x))
                                                            \            .
                                                              \          .
                                                              h   ∃! inducedHom
                                                                  \      .
                                                                    \    .
                                                                        C
            commuting diagram
            
            -}

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
                (a : Dom x ) → 
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

            η≡ : {x : ob C }
                {nf : NatFam P Q R}
                {other : SET ℓ' [ (P ⨂ᴰᵥ Q) .F-ob x , R .F-ob x ] }
                (prf : ((d : Diag x ) → mapout nf x d ≡ other (inc d)) ) → 
                other ≡ inducedHom 
                        (R .F-ob x .snd) 
                        (mapout nf x) 
                        (mapoutcoeq nf x)
            η≡ {x}{nf} {other} prf =  
                uniqueness  
                    ((lmap (diag x))) 
                    ((rmap (diag x))) 
                    ((R .F-ob x .snd)) 
                    ((mapout nf x))  
                    ((mapoutcoeq nf x)) 
                    other 
                    prf
                
            bkwd : NatFam P Q R → 𝓥 [ P ⨂ᴰᵥ Q , R ] 
            bkwd nf = natTrans η ηnat where 
                η : N-ob-Type (P ⨂ᴰᵥ Q) R 
                η x = inducedHom 
                        (R .F-ob x .snd) 
                        (mapout nf x) 
                        (mapoutcoeq nf x)

                ηnat : N-hom-Type (P ⨂ᴰᵥ Q) R η 
                ηnat {x}{y} f = goal where 
                    l : (SET _)[ (P ⨂ᴰᵥ Q) .F-ob x , R .F-ob y ] 
                    l = seq' (SET _) {(P ⨂ᴰᵥ Q) .F-ob x}{(P ⨂ᴰᵥ Q) .F-ob y}{R .F-ob y}
                        ((P ⨂ᴰᵥ Q) .F-hom f) (η y)

                    r : (SET _)[ (P ⨂ᴰᵥ Q) .F-ob x , R .F-ob y ]
                    r = seq' (SET _){(P ⨂ᴰᵥ Q) .F-ob x}{R .F-ob x}{R .F-ob y}
                        (η x) (R .F-hom f)

                                      -- show a map is equal to a component 
                    -- if they are equal maps on Diag
                    fact : {x : ob C }
                         {other : SET ℓ' [ (P ⨂ᴰᵥ Q) .F-ob x , R .F-ob x ] }
                         (prf : ((d : Diag x ) → mapout nf x d ≡ other (inc d)) ) → 
                         other ≡ η x 
                    fact {x} {other} prf = η≡ prf
                        
                    -- to get rid the dumb isSet obligations, explicity use seq'
                    goal : l ≡ r
                    goal = funExt λ coex → {!   !}
                    --funExt⁻ (sym (η≡ {y}{{!   !}} {!   !})) (((P ⨂ᴰᵥ Q) .F-hom f) coex) ∙ {! nf .NF-hom _ _  !}

                    top : SET ℓ' [ F-ob (P ⨂ᴰᵥ Q) x , F-ob (P ⨂ᴰᵥ Q) y ]
                    top = ((P ⨂ᴰᵥ Q) .F-hom f)

                    right' : SET ℓ' [ (P ⨂ᴰᵥ Q) .F-ob y , R .F-ob y ]
                    right' = inducedHom (R .F-ob y .snd) (mapout nf y) (mapoutcoeq nf y)

                    rightcom : (d : Diag y) → mapout nf y d ≡ (η y) (inc d)
                    rightcom = commutativity (R .F-ob y .snd) (mapout nf y) (mapoutcoeq nf y)


                    _ : SetCoequalizer (lmap (diag y)) (rmap (diag y)) ≡ (P ⨂ᴰᵥ Q) .F-ob y  .fst
                    _ = refl


      
                            --{! commutativity (R .F-ob x .snd) (mapout nf x) (mapoutcoeq nf x)  !}
                            --prf

                    cross : 
                         {other : SET ℓ' [ (P ⨂ᴰᵥ Q) .F-ob x , R .F-ob y ] }→ 
                        -- (prf : ((d : Diag x ) → mapout nf x d ≡ other (inc d)) ) → 
                         other ≡ l
                    cross {other} = {! uniqueness ? ? ? ? ? ? ?  !}
                    
                            
                    {-

                      uniqueness : {C : Type ℓ''}
             → (f g : A → B)
             → (Cset : (x y : C) → (p q : x ≡ y) → p ≡ q)
             → (h : B → C)
             → (hcoeq : (a : A) → h (f a) ≡ h (g a))
             → (i : SetCoequalizer f g → C)
             → (icommutativity : (b : B) → h b ≡ i (inc b))
             → (i ≡ inducedHom Cset h hcoeq)

 commutativity : {C : Type ℓ''} {f g : A → B}
                → (Cset : (x y : C) → (p q : x ≡ y) → p ≡ q)
                → (h : B → C)
                → (hcoeq : (a : A) → h (f a) ≡ h (g a))
                → ((b : B) → h b ≡ inducedHom Cset h hcoeq (inc b))
  commutativity Cset h hcoeq = λ b → refl

        record Coend : Set ((ℓ-max ℓC (ℓ-max ℓC' (ℓ-max ℓD ℓD'))))  where
            open Cowedge
            field
                cowedge : Cowedge
                factor : (W : Cowedge ) → D [ cowedge .nadir , W .nadir ]
                commutes : (W : Cowedge )
                           (c : C.ob) →
                           (cowedge .ψ c D.⋆ factor W) ≡ W .ψ c
                unique : (W : Cowedge )
                         (factor' : D [ cowedge .nadir , W .nadir ]) →
                         (∀(c : C.ob) → (cowedge .ψ c D.⋆ factor') ≡ W .ψ c) →
                         factor' ≡ factor W
                    -}
                    topUnique : (other : SET ℓ' [ F-ob (P ⨂ᴰᵥ Q) x , F-ob (P ⨂ᴰᵥ Q) y ]) → other ≡ top
                    topUnique  other = Day' x .unique {! tr  !} {!   !} {!   !} where 

                        tr : Cowedge (diag y) 
                        tr = {! Day' y .cowedge   !}
                           -- Day' x .unique 
                           --     (Day-cowedge {MC = SMC} P Q f) 
                           --     {! Day' x .factor (Day-cowedge {MC = SMC} P Q f)   !} 
                           --     {!   !} 

                    right : SET ℓ' [ (P ⨂ᴰᵥ Q) .F-ob y , R .F-ob y ]
                    right = (η y)

                    tr : F-ob (P ⨂ᴰᵥ Q) x ≡ Day' x .cowedge .nadir
                    tr = refl
 
                    -- l is a composition of two induced homs.. 
                    observation : l ≡ λ x → (inducedHom (R .F-ob y .snd) (mapout nf y) (mapoutcoeq nf y)) {!   !}
                    observation = {!((lmap (diagram P Q y)))    !}

 

                         

            UP : Iso (𝓥 [ P ⨂ᴰᵥ Q , R ]) (NatFam P Q R)
            UP = iso 
                    fwd 
                    bkwd 
                    (λ b → makeNatFamPath (funExt λ x → funExt λ y → funExt λ{(Px , Qy) → funExt⁻ (R .F-id) _ }) )
                    (λ b → makeNatTransPath (funExt λ x → 
                                -- show the components are equal by showing they are equal maps on diagrams
                                sym (η≡  λ {((y , z) , (x→y⊗z , Py) , Qz) → 
                                    funExt⁻ (sym (b .N-hom _)) _ 
                                        ∙ cong (λ h → b .N-ob x h) (day-apₘ {MC = SMC} P Q (C .⋆IdR _))} )))  

