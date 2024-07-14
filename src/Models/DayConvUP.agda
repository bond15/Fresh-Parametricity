{-# OPTIONS  --type-in-type --lossy-unification #-}
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
    open import Cubical.Categories.Constructions.BinProduct
    open import src.Data.NatFam

    module _ {ℓ ℓ' ℓS : Level}{SMC  : StrictMonCategory ℓ ℓ'} where 
        ℓm = ℓ-max ℓ (ℓ-max ℓ' ℓS)
        
        open StrictMonCategory SMC renaming (C to C) hiding(ob)
        open Category
        open Functor
        open Bifunctor
        open NatTrans
        open StrictMonStr hiding(_⊗_ ; _⊗ₕ_)
        open TensorStr hiding(_⊗_ ; _⊗ₕ_)
        open Iso        
        open SetCoequalizer 
        open UniversalProperty
        open Bifunctor
        open Coend
        open Cowedge
        
        𝓥 : Category _ _ 
        𝓥 = PresheafCategory C ℓm

        _×p_ : ob 𝓥 → ob 𝓥 → ob 𝓥
        A ×p B = PshProd .Bif-ob A B

        _⨂ᴰᵥ_ : ob 𝓥 → ob 𝓥 → ob 𝓥
        A ⨂ᴰᵥ B =  _⊗ᴰ_  {MC = SMC} A B


        module definitions (P Q R : ob 𝓥) where
            open NatFam {SMC = SMC} 

            -- some definitions

            {-
              Dom ==(lmap (diag x))=(rmap (diag x))==> Diag --inc--> Day' x = SetCoequalizer (lmap (diag x)) (rmap (diag x))
                                                            \            .
                                                              \          .
                                                              h   ∃! inducedHom
                                                                  \      .
                                                                    \    .
                                                                        C
            -}

            diag : ob C → Bifunctor ((C ×C C) ^op) (C ×C C) (SET ℓ-zero)
            diag = diagram {MC = SMC} P Q
            
            Dom : (x : ob C) → Set _
            Dom x = Σ[ X ∈ (ob C × ob C) ] 
                     Σ[ Y ∈ (ob C × ob C) ] 
                     Σ[ (f , g) ∈ ((C ×C C) [ Y , X ]) ] 
                     ((diag x ⟅ (X , Y) ⟆b ) .fst)
                     

            Diag : (x : ob C) → Set _
            Diag x = Σ[ (y , z) ∈ (ob C × ob C)] (fst (diag x ⟅ (y , z) , (y , z) ⟆b))

            Day' : (c : ob C) → Coend (diag c)
            Day' = Day  {MC = SMC} P Q
            
            DayCoe : (c : ob C) → hSet ℓS
            DayCoe c = Day' c .cowedge .nadir

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
                        (((cong₂ (λ h1 h2 → F-hom R ((f ⊗ₕ g)) (m _ _ (h1 , h2))) (funExt⁻ (P .F-id) _) ((funExt⁻ (Q .F-id) _)) 
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
     
        module _ (P Q R : ob 𝓥) where
            open NatFam {SMC = SMC} 
            open definitions P Q R

            
            fwd : 𝓥 [ P ⨂ᴰᵥ Q , R ] → NatFam P Q R
            fwd nt .NF-ob x y (Px , Qy) = nt .N-ob (x ⊗ y) (inc ((x , y) , (((C .id) , Px) , Qy)))
            fwd nt .NF-hom {X}{Y}{X'}{Y'}f g = 
                funExt λ{(Px , Qy) → funExt⁻ (sym (nt .N-hom (f ⊗ₕ g))) _ 
                ∙ cong (λ h → nt .N-ob ( X' ⊗ Y') h) (day-fact {MC = SMC} P Q (C .⋆IdR _ ∙ sym(C .⋆IdL _)))}
    
            bkwd : NatFam P Q R → 𝓥 [ P ⨂ᴰᵥ Q , R ] 
            bkwd nf = natTrans η ηnat where 
                η : N-ob-Type (P ⨂ᴰᵥ Q) R 
                η x = inducedHom 
                        (R .F-ob x .snd) 
                        (mapout nf x) 
                        (mapoutcoeq nf x)

                ηnat : N-hom-Type (P ⨂ᴰᵥ Q) R η 
                ηnat {x}{y} f = r∘t≡ind ∙ sym (b∘l≡ind) where 

                    --show that the diagram commutes because both paths are equal to 
                    --an inducedHom
                    r : (SET _)[ (P ⨂ᴰᵥ Q) .F-ob x , R .F-ob y ] 
                    r = seq' (SET _) {(P ⨂ᴰᵥ Q) .F-ob x}{(P ⨂ᴰᵥ Q) .F-ob y}{R .F-ob y}
                        ((P ⨂ᴰᵥ Q) .F-hom f) (η y)

                    l : (SET _)[ (P ⨂ᴰᵥ Q) .F-ob x , R .F-ob y ]
                    l = seq' (SET _){(P ⨂ᴰᵥ Q) .F-ob x}{R .F-ob x}{R .F-ob y}
                        (η x) (R .F-hom f)

                    tm : Diag x → DayCoe y .fst
                    tm = (λ { (x , Fxx) → Day-cowedge P Q f .ψ x Fxx })

                    tcom : (a : Dom x) → tm ((lmap (diag x)) a) ≡ tm ((rmap (diag x)) a)
                    tcom = (λ { (X , Y , g , Fxy) → funExt⁻ (Day-cowedge P Q f .extranatural g) Fxy })

                    _∘s_ : {A B C : Set _}(g : B → C) → (f : A → B ) → A → C 
                    g ∘s f = λ x → g (f x)
                    
                    trdiag : (d : Diag x) → R .F-ob y .fst
                    trdiag = (η y ∘s tm) 
                    
                    -- could this be composed by tcom and rcom?      
                    trcom : (a : Dom x) → trdiag (lmap (diag x) a) ≡ trdiag (rmap (diag x) a)
                    trcom ((w , v) , (w' , v') , (w'→w , v'→v) , (x→w'⊗v' , Pw) , Qv) = 
                        funExt⁻ (R .F-seq (x→w'⊗v' ⋆⟨ C ⟩ (w'→w ⊗ₕ v'→v)) f)  _
                        ∙ cong (λ h → R .F-hom f h) 
                            (funExt⁻ (R .F-seq _ x→w'⊗v' ) _ 
                            ∙ cong (λ h → R .F-hom x→w'⊗v' h) 
                                (cong₂ (λ h1 h2 → F-hom R ((w'→w ⊗ₕ v'→v)) (nf .NF-ob w v (h1 , h2))) (funExt⁻ (P .F-id) _) ((funExt⁻ (Q .F-id) _)) 
                                ∙ (funExt⁻ (nf .NF-hom w'→w v'→v) _  -- using naturality of the family
                                ∙ funExt⁻ (sym (R .F-id )) _) 
                                ∙ cong (λ h → R .F-hom h _)  (sym (sms .tenstr .─⊗─ .F-id))) 
                            ∙ funExt⁻ (sym (R .F-seq _ x→w'⊗v')) _) 
                        ∙ funExt⁻ (sym (R .F-seq (x→w'⊗v' ⋆⟨ C ⟩ (C .id ⊗ₕ C .id)) f )) _

                    ind : DayCoe x .fst → R .F-ob y .fst 
                    ind = (inducedHom (R .F-ob y .snd) trdiag trcom)

                    r∘t≡ind : (η y) ∘s ((P ⨂ᴰᵥ Q) .F-hom f) ≡ ind
                    r∘t≡ind = 
                        uniqueness 
                            ((lmap (diag x))) 
                            ((rmap (diag x))) 
                            (R .F-ob y .snd) 
                            (η y ∘s tm)
                            trcom 
                            r 
                            λ _ → refl

                    b∘l≡ind : ((R .F-hom f) ∘s (η x)) ≡ ind
                    b∘l≡ind = 
                        uniqueness
                            ((lmap (diag x))) 
                            ((rmap (diag x))) 
                            (R .F-ob y .snd) 
                            ((η y ∘s tm)) 
                            trcom 
                            l 
                            λ _ → funExt⁻ (R .F-seq _ _) _

                    
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

  