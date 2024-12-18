{-# OPTIONS --allow-unsolved-metas #-}

module src.Data.PlotkinPower where
    open import Cubical.Foundations.HLevels hiding (extend)
    open import Cubical.Foundations.Prelude  
    open import Cubical.Categories.Category
    open import Cubical.Categories.Functor
    open import Cubical.Categories.Instances.Functors
    open import Cubical.Categories.Instances.Sets
    open import Cubical.Categories.NaturalTransformation
    open import Cubical.Categories.Functors.Constant
    open import Cubical.Categories.Presheaf.Base
    open import Cubical.Categories.Presheaf.Constructions
    open import Cubical.Categories.Bifunctor.Redundant hiding (Fst)
    open import Cubical.Categories.Monoidal.Base
    open import src.Data.DayConv
    open import Cubical.Foundations.Isomorphism
    open import Cubical.Data.Sigma 
    open import Cubical.HITs.SetCoequalizer
    open import src.Data.Coend
    open import Cubical.Categories.Constructions.BinProduct renaming (_×C_ to _B×C_)
    open import src.Data.PresheafCCC
    open import Cubical.Categories.Yoneda.More
    open import Cubical.Foundations.Function
    open import Cubical.Data.Sigma 
    open import Cubical.Categories.Instances.Discrete
    
    open Category

    module PP {ℓ ℓ' : Level}(SMC : StrictMonCategory ℓ ℓ') where 
        --open import src.Data.FinSet
        --open Monoidal
        open import src.Data.Semicartesian
        opmon : StrictMonCategory ℓ ℓ'
        opmon = SMC ^opMon

        C = StrictMonCategory.C  opmon
        ⊗C = StrictMonCategory.sms opmon .StrictMonStr.tenstr .TensorStr.─⊗─ 
        Cunit = StrictMonCategory.sms opmon .StrictMonStr.tenstr .TensorStr.unit
        Cidr = StrictMonCategory.sms opmon .StrictMonStr.idr
        Cidl = StrictMonCategory.sms opmon .StrictMonStr.idl
        Cassoc = StrictMonCategory.sms opmon .StrictMonStr.assoc
        𝓥unit = I⨂ opmon

        _ : 𝓥unit ≡ LiftF ∘F (C [-, Cunit ])
        _ = refl



        open import src.Data.BiDCC
        open Mod opmon
        open import Cubical.Categories.Monad.ExtensionSystem hiding (F)
        open Functor
        open NatTrans
        
        --Cidr' : {x : ob C} → C [ ⊗C .F-ob (x , Cunit), x ]
        --Cidr' {x} = transport (cong (λ h → C [ h , x ]) (sym (Cidr _))) (C .id)

        module NotStrict 
            (Cidr' : {x : ob C} → C [ ⊗C .F-ob (x , Cunit), x ])
            (Cidr'inv : {x : ob C} → C [ x , ⊗C .F-ob (x , Cunit) ])
            (Cidl' : {x : ob C} → C [ ⊗C .F-ob (Cunit , x), x ])
            (Cidl'inv : {x : ob C} → C [ x , ⊗C .F-ob (Cunit , x) ])
            (assocl : {x y z : ob C} → C [ ⊗C .F-ob ((⊗C .F-ob ( x , y )) , z) , (⊗C .F-ob (x , (⊗C .F-ob (y , z)))) ] )
            (assocr : {x y z : ob C} → C [ (⊗C .F-ob (x , (⊗C .F-ob (y , z)))) , ⊗C .F-ob ((⊗C .F-ob ( x , y )) , z) ] )
            (⊗sym : {x y : ob C} → C [ ⊗C .F-ob (x , y) , ⊗C .F-ob (y , x) ])
            where
            
            -- see Ian Stark Categorical Models for Local Names page 22
            -- a quotient is added to get the DROP and SWAP laws

            T : ob 𝓥 → ob 𝓥 
            T A .F-ob x = (Σ (ob C) λ y → A .F-ob (⊗C .F-ob (x , y)) .fst) , isSetΣ {!   !} λ y → A .F-ob (⊗C .F-ob (x , y)) .snd
            T A .F-hom {x}{y} f (z , a) = z , A .F-hom (⊗C .F-hom (f , C .id)) a
            T A .F-id = funExt λ x → ΣPathP (refl , cong (λ h → A .F-hom h (snd x)) (⊗C .F-id) ∙ funExt⁻ (A .F-id) _ )
            T A .F-seq f g = 
                funExt λ _ → 
                    ΣPathP (
                        refl , 
                        cong (λ h → A .F-hom h _) (cong (λ h → ⊗C .F-hom ( g ⋆⟨ C ⟩ f , h))  (sym (C .⋆IdR  _))  ∙ ⊗C .F-seq _ _) 
                        ∙ funExt⁻ (A .F-seq _ _ ) _)

            ret : {A : 𝓥 .ob} → 𝓥 [ A , T A ] 
            ret {A} = natTrans 
                        (λ x Ax → Cunit , A .F-hom Cidr' Ax) 
                        λ f → funExt λ x → 
                            ΣPathP (refl , 
                                (funExt⁻ (sym (A .F-seq _ _)) x 
                                -- this holds in our model
                                -- f ⋆⟨ C ^op ⟩ Cidr' : x→y→y⊗Unit
                                -- Cidr' ⋆⟨ C ^op ⟩ (⊗C .F-hom (f , C .id))
                                ∙ cong (λ h → A .F-hom h x) {! Cidr' ⋆⟨ C ^op ⟩ (⊗C .F-hom (f , C .id))  !}) 
                                ∙ funExt⁻ (A .F-seq _ _) _)

            M : ExtensionSystem 𝓥 
            M = T , record{ 
                        η = ret ; 
                        bind = >>= ; 
                        bind-r = makeNatTransPath (funExt λ x → funExt λ Ax → ΣPathP ((Cidr (Ax .fst)) , {!   !})) ; 
                        bind-l = makeNatTransPath ((funExt λ x → funExt λ Ax → ΣPathP ({! Cidl _ !} , {!   !}))) ; 
                        bind-comp = makeNatTransPath (funExt λ x → funExt λ Ax → ΣPathP ({! refl  !} , {!   !})) } where 

                                        
                    >>= : {a b : 𝓥 .ob} → 𝓥 [ a , T b ] → 𝓥 [ T a , T b ]
                    >>= {A}{B} f .N-ob x (y , Axy) = (⊗C .F-ob (y , z)) , B .F-hom assocr b where 
                        e : T B .F-ob (⊗C .F-ob (x , y)) .fst
                        e = f .N-ob (⊗C .F-ob (x , y)) Axy

                        z : ob C
                        z = e .fst 

                        b : B .F-ob (⊗C .F-ob (⊗C .F-ob (x , y) , z)) .fst
                        b = e .snd

                    >>= {A}{B} f .N-hom {x}{y} g =  funExt λ p → ΣPathP ({! refl  !} , {!   !})

            open import Cubical.Categories.Monad.Base

            T' : Functor 𝓥 𝓥 
            T' .F-ob = T 
            T' .F-hom {A}{B} f .N-ob x (y , Axy) = y , f .N-ob (⊗C .F-ob (x , y)) Axy
            T' .F-hom {A}{B} f .N-hom g = funExt λ{(z , Axz) → ΣPathP (refl , funExt⁻ (f .N-hom (⊗C .F-hom (g , C .id))) Axz)}
            T' .F-id = makeNatTransPath (funExt λ x → funExt λ p → refl)
            T' .F-seq f g = makeNatTransPath (funExt λ x → funExt λ p → refl)
            
            M' :  Monad 𝓥
            M' = T' , {! day-fact {MC = opmon}  !}


            open DayUP
            open Iso



            ⊗str' : {P Q : ob 𝓥} → 𝓥× [ P ⨂Ext T Q , T (P ⨂ᴰ Q) ∘F ((⊗C) ^opF)]
            ⊗str' {P}{Q} .N-ob (x , y)(Px , (z , Qyz)) = z , goal where 

                goal : (P ⨂ᴰ Q) .F-ob (⊗C .F-ob ((⊗C ^opF) ⟅ x , y ⟆ , z)) .fst
                goal = inc ((x , ⊗C .F-ob (y , z)) , ((assocl , Px) , Qyz))

            ⊗str' {P}{Q} .N-hom {(x , y)}{(x' , y')} (f , g) = 
                funExt λ {(Px , (z , Qyz)) → 
                    ΣPathP (
                        refl , 
                        sym (day-fact {MC = opmon} P Q {f = f}{g = (⊗C ^opF) .F-hom (g , C .id)}{h = assocl} {Px}{Qyz} {!   !}))} --yes
                
                {-funExt goal where 
                goal : (pq : fst (F-ob (P ⨂Ext T Q) (x , y))) → {!   !} 
                goal (Px , (z , Qyz)) = ΣPathP (refl , goal') where 

                    goal' : inc ((x' , (⊗C .F-ob ( y' , z ))) , (assocl , P .F-hom f Px) , Q .F-hom (⊗C .F-hom (g , C .id)) Qyz) 
                        ≡ inc ((x , (⊗C .F-ob ( y , z ))) , (assocl ⋆⟨ C ^op ⟩ (⊗C ^opF) .F-hom ((⊗C ^opF) .F-hom (f , g) , (C .id)) , Px) , Qyz)
                        -- left ≡ right 
                    goal' = sym (day-fact {MC = opmon} P Q {f = f}{g = ⊗C .F-hom (g , C .id)}{h = assocl} {Px}{Qyz} {!   !})
                -}
            
            ⊗str : {P Q : ob 𝓥} → 𝓥 [ P ⨂ᴰ T Q , T (P ⨂ᴰ Q) ] 
            ⊗str {P} {Q} = ⨂UP .inv ⊗str'


            ⨂map' : {X Y W Z : ob 𝓥} → 𝓥 [ X , W ] → 𝓥 [ Y , Z ] → 𝓥× [ X ⨂Ext Y , (W  ⨂ᴰ Z) ∘F (⊗C ^opF) ]
            ⨂map' {X}{Y}{W}{Z} n m .N-ob (x , y) (Xx , Yy) = inc (((x , y)) , (C .id , n .N-ob x Xx) , m .N-ob y Yy)
            ⨂map' {X}{Y}{W}{Z} n m .N-hom (f , g) = funExt λ x → {!  !}

            ⨂map : {A B C D : ob 𝓥} → 𝓥 [ A , C ] → 𝓥 [ B , D ] → 𝓥 [ A ⨂ᴰ B , C  ⨂ᴰ D ]
            ⨂map {A}{B}{C}{D} n m = ⨂UP .inv (⨂map' n m) 
            -- Day-Functor opmon .F-hom ((𝓥 .id) , (ret {B})) 

            open UniversalProperty

            -- laws

            module _ where 
                fwrd : {A : ob 𝓥} → 𝓥 [ T A , 𝓥unit ⨂ᴰ T A ] 
                fwrd {A} .N-ob x (y , Axy) = inc ((Cunit , x) , ((Cidl'inv , lift (C .id)) , (y , Axy)))
                fwrd .N-hom = {!   !}
                
                strIrel1 : {A : ob 𝓥} → CatIso 𝓥 (T A) (𝓥unit ⨂ᴰ T A)
                strIrel1 {A} = fwrd , isiso bkwrd prf1 prf2 where 


                    bkwrd : 𝓥 [ 𝓥unit ⨂ᴰ T A , T A ]
                    bkwrd = ⨂UP .inv goal where
                        goal : 𝓥× [ 𝓥unit ⨂Ext T A , T A ∘F (⊗C ^opF) ]
                        goal .N-ob (x , y) (m , (z , Ayz)) = z , A .F-hom f Ayz where 
                            _ : C [ x , Cunit ]
                            _ = m .lower

                            f : C [ ⊗C .F-ob (⊗C .F-ob (x , y) , z) , ⊗C .F-ob (y , z) ]
                            f = ⊗C .F-hom ((⊗C .F-hom ((m .lower) , (C .id))) ⋆⟨ C ⟩ Cidl' , (C .id)) 
                            
                        goal .N-hom = {!   !}

                    prf1 : seq' 𝓥 bkwrd fwrd ≡ 𝓥 .id 
                    prf1 = makeNatTransPath (funExt λ x → funExt λ k → {!  !})

                    prf2 : seq' 𝓥 fwrd bkwrd ≡ 𝓥 .id 
                    prf2 = makeNatTransPath (funExt λ x → funExt λ{(y , Axy) → 
                        ΣPathP (refl , (
                                funExt⁻ (sym (A .F-seq _ _)) _ 
                                ∙ cong (λ h → A .F-hom h _) {!   !}) 
                                ∙ funExt⁻ (A .F-id ) _) })


                d : {A : ob 𝓥} → 𝓥 [ A , 𝓥unit ⨂ᴰ A ]
                d {A} .N-ob x Ax = inc ((Cunit , x) , ((Cidl'inv , lift (C .id)) , Ax))
                d {A} .N-hom f = funExt λ Ax → {!   !} ∙ {! sym (day-fact {MC = opmon} A 𝓥unit ?)  !}
                
                triangle : {A : ob 𝓥} → fwrd {A} ⋆⟨ 𝓥 ⟩ ⊗str {𝓥unit}{A} ≡ T' .F-hom d
                triangle {A} = makeNatTransPath (funExt λ x → funExt λ{(y , Axy) → ΣPathP (refl , day-apₘ {MC = opmon} 𝓥unit A {!   !})})

            strUnit : {A B : ob 𝓥} → (⨂map (𝓥 .id) (ret {B})) ⋆⟨ 𝓥 ⟩ ⊗str {A} {B} ≡ ret {(A ⨂ᴰ B)}
            strUnit {A} {B} = 
                ⨂≡map (makeNatTransPath 
                    (funExt λ{(x , y) → funExt λ{(Ax , By)→ 
                        ΣPathP (
                            refl , 
                            day-apₘ {MC = opmon} A B (cong (λ h → h ⋆⟨ C ⟩ assocl) ((cong (λ h → ⊗C .F-hom (h , C .id)) (C .⋆IdR _)) ∙ ⊗C .F-id) ∙ C .⋆IdL _) 
                            ∙ (day-ap {MC = opmon} A B refl (funExt⁻ (sym (A .F-id)) _) refl 
                            ∙ sym (day-fact {MC = opmon} A B {f = C .id}{Cidr'}{fgh = Cidr'} {!   !} )) --yes
                            ∙ day-apₘ {MC = opmon} A B (sym (C .⋆IdR _)) )}}))

            -- strength plays well with associators

            -- strenth commutes with join
            strJoin : {A B : ob 𝓥} → Day-Functor opmon .F-hom ((𝓥 .id) , {!   !}) ⋆⟨ 𝓥 ⟩ {!   !} ≡ {!   !}
            strJoin = {!   !}

            --𝓒 : Category _ _ 
            --𝓒 = Kleisli 𝓥 M

            open import Cubical.Categories.Instances.EilenbergMoore
            𝓒 : Category _ _ 
            𝓒 = EMCategory M'


            open BifunctorPar
            open import Cubical.Categories.Instances.FunctorAlgebras
            open Algebra
            open import Cubical.Foundations.Function

            -- olique morphisms
            𝓞' : BifunctorPar (𝓥 ^op) 𝓒 (SET _)
            𝓞' .Bif-ob v (algebra c str , _) = 𝓥 [ v , c ] , 𝓥 .isSetHom
            𝓞' .Bif-hom× f (algebraHom h strHom) g = f ⋆⟨ 𝓥 ⟩ g ⋆⟨ 𝓥 ⟩ h
            𝓞' .Bif-×-id = funExt λ x → 𝓥 .⋆IdR _ ∙ makeNatTransPath (funExt λ y → funExt λ z → refl)
            𝓞' .Bif-×-seq e f g h = funExt λ x → 
                𝓥 .⋆Assoc (seqTrans f e) x (seqTrans (AlgebraHom.carrierHom g) (AlgebraHom.carrierHom h)) 
                ∙ 𝓥 .⋆Assoc f e (seqTrans x (seqTrans (AlgebraHom.carrierHom g) (AlgebraHom.carrierHom h))) 
                ∙ cong (λ h → seqTrans f h) (sym (𝓥 .⋆Assoc e x (seqTrans (AlgebraHom.carrierHom g) (AlgebraHom.carrierHom h))))
                ∙ cong (λ h → seqTrans f h) (sym (𝓥 .⋆Assoc (seqTrans e x) (AlgebraHom.carrierHom g) (AlgebraHom.carrierHom h)))
                ∙ sym (𝓥 .⋆Assoc f (seqTrans (seqTrans e x) (AlgebraHom.carrierHom g)) (AlgebraHom.carrierHom h) )
                
        
            𝓞 : Bifunctor (𝓥 ^op) 𝓒 (SET _) 
            𝓞 = mkBifunctorPar 𝓞'

            -- oblique morphisms
            𝓞[_,_] : ob 𝓥 → ob 𝓒 → Set ℓm
            𝓞[ v , c ] = 𝓞 .Bif-ob' v c .fst where 
                open Bifunctor renaming (Bif-ob to Bif-ob')

            
            F = FreeEMAlgebra M'
            U = ForgetEMAlgebra M'
            
            -- This is by definition
            adj1 : {A : ob 𝓥} {B : ob 𝓒} → Iso (𝓥 [ A , U .F-ob B ]) 𝓞[ A , B ] 
            adj1 = idIso
            
            -- Have this by abstract nonsense
            adj2 : {A : ob 𝓥} {B : ob 𝓒} → Iso (𝓞[ A , B ]) (𝓒 [ F .F-ob A , B ])
            adj2 {A} {B} = invIso (emBijection M' A B )



            ⨂sym : {A B : ob 𝓥 } → 𝓥 [ A ⨂ᴰ B , B ⨂ᴰ A ]
            ⨂sym {A} {B} = ⨂UP .inv {!   !} where 
                goal : 𝓥× [ A ⨂Ext B , (B ⨂ᴰ A) ∘F (⊗C ^opF) ]
                goal .N-ob (x , y) (Ax , By) = inc ((y , x) , ((⊗sym , By) , Ax))
                goal .N-hom = {!   !}
            
            open SepUP
            
            -- computation separating type now exists via abstract nonsense
            _-*_ : ob 𝓥 → ob 𝓒 → ob 𝓒 
            _-*_ A B = 
                algebra 
                    (A ⊸ (B .fst .carrier)) 
                    (⊸UP .fun (⨂sym ⋆⟨ 𝓥 ⟩ ⊗str ⋆⟨ 𝓥 ⟩ T' .F-hom (⨂sym ⋆⟨ 𝓥 ⟩ ⨂UP .inv (eval {A})) ⋆⟨ 𝓥 ⟩ B .fst .str )) 
                    , 
                proveEMAlgebra 
                    (makeNatTransPath (funExt λ x → funExt λ p → makeNatTransPath (funExt λ y → funExt λ Ay → {! refl !}))) 
                    {!   !}

            {- for concrete model }            
            Names : ob 𝓥 
            Names .F-ob x = {!   !} , {!   !}
            Names .F-hom = {!   !}
            Names .F-id = {!   !}
            Names .F-seq = {!   !}
            -}

            

            

               