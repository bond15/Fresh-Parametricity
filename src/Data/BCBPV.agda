{-# OPTIONS --allow-unsolved-metas #-}

module src.Data.BCBPV where 
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

    module Mod {ℓ ℓ' : Level}(SMC : StrictMonCategory ℓ ℓ')(isGrpCob : isGroupoid (ob (StrictMonCategory.C SMC))) where
        open import src.Data.BiDCC 
        open Mod SMC
        open StrictMonCategory SMC renaming(─⊗─ to ⨂c) hiding (ob)
        open Functor
        open Bifunctor
        open NatTrans
        open BifunctorPar

        𝓒 : Category (ℓ-suc ℓm) ℓm 
        𝓒 = PresheafCategory (C ^op) ℓm

        open import src.Data.Direct2

        |C| : Category ℓ ℓ
        |C| = (DiscreteCategory (ob C , isGrpCob))
        
        Inc : Functor |C| C
        Inc = DiscFunc λ x → x
        
        Fam : Category (ℓ-suc ℓm) ℓm
        Fam = FUNCTOR |C| (SET ℓm)

        Inc* : Functor 𝓒 Fam 
        Inc* = precomposeF (SET ℓm) (Inc)

        open Ran C isGrpCob hiding (Inc* ; Inc)
        open End renaming (fun to end)

        U' : Functor Fam 𝓥
        U' = Ran

        U : Functor 𝓒 𝓥 
        U = U' ∘F  Inc* 

        open Lan (C ^op) isGrpCob hiding (Inc* ; Inc)

        F' : Functor Fam 𝓒 
        F' = Lan

        F : Functor 𝓥 𝓒 
        F = Lan ∘F precomposeF (SET ℓm) (DiscFunc λ x → x)

        private 
            open import Cubical.Data.Unit
            testF : (A : ob 𝓥) → 𝓒 [ Constant _ _ (Unit* , isSetUnit*) , F .F-ob A ]
            testF A .N-ob x tt* = y , f , Ay where 
                postulate y : ob C
                postulate f : (C ^op)[ x , y ]
                postulate Ay : A .F-ob y .fst
                
            testF A .N-hom f = {!   !}

        open import Cubical.Foundations.Function
        
        𝓞' : BifunctorPar (𝓥 ^op) 𝓒 (SET ℓm) 
        𝓞' .Bif-ob v c = (∀ (x : ob C) → v .F-ob x .fst  → c .F-ob x .fst) , isSetΠ λ x → isSet→ (c .F-ob x .snd) 
        𝓞' .Bif-hom× f g m x = (g .N-ob x ∘S m x) ∘S f .N-ob x 
        𝓞' .Bif-×-id = refl 
        𝓞' .Bif-×-seq f₁ f₂ g₁ g₂ = refl 
        
        𝓞 : Bifunctor (𝓥 ^op) 𝓒 (SET ℓm) 
        𝓞 = mkBifunctorPar 𝓞'

        -- oblique morphisms
        𝓞[_,_] : ob 𝓥 → ob 𝓒 → Set ℓm
        𝓞[ v , c ] = (𝓞 .Bif-ob v c) .fst

        open import Cubical.Categories.Adjoint
        open AdjointUniqeUpToNatIso 
        open NaturalBijection
        open _⊣_

        -- the existence of these isomorphisms are mentioned on page 210 of Levy's thesis
        ob₁ : {P : ob 𝓥}{Q : ob 𝓒} → Iso (𝓥 [ P , U .F-ob Q ]) 𝓞[ P , Q ] 
        ob₁ {P} {Q} = iso 
                        (λ nt x Px → nt .N-ob x Px .end x (C .id)) 
                        (λ o → natTrans (λ x Px → record { fun = λ y y→x → o y (P .F-hom y→x Px) }) 
                                λ f  → funExt λ Px → end≡ (Q ∘F Inc) λ z z→y → cong (λ h → o z h) 
                                    (funExt⁻ (sym (P .F-seq _ _))_)) 
                        (λ b  → funExt λ x → funExt λ Px → cong (λ h → b x h ) (funExt⁻ (P .F-id) _)) 
                        λ b → makeNatTransPath (funExt λ x → funExt λ Px → end≡  ((Q ∘F Inc)) λ y y→x  →
                                cong (λ h → h .Ran.End.fun y (C .id)) (funExt⁻ (b .N-hom y→x) Px) 
                                ∙ cong (λ h → b .N-ob x Px .Ran.End.fun y h) (C .⋆IdL _))

        ob₂ : {P : ob 𝓥}{Q : ob 𝓒} → Iso 𝓞[ P , Q ] (𝓒 [ F .F-ob P , Q ]) 
        ob₂ {P}{Q}= iso 
                (λ o → natTrans (λ{x (y , (y→x , Py)) → Q .F-hom y→x (o y Py)}) 
                        λ f → funExt λ{(z , (z→x , Pz)) → funExt⁻ (Q .F-seq _ _ ) _}) 
                (λ nt x Px → nt .N-ob x (x , ((C .id) , Px))) 
                (λ b → makeNatTransPath (funExt λ x → funExt λ{(y , (y→x , Py)) → 
                    funExt⁻ (sym (b .N-hom y→x)) _ 
                    ∙ cong (λ h → b .N-ob x h) (ΣPathP (refl , (ΣPathP ((C .⋆IdL _) , refl))))})) 
                λ b → funExt λ x → funExt λ Px → funExt⁻ (Q .F-id) _

        adjhom : {X : ob 𝓥}{Y : ob 𝓒} → Iso (𝓥 [ X , U .F-ob Y ]) (𝓒 [ F .F-ob X , Y ])
        adjhom = compIso ob₁ ob₂

        F⊣U : F ⊣ U 
        F⊣U .adjIso = invIso adjhom 
        F⊣U .adjNatInD _ _ = makeNatTransPath (funExt λ _ → funExt λ _ → refl) 
        F⊣U .adjNatInC _ _ = makeNatTransPath (funExt λ _ → funExt λ _ → refl) 

        open import Cubical.Categories.Adjoint.Monad
        open import Cubical.Categories.Monad.Base

        T : Functor 𝓥 𝓥
        T = U ∘F F

        M : Monad 𝓥
        M = T , (MonadFromAdjunction F U (adj'→adj F U F⊣U))

        module _ where 
            private 

                open IsMonad (M .snd) renaming (η to ret)

                ret' : {A : ob 𝓥} → 𝓥 [ A , T .F-ob A ]
                ret' {A} .N-ob x Ax .end y x→y = y , (C .id , A .F-hom x→y Ax)
                ret' {A} .N-hom = {!   !}

                _  :{A : ob 𝓥} → ret' {A} ≡ ret .N-ob A
                _ = makeNatTransPath (funExt λ x → funExt λ Ax → refl)

                module _ (A : ob 𝓥) (x y : ob C)(f : C [ y , x ]) where 
                    fmap : T .F-ob A .F-ob x .fst → T .F-ob A .F-ob y .fst 
                    fmap tax .end z z→y = tax .end z (f ⋆⟨ C ^op ⟩ z→y) 

                    _ : T .F-ob A .F-hom f ≡ fmap
                    _ = refl


        𝓞× : ob 𝓥 → ob 𝓥 → ob 𝓒 → Set ℓm
        𝓞× v₁ v₂ c = ∀ (x y : ob C) → v₁ .F-ob x .fst × v₂ .F-ob y .fst → c .F-ob (⨂c .F-ob (x , y)) .fst

        -- looks like you can't define the ⨂UP for oblique morphisms here?
        module attempt where
            frwd :{P Q : ob 𝓥}{R : ob 𝓒} → 𝓞[ P ⨂ᴰ Q , R ] → 𝓞× P Q R 
            frwd {P}{Q}{R} o x y (Px , Qy) = o (⨂c .F-ob (x , y)) (inc ((x , y) , (((C .id) , Px) , Qy)))
            
            open Iso renaming (fun to fun')
            open DayUP
            open UniversalProperty
            
            -- looks like you can't define this ..?
            -- at least for an opaque category C .. what if things are concrete?
            bkd : {P Q : ob 𝓥}{R : ob 𝓒} → 𝓞× P Q R → 𝓞[ P ⨂ᴰ Q , R ]
            bkd {P}{Q}{R} o x = 
                inducedHom 
                    (R .F-ob x .snd) 
                    -- same issue , have R(x ⊗c y) and z→x⊗y but need R(z) 
                    -- and R is covariant..
                    (λ{((y , z) , (x→y⊗z , Py) , Qz) → {! R .F-hom x→y⊗z  !} })--{! o y z (Py , Qz)  !}}) 
                    {!   !}
                --ob₁ {P ⨂ᴰ Q}{R} .fun' (⨂UP {P}{Q}{U .F-ob R} .inv (natTrans (λ{(x , y)(Px , Qy) → record { fun = λ z z→x⊗y → {! o x y (Px , Qy)  !} }}) {!   !})) 
            
            ⨂UP𝓞 : {P Q : ob 𝓥}{R : ob 𝓒} → Iso 𝓞[ P ⨂ᴰ Q , R ] (𝓞× P Q R) 
            ⨂UP𝓞 {P}{Q}{R} = 
                iso 
                    (frwd {P}{Q}{R})
                    (bkd {P}{Q}{R}) 
                    {!   !} 
                    {!   !}

        -- computational function type
        -- TODO feed seq
        fun : ob 𝓥 → ob 𝓒 → ob 𝓒 
        fun A B .F-ob w = (SET ℓm)[ A .F-ob w , B .F-ob w ] , (SET ℓm) .isSetHom
        fun A B .F-hom f g Ay = (B .F-hom f) (g ((A .F-hom f) Ay)) 
        fun A B .F-id = funExt λ g → funExt λ a → 
            B .F-hom (id C) (g (A .F-hom (id C) a)) ≡⟨ funExt⁻  (B .F-id) _ ⟩
            (g (A .F-hom (id C) a)) ≡⟨ cong g (funExt⁻ (A .F-id) _) ⟩ 
            g a ∎
        fun A B .F-seq f g = funExt λ h → funExt λ Az → funExt⁻ (B .F-seq f g) _ ∙ 
            cong (λ x → seq' (SET ℓm) (F-hom B f) (F-hom B g) (h x)) (funExt⁻ (A .F-seq _ _) _)


        _×p_ : ob 𝓥 → ob 𝓥 → ob 𝓥 
        _×p_ A B = PshProd .Bif-ob A B

        module funUP {P Q : ob 𝓥}{R : ob 𝓒} where 
            
            funIntro : 𝓞[ P ×p Q , R ] → 𝓞[ P , fun Q R ] 
            funIntro f = λ x Px Qx → f x (Px , Qx)

            funIntroInv : 𝓞[ P , fun Q R ] → 𝓞[ P ×p Q , R ] 
            funIntroInv f = λ{x (Px , Qx) → f x Px Qx}

            -- fun up
            →UP : Iso (𝓞[ P ×p Q , R ]) (𝓞[ P , fun Q R ])
            →UP = iso 
                        funIntro 
                        funIntroInv 
                        (λ b → refl)
                        (λ b → refl)


        sep : ob 𝓥 → ob 𝓒 → ob 𝓒 
        -- should be an end ?
        sep A B .F-ob w = (∀ (w' : ob C) → (SET ℓm)[ A .F-ob w' , B .F-ob (⨂c .F-ob (w , w')) ]) , isSetΠ  λ _ → (SET ℓm) .isSetHom
        sep A B .F-hom {w₁}{w₂} w₁→w₂ end w₃ Aw₃ = B .F-hom (⨂c .F-hom (w₁→w₂ , C .id)) (end w₃ Aw₃)
        sep A B .F-id = funExt λ end → funExt λ w₃  → funExt λ Aw₃ → cong (λ x → (B .F-hom x) (end w₃ Aw₃) ) (⨂c .F-id) ∙ funExt⁻ (B .F-id) ((end w₃ Aw₃))
        sep A B .F-seq f g = funExt λ end → funExt λ w₃  → funExt λ Aw₃ → cong (λ h → B .F-hom h _) 
            ( cong (λ h → ⨂c .F-hom h) (≡-× refl (sym (C .⋆IdL _))) ∙ (⨂c .F-seq _ _)) 
            ∙ funExt⁻ ( (B .F-seq (⨂c .F-hom (f , C .id)) (⨂c .F-hom (g , C .id)))) (end w₃ Aw₃)

        module cbpvSepUP {P Q : ob 𝓥}{R : ob 𝓒}where                         
            open Iso renaming (fun to fun')
            open DayUP

            test : 𝓥× [ P ⨂Ext Q , U .F-ob R ∘F (⨂c ^opF) ] → 𝓥 [ P , U .F-ob (sep Q R) ]
            test nt = natTrans η' η'com where
                η' : N-ob-Type P (U .F-ob (sep Q R)) 
                η' x Px = record { fun = λ y y→x z Qz → nt .N-ob (y , z) (P .F-hom y→x Px , Qz) .end (⨂c .F-ob (y , z)) (C .id) } 

                η'com : N-hom-Type P (U .F-ob (sep Q R)) η' 
                η'com f = funExt λ Px → end≡ ((sep Q R) ∘F Inc) λ z z→y  → 
                    funExt λ w → funExt λ Qw → 
                    cong (λ h → nt .N-ob (z , w) (h , Qw) .Ran.End.fun (⨂c .F-ob (z , w)) (C .id) ) (funExt⁻ (sym(P .F-seq f z→y )) Px)


            eval : 𝓥× [ (U .F-ob (sep Q R)) ⨂Ext Q , U .F-ob R ∘F (⨂c ^opF) ] 
            eval .N-ob (x , y) (UQ→Rx , Qy) .end z z→x⊗y = goal where 
                goal : R .F-ob z .fst
                goal = {!UQ→Rx .end z  !}
                
                have : R .F-ob (⨂c .F-ob (x , y)) .fst 
                have = UQ→Rx .end x (C .id) y Qy

                cantuse : SET ℓm [ F-ob R z , F-ob R ((⨂c ^opF) ⟅ x , y ⟆) ]
                cantuse = R .F-hom z→x⊗y
                _ = {! UQ→Rx .end  !}
                
            eval .N-hom = {!   !}

            testInv : 𝓥 [ P , U .F-ob (sep Q R) ] → 𝓥× [ P ⨂Ext Q , U .F-ob R ∘F (⨂c ^opF) ]
            testInv nt = ⨂ext .F-hom (nt , (𝓥 .id)) ⋆⟨ 𝓥× ⟩ eval
            
            goal : Iso (𝓥× [ P ⨂Ext Q , U .F-ob R ∘F (⨂c ^opF) ]) (𝓥 [ P , U .F-ob (sep Q R) ])
            goal = iso 
                    test
                    -- (λ nt → natTrans (λ x Px → record { fun = λ y y→x z Qz → {!  nt .N-ob (x , z) (Px , Qz) .end z !} }) {!   !}) 
                    testInv 
                    {!   !} 
                    {!   !}


            ⊸UP' : Iso (𝓥 [ P ⨂ᴰ Q , U .F-ob R ]) (𝓥 [ P , U .F-ob (sep Q R) ] )
            ⊸UP' = compIso ⨂UP goal

            ⊸UP : Iso 𝓞[ P ⨂ᴰ Q , R ] 𝓞[ P , sep Q R ] 
            ⊸UP = compIso (invIso(ob₁ {P ⨂ᴰ Q }{R})) (compIso ⊸UP' (ob₁ {P}{sep Q R}))


        -- from 8-2-24 meeting
        module Test (P : ob 𝓥)(Q : ob 𝓒) where 
            test1 : CatIso 𝓥 (U .F-ob (sep P Q)) (P ⊸ U .F-ob Q)
            test1 = (natTrans (λ x UP→Qx → natTrans (λ y Py → 
                record { fun = λ z z→x⊗y → {! Q .F-hom z→x⊗y  !} }) {! (UP→Qx .end x (C .id) y Py)   !}) {!  Q .F-hom !}) , {!   !}

            
            lemma : {x : ob C} → Q .F-ob (⨂c .F-ob (x , unit)) .fst ≡ Q .F-ob x .fst 
            lemma = cong (λ h → Q .F-ob h .fst) (idr _)

            test2 : CatIso 𝓒 (sep (I⨂ (SMC)) Q) Q 
            test2 = (natTrans (λ x sepIQ → Q .F-hom {! (idr _)  !} (sepIQ unit (lift (C .id))))
            -- transport lemma (sepIQ unit (lift (C .id)))) 
                              {!  !}) , 
                              -- issue
                              -- you need a map C [ x , x ⨂c y]
                              -- which you could construct IF
                              -- f : C [ x , x ⨂c unit ] = inr .fun
                              -- g : C [ x ⨂c unit , x ⨂c y] = ⨂c .map idₓ (unit→y)
                              -- BUT, here we have y→unit
                    isiso (natTrans (λ x Qx y y→unit → Q .F-hom {!   !} Qx) {!   !}) {!   !} {!   !}

        -- from 8-8-24 meeting
        module str (P Q : ob 𝓥)where

            ×str : 𝓥 [ P ×p T .F-ob Q , T .F-ob (P ×p Q) ]
            ×str .N-ob x (Px , TQx) .end y y→x = z , (z→y , Pz , Qz) where 
                -- extract the past/future world from TQx and lift Px into this world
                z : ob C
                z  = TQx .end y y→x .fst

                z→y : C [ z , y ]
                z→y = TQx .end y y→x .snd .fst

                Qz : Q .F-ob z .fst 
                Qz = TQx .end y y→x .snd .snd 

                Pz : P .F-ob z .fst 
                Pz = P .F-hom (z→y ⋆⟨ C ⟩ y→x) Px

            ×str .N-hom {x}{y} f = funExt λ {(Px , TQx) → {!  x !}}

            open DayUP
            open Iso hiding (fun)
            ⊗str : 𝓥 [ P ⨂ᴰ T .F-ob Q , T .F-ob (P ⨂ᴰ Q) ]
            ⊗str = ⨂UP {P}{T .F-ob Q} .inv goal where 
                goal : 𝓥× [ P ⨂Ext T .F-ob Q , T .F-ob (P ⨂ᴰ Q) ∘F (⨂c ^opF) ]
                goal .N-ob (x , y) (Px , TQy) .end z z→x⊗y = v , (v→z , d) where 

                    module _ where 
                        private
                            -- what if we had z→y, we could get a restricted map out of z→x⊗y
                            postulate z→y : C [ z , y ]
                            w' : ob C
                            w' = TQy .end z z→y .fst

                            w'→z : C [ w' , z ]
                            w'→z = TQy .end z z→y .snd .fst

                            Qw' : Q .F-ob w' .fst 
                            Qw' = TQy .end z z→y .snd .snd
                        
                            -- intuition doesn't make sense, and you'd need a map C [ y , w' ]
                            d : (P ⨂ᴰ Q) .F-ob w' .fst 
                            d = inc ((x , y) , ((w'→z ⋆⟨ C ⟩ z→x⊗y , Px) , Q .F-hom {!   !} Qw'))


                    w : ob C 
                    -- need a morphism into y
                    -- the only one we have available is id_y
                    -- unlike the case with tensor strength for product, 
                    -- we dont apply TQ to the future world morphism
                    w = TQy .end y (C .id) .fst

                    w→y : C [ w , y ]
                    w→y = TQy .end y (C .id) .snd .fst

                    Qw : Q .F-ob w .fst
                    Qw = TQy .end y (C .id) .snd .snd

                    -- what we need to provide
                    -- a past object v, and a map C [ v , z ]
                    -- the only one we have available is id_z
                    v : ob C 
                    v = z

                    v→z : C [ v , z ]
                    v→z = C .id

                    -- a diagram at v

                    -- for x' we could just use x
                    -- we already have Px
                    x' : ob C 
                    x' = x

                    Px' : P .F-ob x' .fst 
                    Px' = Px
                    -- both options are equal under the coend qotient. - day-fact
                    module option1 where
                        -- we can try to use y here
                        y' : ob C 
                        y' = y

                        -- in which case we have this morphism 
                        v→x'⊗y' : C [ v , x' ⊗ y' ]
                        v→x'⊗y' = z→x⊗y

                        -- but the issue is we have a Qw and need a Qy
                        -- and the variance of Q does not allow us to get Qy
                        -- from Qw
                        Qy' : Q .F-ob y' .fst 
                        Qy' = {! Q .F-hom w→y ? !}

                    module option2 where
                        -- we can try to use w since we have Qw
                        y' : ob C 
                        y' = w

                        Qy' : Q .F-ob y' .fst 
                        Qy' = Qw 

                        -- then we'd need a C [ z , x ⊗ w ]
                        -- but we have C [ z , x ⊗ y] and C [ w , y ]
                        v→x'⊗y' : C [ v , x' ⊗ y' ]
                        v→x'⊗y' = {!   !}
  
                    open option1             
                    
                    d : (P ⨂ᴰ Q) .F-ob v .fst 
                    d = inc ((x' , y') , ((v→x'⊗y' , Px') , Qy'))
        
                goal .N-hom = {!   !}
   