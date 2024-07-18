-- {-# OPTIONS --lossy-unification #-}
module src.Data.BiDCC where 
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


    module Mod {ℓ ℓ' : Level}(SMC : StrictMonCategory ℓ ℓ') where 
        ℓm = (ℓ-max ℓ ℓ')
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
        open StrictMonCategory SMC renaming(─⊗─ to ⨂c)
        
        𝓥 : Category (ℓ-suc ℓm) ℓm 
        𝓥 = PresheafCategory C ℓm 

        _⨂ᴰ_ : ob 𝓥 → ob 𝓥 → ob 𝓥
        A ⨂ᴰ B =  _⊗ᴰ_  {MC = SMC} A B


        open import Cubical.Categories.Constructions.BinProduct.Redundant.Base renaming (_×C_ to _R×C_)
    
        𝓥× : Category (ℓ-suc ℓm) ℓm
        𝓥× = PresheafCategory (C B×C C)ℓm

        open import Cubical.Categories.Instances.Sets.Properties
        open import Cubical.Categories.Limits.BinProduct.More
        open import Cubical.Categories.Limits.BinProduct

        SetBP : BinProducts (SET ℓm)
        SetBP = BinProducts'ToBinProducts {(ℓ-suc ℓm)} {ℓm} (SET ℓm) BinProducts'SET 

        SetProdR : Functor (SET (ℓm) R×C SET (ℓm) ) (SET  (ℓm))
        SetProdR = BinProductF {(ℓ-suc ℓm)} {ℓm} (SET ℓm) SetBP

        SetProdB : Functor (SET ℓm B×C SET ℓm) (SET ℓm)
        SetProdB = SetProdR ∘F ProdToRedundant (SET ℓm) (SET ℓm)

        𝓥BinProd : BinProducts 𝓥
        𝓥BinProd = ×𝓟 {ℓ} {ℓ'} {C} {ℓm}

        open Notation 𝓥 𝓥BinProd renaming (_×_ to _×N_ ; _×p_ to UHG ; _,p_ to ADF)
        open import Cubical.Categories.Limits.BinProduct.More

        -- theres probably a slicker way to define this.. I just don't know the combinators
        ⨂ext : Functor (𝓥 B×C 𝓥) 𝓥× 
        ⨂ext .F-ob (P , Q) = SetProdB ∘F (P ×F Q)
        ⨂ext .F-hom (nt1 , nt2) = 
            SetProdB ∘ʳ natTrans 
                            (λ{(s , t) → nt1 .N-ob s , nt2 .N-ob t}) 
                            λ{(f , g) → λ i → (nt1 .N-hom f i) , (nt2 .N-hom g i) }
        ⨂ext .F-id = makeNatTransPath refl
        ⨂ext .F-seq f g = makeNatTransPath refl

        _⨂Ext_ : ob 𝓥 → ob 𝓥 → ob 𝓥× 
        P ⨂Ext Q = ⨂ext .F-ob (P , Q)
        
        module DayUP {P Q R : ob 𝓥} where 
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

            diag : ob C → Bifunctor ((C B×C C) ^op) (C B×C C) (SET ℓm)
            diag = diagram {MC = SMC} P Q
            
            Dom : (x : ob C) → Set ℓm
            Dom x = Σ[ X ∈ (ob C × ob C) ] 
                     Σ[ Y ∈ (ob C × ob C) ] 
                     Σ[ (f , g) ∈ ((C B×C C) [ Y , X ]) ] 
                     ((diag x ⟅ (X , Y) ⟆b ) .fst)

            Diag : (x : ob C) → Set ℓm
            Diag x = Σ[ (y , z) ∈ (ob C × ob C)] (fst (diag x ⟅ (y , z) , (y , z) ⟆b))

            Day' : (c : ob C) → Coend (diag c)
            Day' = Day  {MC = SMC} P Q

            DayCoe : (c : ob C) → hSet ℓm
            DayCoe c = Day' c .cowedge .nadir

            mapout : (nf : 𝓥× [ P ⨂Ext Q , R ∘F (⨂c ^opF) ] ) → 
                (x : ob C) → Diag x → R .F-ob x .fst  
            mapout nf x ((y , z) , (x→y⊗z , Py) , Qz) = R .F-hom x→y⊗z (nf .N-ob (y , z) (Py , Qz))

            mapoutcoeq : (m : 𝓥× [ P ⨂Ext Q , R ∘F (⨂c ^opF) ])
                (x : ob C)
                (a : Dom x ) → 
                mapout m x (lmap (diag x) a) 
                 ≡
                mapout m x (rmap (diag x) a)
            mapoutcoeq 
                record { N-ob = m ; N-hom = natfam } 
                x 
                ((y , z) , (y' , z') , (f , g) , (x→y'⊗z' , Py) , Qz) = 
                    funExt⁻ (R .F-seq _ _)  (m (y ,  z) (F-hom P (C . id) Py , F-hom Q (C . id) Qz)) 
                    ∙ cong (λ h →  F-hom R x→y'⊗z' h) 
                        (((cong₂ (λ h1 h2 → F-hom R ((f ⊗ₕ g)) (m (_ ,  _ ) (h1 , h2))) (funExt⁻ (P .F-id) _) ((funExt⁻ (Q .F-id) _)) 
                        ∙ funExt⁻ (sym (natfam (f , g))) _) -- using naturality of the family
                        ∙ funExt⁻ (sym (R .F-id )) (m (_ , _ )(F-hom P f Py , F-hom Q g Qz))) 
                        ∙ cong (λ h → R .F-hom h (m (_ , _) (F-hom P f Py , F-hom Q g Qz))) (sym (sms .tenstr .─⊗─ . F-id)))
                    ∙ funExt⁻ (sym (R .F-seq _ _)) (m (_ , _) (F-hom P f Py , F-hom Q g Qz)) 

            η≡ : {x : ob C }
                {nf : 𝓥× [ P ⨂Ext Q , R ∘F (⨂c ^opF) ]}
                {other : SET ℓm [ (P ⨂ᴰ Q) .F-ob x , R .F-ob x ] }
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

            fwd : 𝓥 [ P ⨂ᴰ Q , R ] → 𝓥× [ P ⨂Ext Q , R ∘F (⨂c ^opF) ]
            fwd nt .N-ob (x , y) (Px , Qy) = nt .N-ob (x ⊗ y) (inc ((x , y) , (((C .id) , Px) , Qy)))
            fwd nt .N-hom {(x , y)}{(x' , y')} (f , g) = 
                funExt (λ p → cong (λ h → nt .N-ob ( x' ⊗ y') h)  
                    (sym (day-fact {MC = SMC} P Q {f = f}{g = g}{h = C .id}{p .fst}{p .snd}{f ⊗ₕ g} (sym (C .⋆IdL _))) 
                    ∙ day-apₘ {MC = SMC} P Q (sym (C .⋆IdR _))))
                ∙ (funExt λ{(Px , Qy) → funExt⁻ ((nt .N-hom (f ⊗ₕ g))) (inc ((x , y) , (C .id , Px) , Qy))}) 

            bkwd : 𝓥× [ P ⨂Ext Q , R ∘F (⨂c ^opF) ] → 𝓥 [ P ⨂ᴰ Q , R ] 
            bkwd nf = natTrans η ηnat where 
                η : N-ob-Type (P ⨂ᴰ Q) R 
                η x = inducedHom 
                        (R .F-ob x .snd) 
                        (mapout nf x) 
                        (mapoutcoeq nf x)

                ηnat : N-hom-Type (P ⨂ᴰ Q) R η 
                ηnat {x}{y} f = r∘t≡ind ∙ sym (b∘l≡ind) where
                    open SetCoequalizer
                    --show that the diagram commutes since both paths are equal
                    -- because they yield the same inducedHom
                    r : (SET _)[ (P ⨂ᴰ Q) .F-ob x , R .F-ob y ] 
                    r = seq' (SET _) {(P ⨂ᴰ Q) .F-ob x}{(P ⨂ᴰ Q) .F-ob y}{R .F-ob y}
                        ((P ⨂ᴰ Q) .F-hom f) (η y)

                    l : (SET _)[ (P ⨂ᴰ Q) .F-ob x , R .F-ob y ]
                    l = seq' (SET _){(P ⨂ᴰ Q) .F-ob x}{R .F-ob x}{R .F-ob y}
                        (η x) (R .F-hom f)

                    td : Diag x → DayCoe y .fst
                    td (x , Fxx) = Day-cowedge {MC = SMC} P Q f .ψ x Fxx 

                    tcom : (a : Dom x) → td ((lmap (diag x)) a) ≡ td ((rmap (diag x)) a)
                    tcom (X , Y , g , Fxy) = funExt⁻ (Day-cowedge {MC = SMC} P Q f .extranatural g) Fxy 


                    trcom : (a : Dom x) → η y (td (lmap (diag x) a)) ≡ η y (td (rmap (diag x) a))
                    trcom a = cong (λ h → η y h) (tcom a)

                    ind : DayCoe x .fst → R .F-ob y .fst 
                    ind = (inducedHom (R .F-ob y .snd) (η y ∘S td) trcom)

                    r∘t≡ind : (η y) ∘S ((P ⨂ᴰ Q) .F-hom f) ≡ ind
                    r∘t≡ind = 
                        uniqueness 
                            ((lmap (diag x))) 
                            ((rmap (diag x))) 
                            (R .F-ob y .snd) 
                            (η y ∘S td)
                            trcom 
                            r 
                            λ _ → refl

                    b∘l≡ind : ((R .F-hom f) ∘S (η x)) ≡ ind
                    b∘l≡ind = 
                        uniqueness
                            ((lmap (diag x))) 
                            ((rmap (diag x))) 
                            (R .F-ob y .snd) 
                            ((η y ∘S td)) 
                            trcom 
                            l 
                            λ _ → funExt⁻ (R .F-seq _ _) _

            ⨂UP :  Iso (𝓥 [ P ⨂ᴰ Q , R ]) (𝓥× [ P ⨂Ext Q , R ∘F (⨂c ^opF) ]) 
            ⨂UP = iso 
                    fwd 
                    bkwd 
                    (λ b → makeNatTransPath (funExt λ{(x , y) → funExt λ{(Px , Qy) → funExt⁻ (R .F-id) _ }}) )
                    (λ b → makeNatTransPath (funExt λ x → 
                                -- show the components are equal by showing they are equal maps on diagrams
                                sym (η≡  λ {((y , z) , (x→y⊗z , Py) , Qz) → 
                                    funExt⁻ (sym (b .N-hom _)) _ 
                                        ∙ cong (λ h → b .N-ob x h) (day-apₘ {MC = SMC} P Q (C .⋆IdR _))} ))) 
 
        {-
        alternative def using right adjoint instead of iso of homsets
        open import Cubical.Categories.Adjoint.2Var
        sep : Type _
        sep = RightAdjointL {! Functor→Bifunctor  !} -}



        -- TODO compare .. just a family of sets vs partial nat trans!
        -- which is correct!?
        -- remember, the setup CBPV is different
        {- 
                    _⊸_ : ob 𝒱 → ob 𝒱 → ob 𝒱
            -- todo make a Set^Inj
            _⊸_ A B .F-ob X = (∀ (Y : ob Inj) → (SET ℓS) [ A .F-ob Y , B .F-ob (_⨂_ .F-ob (X , Y)) ]) , isSetΠ  λ _ → (SET ℓS) .isSetHom
            _⊸_ A B .F-hom {X} {Y} f FX Z AZ = B .F-hom (_⨂_ .F-hom (f , (Inj .id))) (FX Z AZ)
            _⊸_ A B .F-id = {!   !}
                --funExt λ e → funExt λ x → funExt λ Ax → cong (λ h → B .F-hom h (e x Ax)) ((_⨂_ .F-id)) ∙ funExt⁻ (B .F-id) _
            _⊸_ A B .F-seq = {!   !}
        -} 


        {- 
          _∘ʳ_ : ∀ (K : Functor C D) → {G H : Functor B C} (β : NatTrans G H)
       → NatTrans (K ∘F G) (K ∘F H)
        -}
        open import src.Data.Semicartesian
        ⨂c^op = ─⊗─^op where 
            open StrictMonCategory (SMC ^opMon) renaming (─⊗─ to ─⊗─^op)
        open import Cubical.Categories.Instances.Functors.More
        
        _⨂c- : Functor (C ^op) (FUNCTOR (C ^op) (C ^op))
        _⨂c- = curryF (C ^op) (C ^op) {Γ = (C ^op)} .F-ob ⨂c^op

        _⦅_⊗-⦆ : ob 𝓥 → ob C → ob 𝓥
        _⦅_⊗-⦆ P x = P ∘F (_⨂c- .F-ob x)

        private 
            test : (x y : ob C) → (R : ob 𝓥) → (R ⦅ x ⊗-⦆) .F-ob y ≡ R .F-ob (x ⊗ y)
            test x y R = refl
            
        partialAp : {x y : ob C}(P : ob 𝓥)(f : (C ^op) [ x , y ]) → 𝓥 [ P ⦅ x ⊗-⦆ , P ⦅ y ⊗-⦆ ]
        partialAp {x}{y} P f = P ∘ʳ (_⨂c- .F-hom f)

        partialApId : {x : ob C}(P : ob 𝓥) → 
            partialAp P (C .id) ≡ idTrans (P ⦅ x ⊗-⦆)
        partialApId P = 
            (λ i → P ∘ʳ (_⨂c- .F-id) i) 
            ∙ makeNatTransPath (funExt λ x → P .F-id)
        
        partialSeq : {x y z : ob (C ^op)}(P : ob 𝓥)(f : (C ^op) [ x , y ])(g : (C ^op) [ y , z ]) → 
            partialAp P (f ⋆⟨ C ^op ⟩ g) ≡ partialAp P f ⋆⟨ 𝓥 ⟩ partialAp P g
        partialSeq {x}{y}{z} P f g = 
            (λ i → P ∘ʳ (_⨂c- .F-seq f g) i) 
            ∙ makeNatTransPath (funExt λ w → (P .F-seq _ _))
          

        _⊸_ : ob 𝓥 → ob 𝓥 → ob 𝓥 
        (P ⊸ Q) .F-ob x = 𝓥 [ P , Q ⦅ x ⊗-⦆ ] , 𝓥 .isSetHom
        (P ⊸ Q) .F-hom f nt = nt ⋆⟨ 𝓥 ⟩ partialAp Q f
        (P ⊸ Q) .F-id = funExt λ nt → cong (λ h → seqTrans nt h) (partialApId Q) ∙ 𝓥 .⋆IdR nt
        (P ⊸ Q) .F-seq {x}{y}f g = funExt λ nt → 
            cong (λ h → seqTrans nt h) (partialSeq Q f g) 
            ∙ sym (𝓥 .⋆Assoc nt (partialAp Q f) (partialAp Q g))



        module SepUP {P Q R : ob 𝓥} where 
            open DayUP
            η : N-ob-Type ((Q ⊸ R) ⨂Ext Q) (R ∘F (⨂c ^opF))
            η (y , z) (f , q) = f .N-ob z q
            eval : 𝓥 [ ((Q ⊸ R) ⊗ᴰ Q) , R ] 
            eval = ⨂UP .inv (natTrans η ηcom) where


                ηcom : N-hom-Type ((Q ⊸ R) ⨂Ext Q) (R ∘F (⨂c ^opF)) η
                ηcom {(y , z)}{(y' , z')}(y'→y , z'→z) = funExt sub where

                    sub : ((Q⊸Ry , Qz) : fst (F-ob ((Q ⊸ R) ⨂Ext Q) (y , z))) → 
                        F-hom R (⨂c .F-hom (y'→y , (C .id))) (Q⊸Ry .N-ob z' (F-hom Q z'→z Qz))
                      ≡ F-hom R (⨂c .F-hom (y'→y , z'→z))    (Q⊸Ry .N-ob z Qz)
                    sub (Q⊸Ry , Qz) = 
                        -- use naturality of Q⊸Ry 
                        cong (λ h → R .F-hom _ h) (funExt⁻ ( Q⊸Ry .N-hom z'→z ) Qz) 
                        ∙ funExt⁻ (sym (R .F-seq _ _ )) _ 
                        ∙ cong (λ h → R .F-hom h _) 
                            (sym (⨂c .F-seq _ _) ∙ cong (λ h → ⨂c .F-hom h) (≡-× (C .⋆IdR _) (C .⋆IdL _)))  

            ⊸Intro : 𝓥 [ P ⨂ᴰ Q , R ] → 𝓥 [ P , Q ⊸ R ] 
            ⊸Intro nt = natTrans ηi ηcomi where 
                ηi : N-ob-Type P (Q ⊸ R) 
                ηi x Px = natTrans η' η'com where 
                    η' : N-ob-Type Q (R ⦅ x ⊗-⦆)
                    η' y Qy = nt .N-ob (x ⊗ y) ((inc ((x , y) , (((C .id) , Px) , Qy))))

                    η'com : N-hom-Type Q (R ⦅ x ⊗-⦆) η' 
                    η'com {y}{z} z→y = 
                        funExt λ Qy → 
                            cong (λ h → nt .N-ob _ h) 
                                (day-ap {MC = SMC} P Q refl (funExt⁻ (sym (P .F-id )) Px) refl 
                                ∙ sym (day-fact {MC = SMC} P Q {f = C .id}{z→y}{C .id}{Px}{Qy} 
                                    (C .⋆IdR _ ∙ sym (C .⋆IdL _))))
                            -- use naturality of nt
                            ∙  funExt⁻ (nt .N-hom (((C ^op) .id) ⊗ₕ z→y)) (inc ((x , y) , (((C .id) , Px) , Qy)))


                ηcomi : N-hom-Type P (Q ⊸ R) ηi 
                ηcomi {x}{y} y→x = funExt λ Px → makeNatTransPath (funExt λ z → funExt λ Qz → 
                        cong (λ h → nt .N-ob _ h) ((day-ap {MC = SMC} P Q refl refl ((funExt⁻ (sym (Q .F-id )) Qz)) ) 
                            ∙ sym (day-fact {MC = SMC} P Q {f = y→x}{C .id}{C .id}{Px}{Qz}{ y→x ⊗ₕ (C .id)} (sym (C .⋆IdL _))) 
                            ∙ day-apₘ {MC = SMC} P Q (sym(C .⋆IdR _)))
                        -- use naturality of nt
                        ∙ funExt⁻ (nt .N-hom (y→x ⊗ₕ (C .id{z}))) (inc ((x , z) , (C .id , Px) ,  Qz)))

            ⊸IntroInv : 𝓥 [ P , Q ⊸ R ] → 𝓥 [ P ⨂ᴰ Q , R ] 
            ⊸IntroInv nt = (Day-Functor SMC .F-hom (nt , 𝓥 .id)) ⋆⟨ 𝓥 ⟩ eval


            what : (nt : NatTrans P (Q ⊸ R)) →  𝓥× [ P ⨂Ext Q , R ∘F (⨂c ^opF) ] 
            what nt = ⨂UP {P}{Q}{Q ⊸ R} .fun {!(⊸IntroInv nt)   !} ⋆⟨ 𝓥× ⟩ {!   !}
            hmm : (nt : NatTrans P (Q ⊸ R)) → {! (⊸Intro (⊸IntroInv nt))  !}
            hmm nt = {! ⨂UP {P}{Q}{R} .fun  !}
--(⊸Intro (⊸IntroInv nt))
            prf : section ⊸Intro ⊸IntroInv
            prf nt = {! nt  !}
                {-}
                -- need to show these two homsets are equal, 
                -- they are natural transformations so their components need to be equal
                makeNatTransPath 
                -- lets reason pointwise
                (funExt λ x → funExt λ Px → 
                -- each component results in a natural transformation 𝓥 [ Q , partial x R ]
                -- we need to show they are equal 
                makeNatTransPath 
                -- again reasoning pointwise
                (funExt λ y → funExt λ Qy →
                -- one component of the natrual transformation is given by inducedHom
                -- to reason about it, we need to use uniqueness to see if the underlying maps are equal
                funExt⁻ (sym 
                    (uniqueness 
                        (lmap (diag {P}{Q}{R}(x ⊗ y))) 
                        (rmap (diag {P}{Q}{R}(x ⊗ y)))
                        (R .F-ob (⨂c .F-ob (x , y)) .snd) 
                        (mapout {P}{Q}{R} {!   !} (x ⊗ y)) 
                        (mapoutcoeq {P}{Q}{R}{!   !} ((x ⊗ y))) 
                        {! (idTrans Q) .N-ob (⨂c .F-ob (x , y))  !} 
                        {!   !})) 
                        {!   !})) -}
                    --(inc ((x , y) , (? , Px) , Qy))))
{-}
Cubical.HITs.SetCoequalizer.rec 
(R .F-ob (⨂c .F-ob (x , y)) .snd)

(mapout
 (natTrans src.Data.BiDCC.Mod.SepUP.η src.Data.BiDCC.Mod.SepUP.ηcom)
 (⨂c .F-ob (x , y)))

(mapoutcoeq
 (natTrans src.Data.BiDCC.Mod.SepUP.η src.Data.BiDCC.Mod.SepUP.ηcom)
 (⨂c .F-ob (x , y)))

(src.Data.DayConv.unsolved#meta.913 SMC P Q (Q ⊸ R) Q nt
 (idTrans Q) .N-ob (⨂c .F-ob (x , y))

 (inc ((x , y) , (C .id , Px) , Qy)))
≡ nt .N-ob x Px .N-ob y Qy
-}

            UP = ⨂UP {P}{Q}{R}
            maybe : (m n : 𝓥 [ P ⨂ᴰ Q , R ]) → UP .fun m ≡ UP .fun n → m ≡ n 
            maybe m n prf = sym bbb ∙ (cong (λ h → inv UP h) prf ∙ aaa) where 
                aaa : inv UP (fun UP n) ≡ n
                aaa = UP  .leftInv n

                bbb : inv UP (fun UP m) ≡ m
                bbb = UP .leftInv m

            ret : retract ⊸Intro ⊸IntroInv
            ret nt = maybe _ nt (makeNatTransPath {! UP .fun (⊸IntroInv (⊸Intro nt)) .N-ob  !}) where 
                f1 : UP .fun nt .N-ob ≡ fwd nt .N-ob
                f1 = refl

                f2 : UP .fun (⊸IntroInv (⊸Intro nt)) .N-ob ≡ fwd (seqTrans {!   !} {!   !}) .N-ob 
                f2 = refl

            ⊸UP : Iso (𝓥 [ P ⨂ᴰ Q , R ]) (𝓥 [ P , Q ⊸ R ]) 
            ⊸UP = iso 
                    ⊸Intro
                    ⊸IntroInv
                    (λ nt → {!   !})
                    {!   !}
                   -- λ nt → maybe _ nt (makeNatTransPath (funExt λ{(x , y) → funExt λ{(Px , Qy) → 
                   --     {! nt .N-ob (⨂c .F-ob (x , y)) (inc ((x , y) , (C .id , Px) , Qy))  !}}}))

                       -- funExt⁻ (sym (uniqueness {!   !} {!   !} {!   !} {!   !} {!   !} {!   !} {!   !})) _))--sym (η≡ {!   !}) ) )

                    {- 
                    rec (R .F-ob x .snd)
(mapout
 (natTrans src.Data.BiDCC.Mod.SepUP.η src.Data.BiDCC.Mod.SepUP.ηcom)
 x)
(mapoutcoeq
 (natTrans src.Data.BiDCC.Mod.SepUP.η src.Data.BiDCC.Mod.SepUP.ηcom)
 x)
(src.Data.DayConv.unsolved#meta.913 SMC P Q (Q ⊸ R) Q
 (natTrans
  (λ x₁ Px →
     natTrans
     (λ y Qy →
        nt .N-ob (⨂c .F-ob (x₁ , y)) (inc ((x₁ , y) , (C .id , Px) , Qy)))
     (λ {y} {z} z→y i x₂ →
        hcomp
        (doubleComp-faces
         (λ _ →
            nt .N-ob (⨂c .F-ob (x₁ , z))
            (inc ((x₁ , z) , (C .id , Px) , Q .F-hom z→y x₂)))
         (λ i₁ →
            nt .N-hom (⨂c .F-hom (id , z→y)) i₁
            (inc ((x₁ , y) , (C .id , Px) , x₂)))
         i)
        (nt .N-ob (⨂c .F-ob (x₁ , z))
         (hcomp
          (doubleComp-faces
           (λ _ → inc ((x₁ , z) , (C .id , Px) , Q .F-hom z→y x₂))
           (λ i₁ →
              hcomp
              (doubleComp-faces
               (λ _ → inc ((x₁ , y) , (⨂c .F-hom (C .id , z→y) ⋆ id , Px) , x₂))
               (λ i₂ →
                  hcomp
                  (doubleComp-faces
                   (λ _ →
                      inc
                      ((x₁ , y) ,
                       (C .id ⋆ ⨂c .F-hom (C .id , z→y) , F-hom P id Px) , F-hom Q id x₂))
                   (λ i₃ →
                      inc
                      ((x₁ , z) ,
                       (hcomp
                        (doubleComp-faces (λ _ → C .id ⋆ F-hom ⨂c (id , id)) (⋆IdR (C .id))
                         i₃)
                        (C .id ⋆ ⨂c .F-id i₃)
                        , F-hom P (C .id) Px)
                       , F-hom Q z→y x₂))
                   i₂)
                  (coeq ((x₁ , y) , (x₁ , z) , (C .id , z→y) , (C .id , Px) , x₂)
                   i₂))
               (~ i₁))
              (inc
               ((x₁ , y) ,
                (hcomp
                 (doubleComp-faces (λ _ → ⨂c .F-hom (C .id , z→y) ⋆ id)
                  (λ i₂ → C .⋆IdL (⨂c .F-hom (C .id , z→y)) (~ i₂)) (~ i₁))
                 (C .⋆IdR (⨂c .F-hom (C .id , z→y)) (~ i₁))
                 , P .F-id i₁ Px)
                , Q .F-id i₁ x₂)))
           i)
          (inc ((x₁ , z) , (C .id , P .F-id (~ i) Px) , Q .F-hom z→y x₂))))))
  (λ {x = x₁} {y} y→x i x₂ →
     makeNatTransPath
     (λ i₁ x₃ x₄ →
        hcomp
        (doubleComp-faces
         (λ _ →
            nt .N-ob (⨂c .F-ob (y , x₃))
            (inc ((y , x₃) , (C .id , P .F-hom y→x x₂) , x₄)))
         (λ i₂ →
            nt .N-hom (⨂c .F-hom (y→x , C .id)) i₂
            (inc ((x₁ , x₃) , (C .id , x₂) , x₄)))
         i₁)
        (nt .N-ob (⨂c .F-ob (y , x₃))
         (hcomp
          (doubleComp-faces
           (λ _ → inc ((y , x₃) , (C .id , P .F-hom y→x x₂) , x₄))
           (λ i₂ →
              hcomp
              (doubleComp-faces
               (λ _ →
                  inc ((y , x₃) , (C .id , P .F-hom y→x x₂) , Q .F-hom (C .id) x₄))
               (λ i₃ →
                  inc
                  ((x₁ , x₃) , (C .⋆IdR (⨂c .F-hom (y→x , C .id)) (~ i₃) , x₂) , x₄))
               i₂)
              (hcomp
               (doubleComp-faces
                (λ _ → inc ((x₁ , x₃) , (⨂c .F-hom (y→x , C .id) , x₂) , x₄))
                (λ i₃ →
                   hcomp
                   (doubleComp-faces
                    (λ _ →
                       inc
                       ((x₁ , x₃) ,
                        (C .id ⋆ ⨂c .F-hom (y→x , C .id) , F-hom P id x₂) , F-hom Q id x₄))
                    (λ i₄ →
                       inc
                       ((y , x₃) ,
                        (hcomp
                         (doubleComp-faces (λ _ → C .id ⋆ F-hom ⨂c (id , id)) (⋆IdR (C .id))
                          i₄)
                         (C .id ⋆ ⨂c .F-id i₄)
                         , F-hom P y→x x₂)
                        , F-hom Q (C .id) x₄))
                    i₃)
                   (coeq ((x₁ , x₃) , (y , x₃) , (y→x , C .id) , (C .id , x₂) , x₄)
                    i₃))
                (~ i₂))
               (inc
                ((x₁ , x₃) ,
                 (C .⋆IdL (⨂c .F-hom (y→x , C .id)) i₂ , P .F-id i₂ x₂) ,
                 Q .F-id i₂ x₄))))
           i₁)
          (inc ((y , x₃) , (C .id , P .F-hom y→x x₂) , Q .F-id (~ i₁) x₄)))))
     i))
 (idTrans Q) .N-ob x p)
                    -}

                       -- funExt⁻ (sym (uniqueness {!   !} {!   !} {!   !} {!   !} {!   !} {!   !} {!   !})) _))--sym (η≡ {!   !}) ) )
                    -- sym (η≡ {!   !} )) ) 