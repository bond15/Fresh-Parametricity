{-# OPTIONS --allow-unsolved-metas #-}
module src.Data.Concrete where 
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
    open import Cubical.HITs.SetCoequalizer  hiding(rec )
    open import src.Data.Coend
    open import Cubical.Categories.Constructions.BinProduct renaming (_×C_ to _B×C_)
    open import src.Data.PresheafCCC
    open import Cubical.Categories.Yoneda.More
    open import Cubical.Foundations.Function
    open import Cubical.Data.Sigma 
    open import Cubical.Categories.Instances.Discrete
    open import Cubical.Categories.Displayed.Constructions.Comma
    open import Cubical.Categories.Instances.Terminal
    open import Cubical.Data.FinSet.Base
    
    module _ {ℓ ℓ' : Level} where
        
        ℓm = (ℓ-max ℓ ℓ')
        open Category
        open Functor
        open NatTrans
        open import src.Data.FinSet
        module Worlds where 
            
            data SynTy' : Type ℓ where 
                u n b : SynTy'

            SynTyisSet : isSet SynTy' 
            SynTyisSet = {!  !}

            SynTy : hSet ℓ
            SynTy = SynTy' , SynTyisSet

            Inc : Functor (FinSetMono{ℓ}) (SET ℓ)
            Inc .F-ob (ty , fin) = ty , isFinSet→isSet fin 
            Inc .F-hom (f , _) x = f x
            Inc .F-id = refl
            Inc .F-seq (f , _) (g , _) = refl
            
            G : Functor (TerminalCategory {ℓ}) ((SET ℓ))
            G = FunctorFromTerminal SynTy

            -- this variance is used for the semicartisian day conv
            -- this is essentially a slice category but the Identity functor is replaced with an inclusion functor
            -- so that we have the top maps of the slice homs as injective functions
            W : Category (ℓ-suc ℓ) ℓ
            W = (Comma Inc G) ^op
        
        open Worlds

        open import Cubical.Data.Empty hiding (rec)
        open import Cubical.Data.SumFin.Base 
        open import Cubical.Data.Unit
        open import Cubical.Data.FinSet.Constructors
        open import Cubical.Data.Sum.Base
        open import Cubical.HITs.PropositionalTruncation hiding(rec ; map)
        open import Cubical.Functions.Embedding
        -- Monoid on Worlds
        
        emptyFin* : isFinSet {ℓ} (Lift ⊥)
        emptyFin* = 0 , ∣ (λ()) , record { equiv-proof = λ() } ∣₁

        emptymap : ob W 
        emptymap = ((Lift (Fin 0 ) , emptyFin*) , tt*) , λ() 

        FSM = FinSetMono {ℓ}

        ⊎FSM : ob FSM → ob FSM → ob FSM 
        ⊎FSM (X , Xfin) (Y , Yfin) = (X ⊎ Y) , (isFinSet⊎ ((X , Xfin)) (Y , Yfin))


        ≡Wmor : {w₁ w₂ : ob W} → {f g : W [ w₁ , w₂ ]} → f .fst .fst ≡ g .fst .fst → f ≡ g 
        ≡Wmor {w₁} {w₂} {f} {g} prf = ΣPathP ((≡-× prf refl) , λ i → funExt λ x  → {!   !})
        --i = ((prf i) , refl) , funExt λ x → {!  !}
            --Σ≡Prop (λ x → {! W .isSetHom  !}) {!   !}
            -- ΣPathP (prf , {! Σ≡Prop ? ? !})
            --ΣPathP ({! f  !} , {!  ΣPathP ? !})

        mapemb : {X X' Y Y' : ob FSM} → FSM [ X , Y ] → FSM [ X' , Y' ] → FSM [ ⊎FSM X X' , ⊎FSM Y Y' ]
        mapemb {X}{X'}{Y}{Y'}(f , femb) (g , gemb) = map f g , goal where 

            goal : isEmbedding (map f g) 
            goal = injEmbedding (isFinSet→isSet (⊎FSM Y Y' .snd)) {! isEmbedding→Injection inl ? {f} {f}  !}
            --injEmbedding (isFinSet→isSet (⊎FSM Y Y' .snd)) {!   !} where 
           -- goal : {w x : fst (⊎FSM X X')} → map f g w ≡ map f g x → w ≡ x
           -- goal = {!   !}
            
            {-goal {inl wl} {inl xl} = {! isEmbedding→Injection inl !}
            goal {inl wl} {inr xr} = {!   !}
            goal {inr wr} {inl xl} = {!   !}
            goal {inr wr} {inr xr} = {!   !} -}

        ⊗W : Functor (W B×C W) W
        ⊗W .F-ob (((X , tt* ) , w) , ((Y , tt* ) , w')) = 
            (⊎FSM X Y , tt*) , rec w w'
        ⊗W .F-hom {X}{Y}(((f , _), Δ₁) , ((g , _), Δ₂)) = 
            ( mapemb f g , refl) , funExt λ {(inl x) → funExt⁻ Δ₁ x
                                           ; (inr x) → funExt⁻ Δ₂ x} 
        ⊗W .F-id = {!   !} --≡Wmor {!   !}
            -- Σ≡Prop  (λ x → {! FinSetMono .isSetHom !}) {!   !}
        ⊗W .F-seq = {!  isSetHom !}

        _⊎w_ : ob W → ob W → ob W 
        w1 ⊎w w2 = ⊗W .F-ob (w1 , w2)
        
        SMC : StrictMonCategory (ℓ-suc ℓ) ℓ 
        SMC = record { C = W ; sms = 
            record { tenstr = 
                record { 
                    ─⊗─ = ⊗W ; 
                    unit = emptymap } ; 
                    assoc = {!   !} ; 
                    idl = {!   !} ;   
                    idr = {!   !} } } 

        -- now that we have a concrete category W for C and its monoidal structure..
        -- we can get its BiDCC structure and the CPBV scafolding
        open import src.Data.BCBPV
        module M = Mod SMC
       -- open Mod SMC
        open import src.Data.BiDCC 
        module N = src.Data.BiDCC.Mod SMC
        open M 
        open N

        inlemb' : {(A , _) (B , _) : ob FSM} → isEmbedding (inl {ℓ}{ℓ}{A}{B})
        inlemb' {A}{B} = injEmbedding (isFinSet→isSet ((⊎FSM A B .snd))) λ{ {x} → (cong (λ{ (inl x) → x
                                                                                          ; (inr _) → x}))}

        inremb' : {(A , _) (B , _) : ob FSM} → isEmbedding (inr {ℓ}{ℓ}{A}{B})
        inremb' {A}{B} = injEmbedding (isFinSet→isSet ((⊎FSM A B .snd))) λ{ {x} → (cong (λ{ (inl _) → x
                                                                                          ; (inr y) → y}))}

        inlemb : {ℓ : Level}{A B : Type ℓ} → isEmbedding (inl {ℓ}{ℓ}{A}{B})
        inlemb = {!   !}

        inremb : {ℓ : Level}{A B : Type ℓ} → isEmbedding (inr {ℓ}{ℓ}{A}{B})
        inremb = {!   !}
        
        module firstIssue {P Q : ob 𝓥}{R : ob 𝓒} where 
            open import src.Data.Direct2 
            open Ran W {!   !} hiding (Inc* ; Inc)
            open End renaming (fun to end)
            -- first issue
            eval :  𝓥× [ (U .F-ob (sep Q R)) ⨂Ext Q , U .F-ob R ∘F (⊗W ^opF) ] 
            eval  .N-ob (x , y) (UQ→Rx , Qy) .end z z←x⊗y = goal where 
                -- implement the other hack where you can lift both to z⊗z and arbitrarily restrict back to z

                z⊗z←z : W [ ⊗W .F-ob (z , z) , z ] 
                z⊗z←z = ((inl , inlemb' {z .fst .fst}{z .fst .fst}) , refl) , refl

                z←x : W [ z , x ]
                z←x = z←x⊗y ⋆⟨ W ⟩ (((inl , inlemb' {x .fst .fst}{y .fst .fst}) , refl) , refl)

                z←y : W [ z , y ]
                z←y = z←x⊗y ⋆⟨ W ⟩ (((inr , inremb' {x .fst .fst}{y .fst .fst}) , refl) , refl)

                goal : R .F-ob z .fst 
                goal = R .F-hom z⊗z←z (UQ→Rx .end z z←x z ( Q .F-hom z←y Qy ))

            
            {- you can partition z and define maps... but will you be able to prove naturality? 
                hard to implement

                -- can't give the empty map as w because W [ Ø , _ ] is uninhabited
                -- can't give the empty map as v because 
                have' : (w : ob W) → (m : W [ w , x ]) → (v : ob W) → Q .F-ob v .fst → R .F-ob (⊗W .F-ob (w , v)) .fst
                have' = UQ→Rx .end

                postulate z_missed : ob W 
                postulate z_x z_y : ob W
                z_hit : ob W 
                z_hit = ⊗W .F-ob (z_x , z_y)

                postulate zeq : z ≡ ⊗W .F-ob (z_hit , z_missed)
                
                z_y+ : ob W 
                z_y+ = ⊗W .F-ob (z_y , z_missed)

                --alternatively
                postulate zeq' : z ≡ ⊗W .F-ob (z_x , z_y+)

                postulate ylift : W [ z_y+ , y ]

                postulate z_x_map : W [ z_x , x ]

                q' : Q .F-ob z_y+ .fst 
                q' = Q .F-hom ylift Qy

                eqR : R .F-ob z .fst ≡ R .F-ob (⊗W .F-ob (z_x , z_y+)) .fst
                eqR = cong (λ h → R .F-ob h .fst) zeq'
                
                -- this is not symmetric..
                -- arbitrary choice in deciding to "expand y" vs "expand x"
                goal : R .F-ob z .fst
                goal = transport (sym eqR) (have' z_x z_x_map z_y+ q')
                
                have : R .F-ob (⊗W .F-ob (x , y)) .fst 
                have = UQ→Rx .end x (W .id) y Qy



                _ = {! R .F-hom  !}

                cantuse : SET {!   !} [ F-ob R z , F-ob R ((⊗W ^opF) ⟅ x , y ⟆) ]
                cantuse = R .F-hom z→x⊗y

            -}
                
            eval .N-hom {x}{y} f = funExt {!   !}

        module secondIssue where 
            --other issue 
            -- now lets try to show the tensor universal property for oblique morphisms 
            -- using what we know about our concrete category W


            frwd :{P Q : ob 𝓥}{R : ob 𝓒} → 𝓞[ P ⨂ᴰ Q , R ] → 𝓞× P Q R 
            frwd {P}{Q}{R} o x y (Px , Qy) = o (⊗W .F-ob (x , y)) (inc ((x , y) , (((W .id) , Px) , Qy)))

            open UniversalProperty
            bkwrd : {P Q : ob 𝓥}{R : ob 𝓒} → 𝓞× P Q R → 𝓞[ P ⨂ᴰ Q , R ] 
            bkwrd {P}{Q}{R} o x = 
                inducedHom 
                    (R .F-ob x .snd) 
                    underlying
                    {!   !} where 
                open DayUP

                Diag' : (x : ob W) → Set (ℓ-suc ℓ)
                Diag' x = Σ[ (y , z) ∈ (ob W × ob W)] (fst (diagram {MC = SMC} P Q x ⟅ (y , z) , (y , z) ⟆b))
                
            
                underlying : Diag' x → R .F-ob x .fst 
                underlying ((y , z) , (x←y⊗z , Py) , Qz) = goal where 

                    -- x can be partitioned into 3 parts
                    -- x_y for the parts of x←y⊗z that hit x from y
                    -- x_z for the parts of x←y⊗z that hit x from z
                    -- x_miss for the parts of x which are not mapped to
                    postulate x_y x_z x_miss : ob W
                    postulate split : ( x_y ⊎w (x_z ⊎w x_miss)) ≡ x
                    -- map x←y⊗z can be split into maps
                    postulate x_y←y : W [ x_y , y ]
                    postulate x_z←z : W [ x_z , z ]
                    postulate x←sub : W [ x , ⊗W .F-ob (x_y , x_z )]
                    postulate total←hit : W [ ( x_y ⊎w (x_z ⊎w x_miss)) , ( x_y ⊎w x_z ) ]

                    Px_y : P .F-ob x_y .fst
                    Px_y = P .F-hom x_y←y Py

                    Qx_z : Q .F-ob x_z .fst 
                    Qx_z = Q .F-hom x_z←z Qz
                    
                    R' : R .F-ob (⊗W .F-ob (x_y , x_z)) .fst 
                    R' = o x_y x_z (Px_y , Qx_z)
                    
                    goal' : R .F-ob ( x_y ⊎w (x_z ⊎w x_miss)) .fst 
                    goal' = {! R .F-hom total←hit ?  !}
                    _ = {!  !}

                    have : R .F-ob (⊗W .F-ob (y , z)) .fst
                    have = o y z (Py , Qz)

                    y⊗z←z : W [ ⊗W .F-ob (y , z) , z ]
                    y⊗z←z = ((inr , inremb) , refl) , refl

                    y⊗z←y : W [ ⊗W .F-ob (y , z) , y ]
                    y⊗z←y = ((inl , inlemb) , refl) , refl

                    x←y : W [ x , y ]
                    x←y = x←y⊗z ⋆⟨ W ⟩ y⊗z←y

                    x←z : W [ x , z ]
                    x←z = x←y⊗z ⋆⟨ W ⟩ y⊗z←z

                    Px : P .F-ob x .fst 
                    Px = P .F-hom x←y Py

                    Qx : Q .F-ob x .fst 
                    Qx = Q .F-hom x←z Qz

                    -- ARBITRARY
                    x⊗x←x : W [ ⊗W .F-ob (x , x) , x ]
                    x⊗x←x = ((inl , inlemb) , refl) , refl

                    alsohave : R .F-ob (⊗W .F-ob (x , x)) .fst
                    alsohave = o x x (Px , Qx)

                    goal : R .F-ob x .fst 
                    goal = R .F-hom x⊗x←x alsohave

            ⨂UP𝓞 : {P Q : ob 𝓥}{R : ob 𝓒} → Iso 𝓞[ P ⨂ᴰ Q , R ] (𝓞× P Q R) 
            ⨂UP𝓞 {P}{Q}{R} = 
                iso 
                    frwd 
                    bkwrd 
                    {!   !} 
                    {!   !}
                     