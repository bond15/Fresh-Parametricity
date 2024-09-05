{-# OPTIONS --allow-unsolved-metas #-}
module src.Data.ConcreteFin where 
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
        open import src.Data.Semicartesian


        open Monoidal
        open import src.Data.BCBPV
        opmon : StrictMonCategory (ℓ-suc ℓ') ℓ' 
        opmon = SMC ^opMon
        open src.Data.BCBPV.Mod {ℓ-suc ℓ'} {ℓ'}opmon isGroupoidFinSet
        open import src.Data.BiDCC 
        open src.Data.BiDCC.Mod {ℓ-suc ℓ'} {ℓ'}opmon



        module _ {P Q : ob 𝓥}{R : ob 𝓒} where

            open import Cubical.Data.Sum
            C = StrictMonCategory.C {ℓ-suc ℓ'} {ℓ'} opmon
            ⊗C = StrictMonCategory.sms opmon .StrictMonStr.tenstr .TensorStr.─⊗─ 
            Cunit = StrictMonCategory.sms opmon .StrictMonStr.tenstr .TensorStr.unit
            idr = StrictMonCategory.sms opmon .StrictMonStr.idr
            𝓥unit = I⨂ opmon

            private 
                open import Cubical.Data.Unit
                testF : (A : ob 𝓥) → 𝓒 [ Constant _ _ (Unit* , isSetUnit*) , F .F-ob A ]
                testF A .N-ob x tt* = y , f , {!   !} where
                    postulate y : ob (FinSetMono {_})
                    f : (C ^op) [ x , y ]
                    f = {!   !} , {!   !}
                    
                testF A .N-hom f = {!   !}

            lemma : {x : ob C} → R .F-ob (⊗C .F-ob (x , Cunit)) .fst ≡ R .F-ob x .fst 
            lemma = cong (λ h → R .F-ob h .fst) (idr _)

            test1 : CatIso 𝓒 (sep 𝓥unit R) R 
            test1 = (natTrans (λ x sepIR → R .F-hom (inl , isEmbedding-inl) (sepIR Cunit (lift (C .id))) ) {!   !}),
            --transport lemma (sepIR Cunit (lift (C .id)) )) {!   !}) , 
                                                                -- Issue, needs map x ⊎ y → x
                                                                -- we could construct if we were given y→Ø instead..
                                                                -- but y→Ø should never be inhabited!
                                                                -- except when y ≡ Ø ?
                        (isiso (natTrans (λ x Rx y Ø→y → R .F-hom {! ⊗C .F-hom ((C .id) , Ø→y) !} Rx) {! Ø→y  !}) {!   !} {!   !})

            open import Cubical.Data.Unit
            ×unit : ob 𝓥 
            ×unit = Constant _ _ (Unit* , isSetUnit*)

            example : CatIso 𝓒 (fun ×unit R) R 
            example = (natTrans (λ x tt→Rx → tt→Rx tt*) λ _ → refl) , 
                     isiso (natTrans (λ{x Rx tt* → Rx}) λ _ → refl) 
                     (makeNatTransPath refl) (makeNatTransPath refl) 


            
            open import src.Data.Direct2 
            open Ran C isGroupoidFinSet hiding (Inc* ; Inc)
            open End renaming (fun to end)
            open DayUP
            open Iso renaming (fun to ifun)
            open import Cubical.Categories.Monad.Base
            open IsMonad (M .snd) renaming (η to ret)

            -- FS = C ^op

            module Projection where 
                ⊗str' : {P Q : ob 𝓥}  → 𝓥× [ P ⨂Ext T .F-ob Q , T .F-ob (P ⨂ᴰ Q) ∘F (⊗C ^opF) ] 
                ⊗str' {P}{Q}.N-ob (x , y) (Px , TQy) .end z x⊗y→z = goal where 

                    j : FS [ x , z ]
                    j = (inl , isEmbedding-inl) ⋆⟨ FS ⟩ x⊗y→z

                    k : FS [ y , z ]
                    k = (inr , isEmbedding-inr) ⋆⟨ FS ⟩ x⊗y→z 

                    zz : FS [ z , ⊗C .F-ob (z , z) ]
                    zz = inl , isEmbedding-inl

                    v : ob FS
                    v = TQy .end z k .fst

                    g : FS [ z , v ]
                    g = TQy .end z k .snd .fst

                    Qv : Q .F-ob v .fst 
                    Qv = TQy .end z k .snd .snd

                    sub : F .F-ob (P ⨂ᴰ Q) .F-ob (⊗C .F-ob (v , v)) .fst 
                    sub = (⊗C .F-ob (v , v)) , ((C .id) , (inc ((v , v) , ((C .id) , (P .F-hom (j ⋆⟨ FS ⟩ g) Px)) , Qv)))

                    goal : F .F-ob (P ⨂ᴰ Q) .F-ob z .fst
                    goal = F .F-ob (P ⨂ᴰ Q) .F-hom (g ⋆⟨ FS ⟩ (inl , isEmbedding-inl)) sub

    {-
                    v : ob FS
                    v = TQy .end z k .fst

                    g : FS [ z , v ]
                    g = TQy .end z k .snd .fst

                    Qv : Q .F-ob v .fst 
                    Qv = TQy .end z k .snd .snd

                    yv : FS [ y , v ]
                    yv = k ⋆⟨ FS ⟩ g 
                    
                    d : (P ⨂ᴰ Q) .F-ob v .fst
                    d = inc ((x , y) , (((x⊗y→z ⋆⟨ FS ⟩ g) , Px) , (Q .F-hom {! yv !} Qv)))

                    option1 : F .F-ob (P ⨂ᴰ Q) .F-ob z .fst
                    option1 = v , (g , d)

                    d' : (P ⨂ᴰ Q) .F-ob z .fst
                    d' = (inc ((x , y) , ((x⊗y→z , Px) , Q .F-hom {!  !} Qv)))

                    option2 : F .F-ob (P ⨂ᴰ Q) .F-ob z .fst
                    option2 = z , ((FS .id) , d')

                    --d3 : (P ⨂ᴰ Q) .F-ob (⊗C .F-ob (z , z)) .fst
                    --d3 = (inc ((x , y) , ((⊗C .F-hom (j , k) , Px) , {!   !})))
                    
                    d3 : (P ⨂ᴰ Q) .F-ob (⊗C .F-ob (v , v)) .fst
                    d3 = (inc ((v , v) , ((⊗C .F-hom ((C .id) , (C .id)) , P .F-hom (j ⋆⟨ FS ⟩ g) Px) , Qv)))

                    option3' : F .F-ob (P ⨂ᴰ Q) .F-ob (⊗C .F-ob (v , v)) .fst
                    option3' = (⊗C .F-ob (v , v)) , (C .id , d3)

                    option3 : F .F-ob (P ⨂ᴰ Q) .F-ob z .fst
                    option3 = F .F-ob (P ⨂ᴰ Q) .F-hom (g ⋆⟨ FS ⟩ (inl , isEmbedding-inl)) option3'
    -}

                ⊗str' .N-hom {(x , x')}{(y , y')} (x→y , x'→y') = funExt λ{(Px , TQx') → {!   !}}
                
                ⊗str : {P Q : ob 𝓥} → 𝓥 [ P ⨂ᴰ T .F-ob Q , T .F-ob (P ⨂ᴰ Q) ] 
                ⊗str {P} {Q} = ⨂UP .inv ⊗str' 

            module Partition where 
                ⊗str''' : {P Q : ob 𝓥}  → 𝓥× [ P ⨂Ext Q , T .F-ob (P ⨂ᴰ Q) ∘F (⊗C ^opF) ] 
                ⊗str''' {P}{Q}.N-ob (x , y) (Px , Qy) .end z x⊗y→z = goal where 

                    TQy : T .F-ob Q .F-ob y .fst
                    TQy = ret .N-ob Q .N-ob y Qy

                    -- don't want z as codomain.
                    -- want a partition of z
                    _ : (x .fst → z .fst) × (y .fst → z .fst)
                    _ = Π⊎Iso .ifun  (x⊗y→z .fst)

                    postulate zx zy zm : ob FS
                    postulate hx : FS [ x , zx ]
                    postulate hy : FS [ y , zy ]

                    p' : P .F-ob zx .fst 
                    p' = P .F-hom hx Px

                    zy' : ob FS 
                    zy' = ⊗C .F-ob (zy , zm)

                    postulate fact1 : z ≡ ⊗C .F-ob (zx , zy')

                    _ : TQy .end zy hy .fst ≡ zy
                    _ = refl

                    _ : TQy .end zy hy .snd .fst ≡ FS .id
                    _ = refl

                    q' : Q .F-ob zy .fst
                    q' = TQy .end zy hy .snd .snd

                    _ : q' ≡ Q .F-hom hy Qy
                    _ = refl

                    n : FS [ ⊗C .F-ob (zx , zy') , z ] -- identity
                    n = {!  !}
                    

                    goal : (Inc* ⟅ F ⟅ P ⨂ᴰ Q ⟆ ⟆) .F-ob z .fst
                    goal = z , (FS .id) , inc ((zx , zy') , ((n , p') , Q .F-hom (inl , isEmbedding-inl) q'))
                    
                ⊗str''' {P}{Q}.N-hom {(x , y)}{(z' , y')}(f , g) = funExt λ {(Px , Qy) → {!  !}}
                
                {-# TERMINATING #-}
                ⊗str' : {P Q : ob 𝓥}  → 𝓥× [ P ⨂Ext T .F-ob Q , T .F-ob (P ⨂ᴰ Q) ∘F (⊗C ^opF) ] 
                ⊗str' {P}{Q}.N-ob (x , y) (Px , TQy) .end z x⊗y→z = goal where 

                    postulate zx zy zm : ob C
                    postulate fact1 : z ≡ ⊗C .F-ob ((⊗C .F-ob (zx , zy)) , zm) 
                    postulate hx : FS [ x , zx ]
                    postulate hy : FS [ y , zy ]

                    h : FS [ (⊗C .F-ob (x , y)) , z ]
                    h = x⊗y→z

                    v : ob FS 
                    v = TQy .end zy hy .fst

                    g : FS [ zy , v ]
                    g = TQy .end zy hy .snd .fst

                    q' : Q .F-ob v .fst 
                    q' = TQy .end zy hy .snd .snd

                    p' : P .F-ob zx .fst 
                    p' = P .F-hom hx Px

                    zy'  = ⊗C .F-ob (v , zm)
                    n = ⊗C .F-ob (zx , zy')

                    -- zx ⊎ zy ⊎ zm --> zx ⊎ v ⊎ zm via id ⊎ g ⊎ id
                    m : FS [ z , n ]
                    m = {!   !} , {!   !}
                    
                    goal : F .F-ob (P ⨂ᴰ Q) .F-ob z .fst
                    goal = n , m , inc ((zx , zy') , ((FS .id , p') , Q .F-hom ((inl , isEmbedding-inl)) q'))  
                        --z , (FS .id , inc ((zx , v) , (({!   !} , p') , q'))) 
                        
                        {-F .F-ob (P ⨂ᴰ Q) .F-hom 
                            m 
                            (n , (FS .id , 
                                (inc ((⊗C .F-ob (zx , zm) , v) , ((FS .id , P .F-hom (hx ⋆⟨ FS ⟩ (inl , isEmbedding-inl)) Px) , q'))))) 
                        -}


                        --(⊗C .F-ob (⊗C .F-ob (zx , zm), v )) , m , 
                        -- inc (((⊗C .F-ob (zx , zm)) , v) , (((FS .id) , P .F-hom (hx ⋆⟨ FS ⟩ (inl , isEmbedding-inl)) Px) , q'))

                ⊗str' .N-hom {(x , y)}{(x' , y')} (x→y , x'→y') =
                    funExt λ {(Px , TQy) → 
                        end≡ _ (λ z x'⊗y'→z → 
                            ΣPathP ({!  refl !} , 
                                ΣPathP ( {!   !}   , 
                                    {!   !}   )  )  )}    
                
                ⊗str : {P Q : ob 𝓥} → 𝓥 [ P ⨂ᴰ T .F-ob Q , T .F-ob (P ⨂ᴰ Q) ] 
                ⊗str {P} {Q} = ⨂UP .inv ⊗str' 

            module Desired where 
                ⊗str' : {P Q : ob 𝓥}  → 𝓥× [ P ⨂Ext T .F-ob Q , T .F-ob (P ⨂ᴰ Q) ∘F (⊗C ^opF) ] 
                ⊗str' {P}{Q}.N-ob (x , y) (Px , TQy) .end z x⊗y→z = goal where 

                    h : FS [ (⊗C .F-ob (x , y)) , z ]
                    h = x⊗y→z

                    v : ob FS 
                    v = TQy .end y (FS .id) .fst

                    g : FS [ y , v ]
                    g = TQy .end y (FS .id) .snd .fst

                    postulate g' : FS [ v , y ]

                    q' : Q .F-ob v .fst 
                    q' = TQy .end y (FS .id) .snd .snd

                    goal : F .F-ob (P ⨂ᴰ Q) .F-ob z .fst
                    goal = z , (FS .id , inc ((x , y) , (x⊗y→z , Px) , Q .F-hom g' q'))
                    
                ⊗str' .N-hom {(x , x')}{(y , y')} (x→y , x'→y') = {!   !}
                
                ⊗str : {P Q : ob 𝓥} → 𝓥 [ P ⨂ᴰ T .F-ob Q , T .F-ob (P ⨂ᴰ Q) ] 
                ⊗str {P} {Q} = ⨂UP .inv ⊗str'

            --open Projection
            open Partition
            --open Desired


            str⊗Unitor : CatIso 𝓥 (𝓥unit ⨂ᴰ T .F-ob P) (T .F-ob (𝓥unit ⨂ᴰ P)) 
            str⊗Unitor = ⊗str , isiso b {!   !} {!   !} where

                b : 𝓥 [ T .F-ob (𝓥unit ⨂ᴰ P) , 𝓥unit ⨂ᴰ T .F-ob P ] 
                b .N-ob x e = inc (({! e .end x (C .id)  !} , {!   !}) , (({!  !} , {!   !}) , {!   !})) where 
                    y : ob FS 
                    y = e .end x (C .id) .fst

                    x→y : FS [ x , y ]
                    x→y = e .end x (C .id) .snd .fst

                    Py : (𝓥unit ⨂ᴰ P) .F-ob y .fst 
                    Py = e .end x (C .id) .snd .snd

                b .N-hom = {!   !}

            ⨂map' : {X Y W Z : ob 𝓥} → 𝓥 [ X , W ] → 𝓥 [ Y , Z ] → 𝓥× [ X ⨂Ext Y , (W  ⨂ᴰ Z) ∘F (⊗C ^opF) ]
            ⨂map' {X}{Y}{W}{Z} n m .N-ob (x , y) (Xx , Yy) = inc (((x , y)) , (C .id , n .N-ob x Xx) , m .N-ob y Yy)
            ⨂map' {X}{Y}{W}{Z} n m .N-hom (f , g) = funExt λ x → {!   !}

            ⨂map : {A B C D : ob 𝓥} → 𝓥 [ A , C ] → 𝓥 [ B , D ] → 𝓥 [ A ⨂ᴰ B , C  ⨂ᴰ D ]
            ⨂map {A}{B}{C}{D} n m = ⨂UP .inv (⨂map' n m) 
            -- Day-Functor opmon .F-hom ((𝓥 .id) , (ret {B})) 

            open UniversalProperty
            strUnit : {A B : ob 𝓥} → (⨂map (𝓥 .id) (ret .N-ob B)) ⋆⟨ 𝓥 ⟩ ⊗str {A} {B} ≡ ret .N-ob (A ⨂ᴰ B)
            strUnit {A} {B} = {!   !}
               -- ⨂≡map (makeNatTransPath 
               --     (funExt λ{(x , y) → funExt λ{(Ax , By)→ 
                --        end≡ _ λ z x⊗y→z  → ΣPathP (refl , (ΣPathP (refl , {!   !})))}}))
                --makeNatTransPath (funExt λ z → {!   !})
            --sym (η≡ {!   !}))
                {-}
                ⨂≡map (makeNatTransPath 
                    (funExt λ{(x , y) → funExt λ{(Ax , By)→ 
                        end≡ _ λ z x⊗y→z  → 
                            -- RHS (z , FS .id , A⨂B(x⊗y→z)(inc (x , y) (id , Ax , By)))?
                            -- Projection 
                            -- first components are not equal
                            -- z ⊎ z != z
                            
                            -- Partition
                            -- first and second components are equal
                            -- (zx ⊎ zm) ⊎ v = z

                            -- Desired
                            -- first and second components are equal
                            -- B(g')(q') = By ... unclear..
                            -- dayfact {MC = opmon} A B ?
                            --ΣPathP (refl , ΣPathP (refl , day-ap {MC = opmon} A B {!ret .N-ob (A ⨂ᴰ B)   !} refl {!   !})) }}))
            -}

{- seemingly no UP ⨂ for oblique morphisms 

            open UniversalProperty
            open import Cubical.Categories.Constructions.BinProduct

            mapout : (m : 𝓞× P Q R)(x : ob C) → 
                Σ[ X ∈ ob C × ob C ] fst (diagram {MC = opmon} P Q x ⟅ X , X ⟆b) → R .F-ob x .fst
            mapout m x ((y , z) , (y⊗z→x , p) , q) = R .F-hom (inl , isEmbedding-inl) (m x x (p' , q')) where 
                p' : P .F-ob x . fst
                p' = P .F-hom ((inl , isEmbedding-inl) ⋆⟨ C ^op ⟩ y⊗z→x) p

                q' : Q .F-ob x .fst 
                q' = Q .F-hom ((inr , isEmbedding-inr) ⋆⟨ (C ^op) ⟩ y⊗z→x) q

            mapoutcoeq : (m : 𝓞× P Q R)(x : ob C) → 
                (a : Σ[ X ∈ ob C × ob C ] 
                                Σ[ Y ∈ ob C × ob C ]  
                                Σ[ f ∈ (C ×C C)[ Y , X ] ] 
                                fst (diagram {MC = SMC ^opMon} P Q x ⟅ X , Y ⟆b)) 
                →  mapout m x (lmap (diagram {MC = SMC ^opMon} P Q x) a) ≡ mapout m x (rmap (diagram{MC = SMC ^opMon} P Q x) a)
            mapoutcoeq m x ((y , z) , (y' , z') , (y'→y , z'→z) , (x←y'⊗z' , Py) , Qz) = 
                cong (λ h → R .F-hom ((inl , isEmbedding-inl)) (m x x h)) 
                    (≡-× ( (funExt⁻ (sym (P .F-seq _ _)) Py ∙ {!   !}) ∙  funExt⁻ ( (P .F-seq y'→y _)) Py) 
                            {!  rmap (diagram P Q x ) ((y , z) , (y' , z') , (y'→y , z'→z) , (x←y'⊗z' , Py) , Qz)!})

            bkwrd : 𝓞× P Q R → 𝓞[ P ⨂ᴰ Q , R ]
            bkwrd m x = 
                inducedHom 
                    (R .F-ob x .snd) 
                    (mapout m x) 
                    (mapoutcoeq m x)
                    
            frwd : 𝓞[ P ⨂ᴰ Q , R ] → 𝓞× P Q R 
            frwd  o x y (Px , Qy) = o (⊗C .F-ob (x , y)) (inc ((x , y) , (((C .id) , Px) , Qy)))
            
            ⨂UP𝓞 :  Iso 𝓞[ P ⨂ᴰ Q , R ] (𝓞× P Q R) 
            ⨂UP𝓞 = iso 
                    frwd 
                    bkwrd 
                    -- b : 𝓞[ P ⨂ᴰ Q , R ]
                    -- R .F-hom inl (b (x ⊎ y) (x ⊎ y) (P .F-hom (id ; inl) p , Q .F-hom (id , inr q)))
                    -- ≡ b x y (p , q)
                    (λ b → funExt λ x → funExt λ y →  funExt λ{(p , q) → {!   !} }  ) 
                    (λ b → funExt λ x → sym (uniqueness 
                                                (lmap (diagram {MC = SMC ^opMon} P Q x)) 
                                                (rmap (diagram {MC = SMC ^opMon} P Q x))
                                                (R .F-ob x .snd) 
                                                (mapout (frwd b) x)
                                                (mapoutcoeq (frwd b)x) 
                                                (b x) 
                                                {-
                                                R .F-hom inl (b (x ⊎ y) (inc ((x , x), (id , P.F-hom (x←y⊗z ∘ inl) Py), Q .F-hom (x←y⊗z ∘ inr) Qz )))
                                                ≡ 
                                                b x (inc ((y , z) , (x←y⊗z , Py) , Qz))
                                                -}
                                                λ{ ((y , z) , (x←y⊗z , Py) , Qz) → {!  i !}}))

-}         