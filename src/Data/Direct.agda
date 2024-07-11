{-# OPTIONS --allow-unsolved-metas  --lossy-unification #-}

module src.Data.Direct where
    open import Cubical.Foundations.Function
    open import Cubical.Foundations.Prelude
    open import Cubical.Foundations.HLevels hiding (extend)
    open import Cubical.Functions.Embedding
    open import Cubical.Functions.FunExtEquiv

    open import Cubical.Categories.Adjoint
    open import Cubical.Categories.Adjoint.Monad
    open import Cubical.Categories.Bifunctor.Redundant
    open import Cubical.Categories.Category 
    open import Cubical.Categories.Functor
    open import Cubical.Categories.Functors.Constant
    open import Cubical.Categories.Instances.Discrete
    open import Cubical.Categories.Instances.Functors
    open import Cubical.Categories.Instances.Sets 
    open import Cubical.Categories.Monad.Base
    open import Cubical.Categories.NaturalTransformation
    open import Cubical.Categories.Presheaf.Base
    open import Cubical.Categories.Presheaf.Constructions
    
    open import Cubical.Data.Bool 
    open import Cubical.Data.FinSet
    open import Cubical.Data.FinSet.Constructors
    open import Cubical.Data.Nat
    open import Cubical.Data.Sigma
    open import Cubical.Data.Sum
    open import Cubical.Data.Unit

    open import Cubical.HITs.SetQuotients renaming ([_] to q[_])

    open Category hiding (_∘_)
    open Functor        
    open NatTrans

    {-
        This is specialized form of Cubical.Categories.Presheaf.KanExtension
        where the functor F is just inclusion from the discrete catgory
        
        This simiplifies the construction. Notably the end and coend quotients
        trivialize in this setting due to the fact that the only 
        morphisms in a discrete category are the identity morphisms

            However, in Cubical Agda, lift is not so simple
            since the definition of the Discrete category defines 
            Hom to be paths and there are non trivial paths.

            Maybe this can be rectcified using an identity system?

        This construction also makes it easier to compose the mediating category
            (or you could convince Agda that Set^(|W|) and Set^(|W|^op) are the same
            and moreover you have an adjunction between them ...?)
        
    -}

    -- exists future
    module Lan {ℓC ℓC' ℓS : Level} (W : Category ℓC ℓC')(isSetWob : isSet (ob W)) where

        ℓ = (ℓ-max (ℓ-max ℓC ℓC') ℓS)

        |W| : Category ℓC ℓC 
        |W| = (DiscreteCategory (ob W , isSet→isGroupoid isSetWob))
        
        Inc : Functor |W| W
        Inc = DiscFunc λ x → x

        Inc^op : Functor |W| (W ^op)
        Inc^op = DiscFunc λ x → x

        module _ (A : Functor |W| (SET ℓ)) where
            
            module _ (w₁ : ob W) where

                Sig : Type ℓ 
                Sig = Σ[ w₂ ∈ ob W ] Σ[ g ∈ W [ w₁ , w₂ ] ] A .F-ob w₂ .fst

                isSetSig : isSet Sig 
                isSetSig = isSetΣ isSetWob  λ w → isSetΣ (W .isSetHom) λ f → A .F-ob w .snd

                -- trivial quotient?
                module _ {w₂ w₃ : ob W} 
                    (g : W [ w₁ , w₂ ] ) 
                    (f : |W| [ w₂ , w₃ ]) -- w₂ ≡ w₃
                    (a : (A ⟅ w₃ ⟆) .fst) where

                    module _ {ℓD ℓD'}{D : Category ℓD ℓD' } where 
                        hom-path : ∀ {A B A' B'} (p : A ≡ A') (q : B ≡ B') →
                            (D [ A , B ]) ≡ (D [ A' , B' ])
                        hom-path p q = cong₂ (λ a b → D [ a , b ]) p q

                        hom-pathP : ∀ {A B A' B'} (p : A ≡ A') (q : B ≡ B') →
                                    (f : D [ A , B ]) → (f' : D [ A' , B' ]) →
                                    Type ℓD'
                        hom-pathP p q f f' = PathP (λ i → hom-path p q i) f f'

                    hammer  : {w w' : ob W} →  isProp (|W| [ w , w' ])
                    hammer = isSetWob _ _

                    -- these homsets are equal
                    eqhomset : (|W| [ w₂ , w₂ ]) ≡ (|W| [ w₂ , w₃ ])
                    eqhomset = hom-path refl f
                    _ : (w₂ ≡ w₂) ≡ (w₂ ≡ w₃)
                    _ = eqhomset

                    _ : ((w₂ ≡ w₂) ≡ (w₂ ≡ w₃)) ≡ ((w₂ ≡ w₂) ≡ (w₂ ≡ w₃))
                    _ = {! isSetHom |W| {w₂} {w₃} (hom-path refl f)!}

                    

                    _ : isProp (w₂ ≡ w₃)
                    _ = hammer

                    _ = {! isSetHom |W|  !}

                    eqelems : hom-pathP {D = |W|}{A = w₂} refl f (|W| .id) f -- hom-pathP refl f (|W| .id) f 
                    eqelems = isProp→PathP (λ i → hammer) refl f

                    yas : (f g : |W| [ w₂ , w₃ ]) → f ≡ g
                    yas f g = hammer  f g

                    closer : PathP (λ i → |W| [ w₂ , (f i) ]) (|W| .id) f -- |W| .id is refl
                    closer = isProp→PathP (λ i → hammer) refl f

                    eqhom' : W [ Inc ⟅ w₂ ⟆ , Inc ⟅ w₂ ⟆ ] ≡ W [ Inc ⟅ w₂ ⟆ , Inc ⟅ w₃ ⟆ ]
                    eqhom' = hom-path refl f


                    -- every element in this set is equal to refl
                    contr : isContr (|W| [ w₂ , w₂ ])
                    contr = refl , hammer refl 

                    -- all morphisms in |W| [ w , w ] map to via Inc W .id 
                    toId : {w : ob |W|}(f : |W| [ w , w ]) → (Inc ⟪ f ⟫ ) ≡ W .id 
                    toId f = Inc ⟪ f ⟫ ≡⟨ cong (Inc .F-hom) (hammer _ _) ⟩  
                             Inc ⟪ |W| .id ⟫ ≡⟨ Inc .F-id ⟩ 
                             W .id ∎

                    toId' : hom-pathP {D = W}{A = w₂} refl f (W .id ) (Inc ⟪ f ⟫ )
                    toId' = {! hammer {w₂}{(f i)}  !}
                        --toPathP {! toId (transport (sym eqhomset) f) !}


                    contrcong : isContr (|W| [ w₂ , w₂ ]) ≡ isContr (|W| [ w₂ , w₃ ])
                    contrcong = cong isContr eqhomset
                    -- now show this for hom-path refl f


                    eqhomprop : isProp ((|W| [ w₂ , w₂ ]) ≡ (|W| [ w₂ , w₂ ]))
                    eqhomprop = {! J ()  !}
                        -- {! isPropIsProp {A = } !}

                    contrcontr : isContr ((|W| [ w₂ , w₂ ]) ≡ (|W| [ w₂ , w₂ ]))
                    contrcontr = refl , λ y → λ i → {! hammer {w₂} {w₂}  !}

                    
                    contrcontr' : isContr ((|W| [ w₂ , w₂ ]) ≡ (|W| [ w₂ , w₃ ]))
                    contrcontr' = eqhomset , λ y → {!   !}

                    contr' : isContr (|W| [ w₂ , w₃ ])
                    contr' = transport contrcong contr

                    _ = {! J (contr' .snd)  !}

                    _ : |W| .id ≡ f ∙ (sym f)
                    _ = hammer _ _

                    lemma : hom-pathP  {D = W} {A = w₁} refl (sym f) (g ⋆⟨ W ⟩ (Inc ⟪ f ⟫)) g
                        --PathP (λ i → W [ w₁ , Inc ⟅ f i ⟆ ])  g  (g ⋆⟨ W ⟩ (Inc ⟪ f ⟫))
                    lemma = {! (g ⋆⟨ W ⟩ (Inc ⟪ f ⟫)) ≡[ i ]⟨ ? ⟩ ?  !}

                    _ = ({!   !} ≡[ i ]⟨ {!   !} ⟩ {!   !})


                    -- toId
                    lemma₂ : transport (λ z → W [ w₁ , (f (~ z)) ] ) (g ⋆⟨ W ⟩ (Inc ⟪ f ⟫)) ≡ g
                    lemma₂ = transport (λ z → W [ w₁ , (f (~ z)) ] ) (g ⋆⟨ W ⟩ (Inc ⟪ f ⟫)) ≡⟨ {!   !} ⟩ {!   !}

                    lemma₃ : transport (λ i → fst (F-ob A (f (~ i)))) a ≡ (A ⟪ sym f ⟫) a
                    lemma₃ i = {!   !}
                    
                    -- use identity system?
                    -- I'd like a discrete category with refl as the only endomorphism
                    open import Cubical.Data.Sigma
                    postulate triv : (w₃ , (g ⋆⟨ W ⟩ (Inc ⟪ f ⟫)) , a) ≡ (w₂ , g , (A ⟪ sym f ⟫) a)
                    prove : (w₃ , (g ⋆⟨ W ⟩ (Inc ⟪ f ⟫)) , a) ≡ (w₂ , g , (A ⟪ sym f ⟫) a)
                    prove = ΣPathP (sym f , ΣPathP (toPathP lemma₂ , toPathP lemma₃))
            
            -- action on arrows
            mapR : {w₁ w₂ : ob W}(f : (W ^op) [ w₁ , w₂ ]) → Sig w₁ → Sig w₂
            mapR f (w₃ , w₁→w₃ , Aw₃) = w₃ , (f ⋆⟨ W ⟩ w₁→w₃ , Aw₃)

            mapRId : (w₁ : ob W) → mapR (W .id{w₁}) ≡ λ x → x 
            mapRId w₁ = funExt λ { (w₂ , g , a) i → w₂ , (W .⋆IdL g i , a)}
        
        LanOb : Functor |W| (SET ℓ) → Functor (W ^op) (SET _)
        LanOb A .F-ob w₁ .fst = Sig A w₁
        LanOb A .F-ob w₁ .snd = isSetSig A w₁
        LanOb A .F-hom = mapR A
        LanOb A .F-id {x} = mapRId A x
        LanOb A .F-seq f g = funExt λ {(c , h , a) i → c , (W .⋆Assoc g f h i , a) }

        -- action of Lan on arrows in Set^|W| 
        module _ {A B : Functor |W| (SET ℓ) }(nt : A ⇒ B) where 

            mapL : (w : ob W) → Sig A w → Sig B w 
            mapL w (w₂ , f , a ) = w₂ , f , (nt ⟦ w₂ ⟧) a

            mapLR : {w₁ w₂ : ob W}(f : (W ^op) [ w₁ , w₂ ]) → 
                mapL w₂ ∘ mapR A f ≡ mapR B f ∘ mapL w₁ 
            mapLR f = refl

            LanHom : LanOb A ⇒ LanOb B
            LanHom = natTrans mapL mapLR

        Lan : Functor (FUNCTOR |W| (SET ℓ)) (FUNCTOR (W ^op) (SET ℓ))
        Lan .F-ob = LanOb
        Lan .F-hom = LanHom
        Lan .F-id = makeNatTransPath (funExt λ x → refl)
        Lan .F-seq α β = makeNatTransPath (funExt λ x → refl)

        Inc* = precomposeF (SET ℓ) Inc^op
        open UnitCounit

        η : 𝟙⟨ FUNCTOR |W| (SET ℓ) ⟩ ⇒ funcComp Inc* Lan
        η .N-ob A .N-ob c a = c , (W .id) , a
        {-
        (w₂ , W .id , A .F-hom f x) ≡
        (w₁ ,   (W ⋆ transp (λ i → Hom[ W , f i ] w₁) i0 (id W)) (W .id) , x) 
        -}
        η .N-ob A .N-hom {w₁}{w₂} f = funExt λ Aw₁ → 
            w₂ , ((W .id) , (A ⟪ f ⟫) Aw₁) ≡⟨ sym (triv A w₂ (W .id) (sym f) Aw₁ ) ⟩
             (w₁ , seq' W (W .id) (Inc ⟪ (λ i → f (~ i)) ⟫) , Aw₁) ≡⟨ {! ≡[ i ]⟨ [ c' , lem i , a ] ⟩ !} ⟩ {!   !}

        η .N-hom f = makeNatTransPath refl

        ε : funcComp Lan Inc* ⇒ 𝟙⟨ FUNCTOR (W ^op) (SET ℓ) ⟩
        ε .N-ob A .N-ob w₁ (w₂ , w₁→w₂ , a) = (A ⟪ w₁→w₂ ⟫ ) a
        ε .N-ob A .N-hom {w₁} {w₂} w₂→w₁ = funExt λ{(w₃ , w₁→w₃ , a) → funExt⁻ (A .F-seq w₁→w₃ w₂→w₁) a}
        ε .N-hom {A} {B} nt = makeNatTransPath (funExt₂ λ{w₁ (w₂ , w₁→w₂ , a) → sym (funExt⁻ (nt .N-hom w₁→w₂) a) }) 

        -- (w₂ , (W ⋆ w₁→w₂) (W .id) , a) ≡ (w₂ , w₁→w₂ , a)
        Δ₁ : ∀ G → seqTrans (Lan ⟪ η ⟦ G ⟧ ⟫) (ε ⟦ Lan ⟅ G ⟆ ⟧) ≡ idTrans _
        Δ₁ G = makeNatTransPath (funExt₂ λ {w₁ (w₂ , w₁→w₂ , a) → {!  (w₂ , (W ⋆ w₁→w₂) (W .id) , a) ≡ (w₂ , w₁→w₂ , a) !}})
        --    {!  (w₂ , ( w₁→w₂ , a)) !} ≡⟨ {!   !} ⟩ {!   !}})
      
        
        Δ₂ : ∀ H → seqTrans (η ⟦ Inc* ⟅ H ⟆ ⟧) (Inc* ⟪ ε ⟦ H ⟧ ⟫) ≡ idTrans _
        Δ₂ H = makeNatTransPath (funExt λ c → H .F-id)

        adj : Lan ⊣ Inc*
        adj ._⊣_.η = η
        adj ._⊣_.ε = ε
        adj ._⊣_.triangleIdentities .TriangleIdentities.Δ₁ = Δ₁
        adj ._⊣_.triangleIdentities .TriangleIdentities.Δ₂ = Δ₂


    -- forall past
    module Ran {ℓC ℓC' ℓS : Level} (W : Category ℓC ℓC')(isSetWob : isSet (ob W)) where
        ℓ = (ℓ-max (ℓ-max ℓC ℓC') ℓS)
        
        |W| : Category ℓC ℓC 
        |W| = (DiscreteCategory (ob W , isSet→isGroupoid isSetWob))
        
        Inc : Functor |W| W
        Inc = DiscFunc λ x → x

        Inc^op : Functor |W| (W ^op)
        Inc^op = DiscFunc λ x → x

        module _ (A : Functor |W| (SET ℓ)) where 

            record End (w₁ : ob W) : Type ℓ where
                field
                    fun : (w₂ : ob W)(g : W [ w₂ , w₁ ]) → A .F-ob w₂ .fst

           -- coh : {w₁ w₂ w₃ : ob W}(f : |W| [ w₂ , w₃ ])(g : W [ w₂ , w₁ ]) → 
           --     End {!   !} ≡ End {!   !} 
            open End 

            postulate thing : {w w' : ob W}(f : |W| [ w  , w' ]) → PathP (λ i → W [ w , (sym f) i ]) (Inc ⟪ f ⟫) (W .id)
            
            coh : (w₁ w₂ w₃ : ob W)(f : |W| [ w₂ , w₃ ])(g : W [ w₂ , w₁ ])(e : End w₁) → 
                e . fun w₂ ({! Inc ⟪ f ⟫ !} ⋆⟨ W ⟩ g) ≡ {!(A ⟪ f ⟫) ?  !} 
            coh = {!   !}

            isSetEnd : {w : ob W} → isSet (End w)
            isSetEnd = {!   !}

            end≡ : {w₁ : ob W} {x x' : End w₁} → (∀ c g → x .fun c g ≡ x' .fun c g) → x ≡ x'
            end≡ h i .fun c g = h c g i

            --action of End on arrows in W 
            -- post compose f 
            mapR : {w₁ w₂ : ob W} → (f : W [ w₂ , w₁ ]) → End w₁ → End w₂ 
            mapR w₂→w₁ e .fun w₃ w₃→w₂ = e .fun w₃ (w₃→w₂ ⋆⟨ W ⟩ w₂→w₁)

        open End 

        RanOb : Functor |W| (SET ℓ) → Functor (W ^op) (SET _)
        RanOb A .F-ob w₁ .fst = End A w₁
        RanOb A .F-ob w₁ .snd = isSetEnd A
        RanOb A .F-hom = mapR A
        RanOb A .F-id = funExt λ x → end≡ A λ c g → cong (x .fun c) (W .⋆IdR g)
        RanOb A .F-seq h' h = funExt λ x → end≡ A λ c g → cong (x .fun c) (sym (W .⋆Assoc g h h'))

        RanHom : {A B : Functor |W| (SET ℓ)}(nt : A ⇒ B) → (RanOb A) ⇒ (RanOb B)
        RanHom nt = natTrans 
                        (λ w₁ e → record { fun = λ w₂ g → (nt ⟦ w₂ ⟧) (e .fun w₂ g) }) 
                        λ h → funExt λ _ → end≡ _ λ _ _ → refl
                
        Ran : Functor (FUNCTOR |W| (SET ℓ)) (FUNCTOR (W ^op) (SET ℓ))
        Ran .F-ob = RanOb
        Ran .F-hom = RanHom
        Ran .F-id {A} = makeNatTransPath (funExt λ w → refl)
        Ran .F-seq α β = makeNatTransPath (funExt λ w → refl) 

        Inc* = precomposeF (SET ℓ) Inc^op
        open UnitCounit

        η : 𝟙⟨ FUNCTOR (W ^op) (SET ℓ) ⟩ ⇒ (funcComp Ran Inc*)
        η .N-ob A .N-ob w₁ Aw₁ .fun w₂ g = (A ⟪ g ⟫) Aw₁
        η .N-ob A .N-hom {w₁}{w₂} f = funExt λ Aw₁ → end≡ _  λ c g → sym (funExt⁻ (A .F-seq f g) Aw₁)
        η .N-hom α = makeNatTransPath (funExt₂ λ d a → end≡ _ λ c g → sym (funExt⁻ (α .N-hom g) a))

        ε : funcComp Inc* Ran ⇒ 𝟙⟨ FUNCTOR |W| (SET ℓ) ⟩
        ε .N-ob A .N-ob w e = e .fun w (W .id)
        ε .N-ob A .N-hom {w₁}{w₂}f = funExt λ e → cong (e . fun w₂) ((W .⋆IdL _ ∙ sym (W .⋆IdR _))) ∙ {!   !}
        ε .N-hom α = makeNatTransPath refl

        Δ₁ : ∀ G → seqTrans (Inc* ⟪ η ⟦ G ⟧ ⟫) (ε ⟦ Inc* ⟅ G ⟆ ⟧) ≡ idTrans _
        Δ₁ G = makeNatTransPath (funExt₂ λ c a → funExt⁻ (G .F-id) a)

        Δ₂ : ∀ H → seqTrans (η ⟦ Ran ⟅ H ⟆ ⟧) (Ran ⟪ ε ⟦ H ⟧ ⟫) ≡ idTrans _
        Δ₂ H = makeNatTransPath (funExt₂ λ c x → end≡ _ λ c' g → cong (x .fun c') (W .⋆IdL g))

        adj : Inc* ⊣ Ran
        adj ._⊣_.η = η
        adj ._⊣_.ε = ε
        adj ._⊣_.triangleIdentities .TriangleIdentities.Δ₁ = Δ₁
        adj ._⊣_.triangleIdentities .TriangleIdentities.Δ₂ = Δ₂

     