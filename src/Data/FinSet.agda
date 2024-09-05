{-# OPTIONS --allow-unsolved-metas #-}
-- category of finite sets and embeddings
module src.Data.FinSet where
    open import Cubical.Categories.Category        
    open import Cubical.Foundations.HLevels hiding (extend)
    open import Cubical.Functions.Embedding
    open import Cubical.Foundations.Prelude
    open import Cubical.Data.FinSet
    open import Cubical.Data.FinSet.Constructors

    module _ {ℓ : Level} where 
        open Category
        open import Cubical.Data.Sigma
        
        -- TODO: define compositionally using subcategories of Set
        FinSetMono : Category (ℓ-suc ℓ) ℓ 
        ob FinSetMono = FinSet ℓ
        Hom[_,_] FinSetMono (A , _) (B , _) = A ↪ B
        id FinSetMono {x} = id↪ (fst x)
        _⋆_ FinSetMono f g = compEmbedding g f
        ⋆IdL FinSetMono (f , emb) = Σ≡Prop (λ x → isPropIsEmbedding) refl
        ⋆IdR FinSetMono (f , emb) = Σ≡Prop (λ x → isPropIsEmbedding) refl
        ⋆Assoc FinSetMono f g h = Σ≡Prop (λ x → isPropIsEmbedding) refl
        isSetHom FinSetMono {x} {y} = isSetΣ 
                                (isSetΠ λ _ → isFinSet→isSet (snd y)) 
                                (λ t → isProp→isOfHLevelSuc 1 isPropIsEmbedding)

        module Monoidal where 

            open import Cubical.Categories.Monoidal.Base
            open import Cubical.Categories.Constructions.BinProduct
            open import Cubical.Categories.Functor
            open Functor
            open import Cubical.Data.Sum
            open import Cubical.Data.Empty 
            open import Cubical.HITs.PropositionalTruncation hiding(map)

            emptyFin* : isFinSet {ℓ} (Lift ⊥)
            emptyFin* = 0 , ∣ (λ()) , record { equiv-proof = λ() } ∣₁
            
            Ø : FinSet ℓ 
            Ø = (Lift ⊥  , emptyFin*) 

            ⊕ : Functor (FinSetMono ×C FinSetMono) FinSetMono
            ⊕ .F-ob (x , y) = (x .fst ⊎ y .fst) , isFinSet⊎ x y
            ⊕ .F-hom (f , g) = ⊎Monotone↪ f g
            ⊕ .F-id = Σ≡Prop (λ x → isPropIsEmbedding) (funExt λ{(inl x) → refl
                                                               ; (inr x) → refl })
            ⊕ .F-seq f g = Σ≡Prop (λ x → isPropIsEmbedding) (funExt λ{ (inl x) → refl
                                                                     ; (inr x) → refl })

            FS = FinSetMono

            Inl : {X Y : ob FS} → FS [ X , ⊕ .F-ob (X , Y) ]
            Inl = inl , isEmbedding-inl

            Inr : {X Y : ob FS} → FS [ Y , ⊕ .F-ob (X , Y) ]
            Inr = inr , isEmbedding-inr

            open import Cubical.Foundations.Isomorphism
            idl⊕ : (X : FinSet ℓ) → ⊕ .F-ob (Ø , X) ≡ X 
            idl⊕ X = Σ≡Prop (λ _ → isPropIsFinSet) (isoToPath ⊎-IdL-⊥*-Iso)

            idr⊕ : (X : FinSet ℓ) → ⊕ .F-ob (X , Ø) ≡ X 
            idr⊕ X = Σ≡Prop (λ _ → isPropIsFinSet) (isoToPath ⊎-IdR-⊥*-Iso)

            assoc⊕ : (X Y Z : FinSet ℓ) →  ⊕ .F-ob (X , ⊕ .F-ob (Y , Z)) ≡ ⊕ .F-ob (⊕ .F-ob (X , Y), Z)
            assoc⊕ X Y Z = Σ≡Prop (λ _ → isPropIsFinSet) (sym (isoToPath ⊎-assoc-Iso))

            SMC : StrictMonCategory (ℓ-suc ℓ) ℓ
            SMC = record { 
                    C = FinSetMono ; 
                    sms = record { 
                            tenstr = 
                                record { 
                                    ─⊗─ = ⊕ ; 
                                    unit = Ø } ; 
                            assoc = assoc⊕ ; 
                            idl = idl⊕ ; 
                            idr = idr⊕ } }


        -- partition
        module part where
            open import Cubical.Categories.Functor 
            open Monoidal
            open Functor
            open import Cubical.Data.Sum renaming (map to Smap)
            open import Cubical.Foundations.Isomorphism
            open Iso
            open import Cubical.Functions.Image
            open import Cubical.HITs.PropositionalTruncation renaming (rec to Prec)

            module _ {X Y : ob FS}(f : FS [ X , Y ]) where 
                Img : ob FS 
                Img = (Image (f .fst)) , 
                    isFinSetΣ Y λ y → (isInImage (f .fst) y) , 
                    isFinSet∥∥ ((Σ (X .fst) (λ x → (f .fst) x ≡ y)) , 
                    isFinSetΣ X λ x → ((f .fst) x ≡ y) , 
                    isFinSet≡ Y  ((f .fst) x) y)

                f|Img : FS [ X , Img ]
                f|Img = (restrictToImage (f .fst)) , isEquiv→isEmbedding (isEquivEmbeddingOntoImage f)

                _ = isFinProp→Dec

                open import Cubical.Relation.Nullary 
                decIsInImage : ( y : fst Y) → Dec (isInImage (f .fst) y)
                decIsInImage y = isFinProp→Dec 
                            (isFinSet∥∥ ((Σ (X .fst) (λ x → (f .fst) x ≡ y)) , (isFinSetΣ X λ x → ((f .fst) x ≡ y) , isFinSet≡ Y (f .fst x) y))) 
                            (isPropIsInImage (f .fst) y)
                            
                open import Cubical.Data.FinSet.DecidablePredicate
                _ = isFinSetSub
                open import Cubical.Data.Bool
                _ = Dec→Bool
                
                --¬Img : ob FS 
                --¬Img = (¬ Image (f .fst)) , isFinSet¬ Img

                ¬Img : ob FS 
                ¬Img = ( Σ[ y ∈ Y .fst ] (¬(isInImage (f .fst ) y)) ) , isFinSetΣ Y λ y → (¬(isInImage (f .fst ) y)) , (isFinSet¬ ((isInImage (f .fst ) y) , isFinSet∥∥ ((Σ (X .fst) (λ x → (f .fst) x ≡ y)) , 
                    isFinSetΣ X λ x → ((f .fst) x ≡ y) , 
                    isFinSet≡ Y  ((f .fst) x) y)))
                
                part : ob FS 
                part = ⊕ .F-ob (Img , ¬Img )

                {-
                                        goal' with (isDecProp≡ (w .fst .fst) (case .fst) (osum .fst) )
                        ... | false , _ = N w Γw
                        ... | true , eq = M w (Γw , a) where 
                            eqtag : case .fst ≡ osum .fst  
                -}
                theorem : CatIso FS Y part
                theorem = fwd , isiso bkwd prf1 {!   !} where 
                    fwd : FS [ Y , part ]
                    fwd = m , {!λ w x isEmbeddingFstΣProp ?  !} where 
                        m : fst Y → fst part 
                        m y = decRec (λ yin → inl (y , yin)) (λ yout → inr (y , yout)) (decIsInImage y)


                    bkwd : FS [ part , Y ]
                    bkwd = n , {!   !} where 
                        n : fst part → fst Y
                        n (inl x) = x .fst
                        n (inr x) = x .fst

                    prf1 : seq' FS bkwd fwd ≡ FS .id
                    prf1 = {!   !} -- Σ≡Prop (λ x → isPropIsEmbedding) ?   here be poor typechecking timeout

                


            module _ (X Y Z : ob FS)(h : FS [ ⊕ .F-ob (X , Y) , Z ]) where 

                f : FS [ X , Z ]
                f = (Inl {X} {Y} ⋆⟨ FS ⟩ h)

                hx : FS [ X , Img {X}{Z} f ]
                hx = f|Img {X}{Z} f

                g : FS [ Y , Z ]
                g = (Inr {X} {Y} ⋆⟨ FS ⟩ h)

                hy : FS [ Y , Img {Y}{Z} g ]
                hy = f|Img {Y}{Z} g

                h' : FS [ ⊕ .F-ob (X , Y) , ⊕ .F-ob (Img f , Img g) ]
                h' = ⊎Monotone↪ hx hy

                _ = isDecProp→isFinSet

                prf : CatIso FS (Img h') (⊕ .F-ob ((Img f) , (Img g)))
                prf = frwd , isiso bkwd prf1 prf2 where 
                    frwd : FS [ Img h' , ⊕ .F-ob ((Img f) , (Img g)) ]
                    frwd = fst , λ _ _ → isEmbeddingFstΣProp λ _ → isPropIsInImage _ _ 

                    bkwd : FS [ ⊕ .F-ob ((Img f) , (Img g)) , Img h' ]
                    bkwd = (λ {(inl imgf) → (inl imgf) , Prec (isPropIsInImage _ _)  (λ{(x , xin) → ∣ inl x , cong inl (Σ≡Prop (λ _ → isPropIsInImage _ _) xin) ∣₁}) (imgf .snd)
                             ; (inr imgg) → (inr imgg) , Prec (isPropIsInImage _ _)  (λ{(y , yin) → ∣ inr y , cong inr (Σ≡Prop (λ _ → isPropIsInImage _ _) yin) ∣₁}) (imgg .snd)}) , {!   !}

                    -- proof with no binders just following types
                    -- could this be automated
                    prf2 : seq' FS frwd bkwd ≡ FS .id 
                    prf2 = Σ≡Prop (λ _ → isPropIsEmbedding) (funExt λ{(inl _ , _) → Σ≡Prop (λ _ → isPropIsInImage _ _) refl
                                                                    ; (inr _ , _) → Σ≡Prop (λ _ → isPropIsInImage _ _) refl})

                    prf1 : seq' FS bkwd frwd ≡ FS .id 
                    prf1 = Σ≡Prop (λ _ → isPropIsEmbedding) (funExt λ {(inl _) → refl
                                                                     ; (inr _) → refl})


                otherprf : CatIso FS (Img h) (Img h')
                otherprf = frwd , isiso {!   !} {!   !} {!   !} where 
                    frwd : FS [ Img h , Img h' ]
                    frwd = (λ {(z , zin) → {!   !} , {!   !}}) , {!   !}

                    bkwd : FS [ Img h' , Img h ]
                    bkwd = (λ{(inl x , snd₁) → (x .fst) , {!   !}
                            ; (inr x , snd₁) → {!   !}}) , {!   !}
                
                _ : FS [ Z , ⊕ .F-ob (Img h , ¬Img h ) ] -- part h
                _ = theorem h .fst

                open import Cubical.Functions.Surjection
                alt : Iso (Img h .fst) (Img h' .fst) 
                alt = imagesIso ((λ x → {!   !}) , {!   !})  {!   !} {!   !} {!   !} {!   !}


                eventually : CatIso FS Z (⊕ .F-ob (⊕ .F-ob (Img f , Img g), ¬Img h))
                eventually = (theorem h .fst ⋆⟨ FS ⟩ ⊎Monotone↪ (otherprf .fst) (id↪ _) ⋆⟨ FS ⟩ ⊎Monotone↪ (prf .fst) (id↪ _)) , {!   !}


                {-
                
                E : (X .fst) ⊎ (Y .fst) → Set _
                E (inl x) = Σ (Z .fst) λ z → z ≡ h .fst (inl x)
                E (inr x) = Σ (Z .fst) λ z → z ≡ h .fst (inr x)

                split :   ((a : X .fst) → Σ (Z .fst) λ z → z ≡ h .fst (inl a)) 
                        × ((a : Y .fst) → Σ (Z .fst) λ z → z ≡ h .fst (inr a))
                split = Π⊎Iso {E = E} .fun λ{(inl x) → (h .fst (inl x)) , refl
                                           ; (inr x) → (h .fst (inr x)) , refl }


                E' : (X .fst) ⊎ (Y .fst) → ob FS
                E' (inl x) = E (inl x) , isFinSetΣ Z λ z → (z ≡ h .fst (inl x)) , isFinSet≡ Z z (h .fst (inl x))
                E' (inr x) = E (inr x) , isFinSetΣ Z λ z → (z ≡ h .fst (inr x)) , isFinSet≡ Z z (h .fst (inr x))
                -}
   