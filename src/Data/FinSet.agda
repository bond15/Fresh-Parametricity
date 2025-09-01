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

        module Partition where 
            open import Cubical.Categories.Functor 
            open Monoidal
            open Functor
            open import Cubical.Data.Sum renaming (map to Smap)
            open import Cubical.Foundations.Isomorphism
            open Iso
            open import Cubical.Functions.Image
            open import Cubical.HITs.PropositionalTruncation renaming (rec to Prec)
            open import Cubical.Relation.Nullary 
            open import Cubical.Foundations.Equiv

            module _ {X Y : ob FS}(f : FS [ X , Y ]) where 
                Img : ob FS 
                Img = (Image (f .fst)) , 
                    isFinSetΣ Y λ y → (isInImage (f .fst) y) , 
                    isFinSet∥∥ ((Σ (X .fst) (λ x → (f .fst) x ≡ y)) , 
                    isFinSetΣ X λ x → ((f .fst) x ≡ y) , 
                    isFinSet≡ Y  ((f .fst) x) y)

                f|Img : FS [ X , Img ]
                f|Img = (restrictToImage (f .fst)) , isEquiv→isEmbedding (isEquivEmbeddingOntoImage f)

                ¬Img : ob FS 
                ¬Img = ( Σ[ y ∈ Y .fst ] (¬(isInImage (f .fst ) y)) ) , 
                    isFinSetΣ Y λ y → (¬(isInImage (f .fst ) y)) , 
                    isFinSet¬ ((isInImage (f .fst ) y) , 
                    isFinSet∥∥ ((Σ (X .fst) (λ x → (f .fst) x ≡ y)) , 
                    isFinSetΣ X λ x → ((f .fst) x ≡ y) , 
                    isFinSet≡ Y  ((f .fst) x) y))

                decIsInImage : ( y : fst Y) → Dec (isInImage (f .fst) y)
                decIsInImage y = isFinProp→Dec 
                            (isFinSet∥∥ ((Σ (X .fst) (λ x → (f .fst) x ≡ y)) , 
                            (isFinSetΣ X λ x → ((f .fst) x ≡ y) , 
                            isFinSet≡ Y (f .fst x) y))) 
                            (isPropIsInImage (f .fst) y)

                YIso : Iso (Y .fst) (⊕ .F-ob (Img , ¬Img ) .fst)
                YIso = iso 
                        ((λ y → decRec (λ yin → inl (y , yin)) (λ yout → inr (y , yout)) (decIsInImage y))) 
                        (λ {(inl x) → x .fst
                          ; (inr x) → x .fst}) 
                        (λ{ (inl x) →  {! !}
                          ; (inr x) → {!   !}}) 
                        λ{ y → {! y  !}} 

                in⊎Out : FS [ Y , ⊕ .F-ob (Img , ¬Img ) ]
                in⊎Out = (λ y → decRec (λ yin → inl (y , yin)) (λ yout → inr (y , yout)) (decIsInImage y)) , isEquiv→isEmbedding (isoToEquiv YIso .snd)

            module SimpleSplit {X Y Z : ob FS}(h : FS [ ⊕ .F-ob (X , Y) , Z ]) where 

                f : FS [ X , Z ]
                f = (Inl {X} {Y} ⋆⟨ FS ⟩ h)

                zx : ob FS 
                zx = Img {X} {Z} f

                hx : FS [ X , zx ]
                hx = f|Img {X}{Z} f

                Zsplit : ob FS 
                Zsplit = ⊕ .F-ob ({!   !} , {!   !})    

            module Split {X Y Z : ob FS}(h : FS [ ⊕ .F-ob (X , Y) , Z ]) where 

                f : FS [ X , Z ]
                f = (Inl {X} {Y} ⋆⟨ FS ⟩ h)

                g : FS [ Y , Z ]
                g = (Inr {X} {Y} ⋆⟨ FS ⟩ h)
                
                zx : ob FS 
                zx = Img {X} {Z} f

                zy : ob FS 
                zy = Img {Y} {Z} g 
                
                zm : ob FS 
                zm = ¬Img {⊕ .F-ob (X , Y)} {Z} h

                hx : FS [ X , zx ]
                hx = f|Img {X}{Z} f

                hy : FS [ Y , zy ]
                hy = f|Img {Y}{Z} g

                h' : FS [ ⊕ .F-ob (X , Y) , ⊕ .F-ob (zx , zy) ]
                h' = ⊎Monotone↪ hx hy

                Zsplit : ob FS 
                Zsplit = ⊕ .F-ob (zx , ⊕ .F-ob ( zy , zm))

                equivImage : Image (h .fst) ≃ Image (h' .fst) 
                equivImage = compEquiv e1 e2 where 
                    e1 : Image (h .fst) ≃ (X .fst ⊎ Y .fst) 
                    e1 = invEquiv ((restrictToImage (fst h)) , (isEquivEmbeddingOntoImage h))

                    e2 : (X .fst ⊎ Y .fst) ≃ Image (h' .fst) 
                    e2 = (restrictToImage (fst h')) , (isEquivEmbeddingOntoImage h')

                hToh' : FS [ Img h , Img h' ]
                hToh' = (equivImage .fst) , (isEquiv→isEmbedding (equivImage .snd))
                
                split : FS [ Z , Zsplit ]
                split = 
                    in⊎Out h ⋆⟨ FS ⟩ 
                    ⊎Monotone↪ hToh' (id↪ _) ⋆⟨ FS ⟩ 
                    ⊎Monotone↪ (imageInclusion (h' .fst)) (id↪ _) ⋆⟨ FS ⟩ 
                    (⊎-assoc-≃ .fst , isEquiv→isEmbedding (⊎-assoc-≃ .snd))



{- cruft 

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
                    fwd = m , {! isEmbedding !} where 
                        m : fst Y → fst part 
                        m y = decRec (λ yin → inl (y , yin)) (λ yout → inr (y , yout)) (decIsInImage y)


                    bkwd : FS [ part , Y ]
                    bkwd = n , {!   !} where 
                        n : fst part → fst Y
                        n (inl x) = x .fst
                        n (inr x) = x .fst

                    prf1 : seq' FS bkwd fwd ≡ FS .id
                    prf1 = {!   !} -- Σ≡Prop (λ x → isPropIsEmbedding) ?   here be poor typechecking timeout

                open import Agda.Builtin.Cubical.Equiv
                -- isEquivEmbeddingOntoImage
                _ : isEquiv (restrictToImage (fst f))
                _ = isEquivEmbeddingOntoImage f

                _ = isoToPath
                _ : X .fst ≃ Image (f .fst) 
                _ = (restrictToImage (fst f)) , (isEquivEmbeddingOntoImage f)


            module _ {X Y Z : ob FS}(h : FS [ ⊕ .F-ob (X , Y) , Z ]) where 
                open import Cubical.Relation.Nullary 
                open import Agda.Builtin.Cubical.Equiv


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


                Zsplit : ob FS 
                Zsplit = ⊕ .F-ob (⊕ .F-ob (Img f , Img g) , ¬Img h)

                open import Cubical.Foundations.Equiv

                hmm  : (X .fst ⊎ Y .fst) ≃ Image (h .fst) 
                hmm  = (restrictToImage (fst h)) , (isEquivEmbeddingOntoImage h)

                also : (X .fst ⊎ Y .fst) ≃ Image (h' .fst) 
                also = (restrictToImage (fst h')) , (isEquivEmbeddingOntoImage h')

                then : Image (h .fst) ≃ Image (h' .fst) 
                then = compEquiv (invEquiv hmm) also

                hh' : FS [ Img h , Img h' ]
                hh' = (then .fst) , (isEquiv→isEmbedding (then .snd))
                
                fromZ : FS [ Z , Zsplit ]
                fromZ = theorem h .fst ⋆⟨ FS ⟩ ⊎Monotone↪ hh' (id↪ _) ⋆⟨ FS ⟩ ⊎Monotone↪ (imageInclusion (h' .fst)) (id↪ _)

                -- imageFactorization
                toZ : FS [ ⊕ .F-ob (Img f , Img g) , Z ]
                toZ = (λ {(inl x) → x .fst
                        ; (inr x) → x .fst}) , {!   !}

                factorize : h ≡ h' ⋆⟨ FS ⟩ toZ 
                factorize = {!   !} -- slow typechecking
                    -- Σ≡Prop (λ x → isPropIsEmbedding) ?

                open import Cubical.Foundations.Equiv

                hmm  : (X .fst ⊎ Y .fst) ≃ Image (h .fst) 
                hmm  = (restrictToImage (fst h)) , (isEquivEmbeddingOntoImage h)

                also : (X .fst ⊎ Y .fst) ≃ Image (h' .fst) 
                also = (restrictToImage (fst h')) , (isEquivEmbeddingOntoImage h')

                then : Image (h .fst) ≃ Image (h' .fst) 
                then = compEquiv (invEquiv hmm) also

                alas : CatIso FS (Img h) (Img h') 
                alas = fwrd , isiso bkwd prf1  {!   !} where 
                    fwrd : FS [ Img h , Img h' ] 
                    fwrd = (fst then) , (isEquiv→isEmbedding (then .snd))

                    bkwd : FS [ Img h' , Img h ]
                    bkwd = (invEquiv then .fst) , (isEquiv→isEmbedding ((invEquiv then .snd)))

                    prf1 : seq' FS bkwd fwrd ≡ FS .id 
                    prf1 =  {!   !} -- bad typchecking timeout Σ≡Prop (λ _ → isPropIsEmbedding) ?
                
                
                woah : Image (h .fst) → (X .fst ⊎ Y .fst)
                woah = invEq hmm

                problem : (z : Z .fst) → isInImage (f .fst) z ⊎ ((isInImage (g .fst) z) ⊎ (¬ (isInImage (h .fst) z)))
                problem z = decRec goal  (λ zouth → inr  (inr zouth)) ((decIsInImage h z)) where 
                    goal : isInImage (h .fst) z → isInImage (f .fst) z ⊎ ((isInImage (g .fst) z) ⊎ (¬ (isInImage (h .fst) z)))
                    goal zinh with (woah (z , zinh)) 
                    ... | (inl x) = inl (Prec ((isPropIsInImage _ _)) (λ{(inl x , snd₁) → {!   !}
                                                                       ; (inr x , snd₁) → {!   !}}) zinh)
                    ... | (inr y) = {!   !}
                        --xy : (X .fst ⊎ Y .fst)
                       -- xy = woah (z , zinh)

                        {-
                        with (isDecProp≡ (w .fst .fst) (case .fst) (osum .fst) )
                        ... | false , _ = N w Γw
                        ... | true , eq = M w (Γw , a) where  
                        -}

                
                _ = isDecProp→isFinSet

                prf : CatIso FS (Img h') (⊕ .F-ob ((Img f) , (Img g)))
                prf = frwd , isiso bkwd prf1 prf2 where 
                    frwd : FS [ Img h' , ⊕ .F-ob ((Img f) , (Img g)) ]
                    frwd = imageInclusion (h' .fst)

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