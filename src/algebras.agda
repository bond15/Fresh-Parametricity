open import Cubical.Foundations.Prelude hiding (_▷_)
open import Cubical.Foundations.HLevels

module src.algebras {ℓ : Level} where
    open import Cubical.Reflection.RecordEquiv

    open import Cubical.Foundations.Isomorphism
    open import Cubical.Data.Sigma
    ⟨_⟩ : (e : hSet ℓ) → Set ℓ 
    ⟨_⟩ = fst

    record MonoidAlg : Set (ℓ-suc ℓ) where 
        field
            carrier : hSet ℓ
            e :  ⟨ carrier ⟩
            _⊗_ : ⟨ carrier ⟩ → ⟨ carrier ⟩ → ⟨ carrier ⟩
            idl : (x : ⟨ carrier ⟩) → e ⊗ x ≡ x
            idr : (x : ⟨ carrier ⟩) → x ⊗ e ≡ x
            assoc : (x y z : ⟨ carrier ⟩) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)

    open MonoidAlg

    unquoteDecl MonAlgIsoΣ = declareRecordIsoΣ MonAlgIsoΣ (quote MonoidAlg)


    --data MRel (A B : MonoidAlg) : ⟨ A .carrier ⟩ → ⟨ B .carrier ⟩ → Set ℓ where
    --    l1 : (x y : ⟨ A .carrier ⟩)(x' y' : ⟨ B .carrier ⟩) → 
    --                (MRel A B x x') × (MRel A B y y') → MRel A B (A ._⊗_ x y) (B ._⊗_ x' y')

    record MonoidRel (A B : MonoidAlg) : Set (ℓ-suc ℓ) where 
        field 
            R : ⟨ A .carrier ⟩ → ⟨ B .carrier ⟩ → Set ℓ
            l1 : {x y : ⟨ A .carrier ⟩}{x' y' : ⟨ B .carrier ⟩} → 
                    (R x x') × (R y y') → R (A ._⊗_ x y) (B ._⊗_ x' y')
            l2 : R (A .e) (B .e)

    
    I_ : (A : MonoidAlg) → MonoidRel A A 
    I_ A = record { R = _≡_ ; 
                    l1 = λ{(p , q) → cong₂ (A ._⊗_) p q} ; 
                    l2 = refl }


    record MonoidAlgHom (A B : MonoidAlg) : Set ℓ where
        field 
            f : ⟨ A .carrier ⟩ → ⟨ B .carrier ⟩ 
            e→ : f (A .e) ≡ B .e
            ⊗→ : (a b : ⟨ A .carrier ⟩ ) → f ((A ._⊗_) a b) ≡ (B ._⊗_) (f a)(f b)
    
    open MonoidAlgHom

    MonoidAlgHom' : (A B : MonoidAlg) → Set ℓ 
    MonoidAlgHom' A B = Σ (⟨ A .carrier ⟩ → ⟨ B .carrier ⟩) λ f → 
                        Σ (f (A .e) ≡ B .e) λ _  → 
                        (a b : ⟨ A .carrier ⟩ ) → f ((A ._⊗_) a b) ≡ (B ._⊗_) (f a)(f b)


    hmm : (A : hSet ℓ)(x y : ⟨ A ⟩) → isSet (x ≡ y)
    hmm A x y = isProp→isSet (A .snd x y)
    
    isSetMonHom' : {A B : MonoidAlg} → isSet (MonoidAlgHom' A B) 
    isSetMonHom' {A}{B} = isSetΣ (isSet→ (B .carrier .snd)) λ f → 
                            isSetΣ (hmm (B .carrier) _ _) λ _ → isSetΠ  λ _ → isSetΠ λ _ →  
                            hmm (B .carrier) _ _

    open import Cubical.Foundations.Path
    
    MonHom≡' : {A B : MonoidAlg}{F G : MonoidAlgHom' A B} → F .fst ≡ G .fst → F ≡ G 
    MonHom≡' {A} {B} {F} {G} p = ΣPathP (
                                    p , 
                                    ΣPathPProp (λ eq → isPropΠ λ _ → isPropΠ λ _ → B .carrier .snd _ _) 
                                    (isProp→PathP (λ i → B .carrier .snd _ _) _ _) ) 

    unquoteDecl MonHomIsoΣ = declareRecordIsoΣ MonHomIsoΣ (quote MonoidAlgHom)

    open Iso 
    _ = isoToEquiv

    eqHom : {A B : MonoidAlg} → MonoidAlgHom A B ≡ MonoidAlgHom' A B 
    eqHom = isoToPath MonHomIsoΣ

    thing : (A B : Set ℓ)(p : Iso A B)(a a' : A)(b b' : B)(l : a ≡ p .inv b)(q : b ≡ b')(r : a' ≡ p .inv b') → a ≡ a'
    thing A B p a a' b b' l q r = l ∙ cong (λ h → p .inv h) q  ∙ sym r

    MonHom≡  : {A B : MonoidAlg}{F G : MonoidAlgHom A B} → F .f ≡ G .f → F ≡ G 
    MonHom≡ {A}{B}{F}{G} p = thing _ _ MonHomIsoΣ F G (MonHomIsoΣ .fun F) (MonHomIsoΣ .fun G) (sym (MonHomIsoΣ .leftInv F)) fact (sym ( MonHomIsoΣ .leftInv G)) where 
        fact : MonHomIsoΣ .fun F ≡ MonHomIsoΣ .fun G
        fact = MonHom≡' {A}{B}{MonHomIsoΣ .fun F}{MonHomIsoΣ .fun G} p 


    isSetMonHom : {A B : MonoidAlg} → isSet (MonoidAlgHom A B) 
    isSetMonHom {A} {B} = transport (cong isSet (isoToPath (invIso MonHomIsoΣ))) (isSetMonHom' {A}{B})


    HomRel : {A B : MonoidAlg} → MonoidAlgHom A B → MonoidRel A B 
    HomRel {A} {B} F = record { R = λ a b → F .f a ≡ b ; 
                                l1 = λ{(p , q) → F .⊗→ _ _ ∙ cong₂ (B ._⊗_) p q} ; 
                                l2 = F .e→ }

    open import Cubical.Categories.Category
    open Category
    open import Cubical.Foundations.Function


    MonCat : Category _ _ 
    MonCat .ob = MonoidAlg
    MonCat .Hom[_,_] = MonoidAlgHom
    MonCat .id = record { f = λ x → x ; e→ = refl ; ⊗→ = λ _ _ → refl }
    MonCat ._⋆_ A B = record { f = (B .f) ∘S (A .f) ; e→ = cong (λ h → B .f h) (A .e→) ∙ B .e→ ; ⊗→ = λ a b → cong (λ h → B .f h) (A .⊗→ _ _) ∙ B .⊗→ _ _ }
    MonCat .⋆IdL F = MonHom≡ refl
    MonCat .⋆IdR F = MonHom≡ refl
    MonCat .⋆Assoc _ _ _ = MonHom≡ refl
    MonCat .isSetHom = isSetMonHom

    -- initial object in the category of Monoid Algebras
    data FreeMon : Set ℓ where 
        fe : FreeMon
        _⊗f_ : FreeMon → FreeMon → FreeMon
        fidl : ∀ {x : FreeMon} → fe ⊗f x ≡ x
        fidr : ∀ {x : FreeMon} → x ⊗f fe ≡ x 
        fassoc : ∀ {x y z : FreeMon} → (x ⊗f y) ⊗f z ≡ x ⊗f (y ⊗f z)
        fisSet : isSet FreeMon

    -- tautologically 
    FreeMonAlg : ob MonCat
    FreeMonAlg .carrier = FreeMon , fisSet
    FreeMonAlg .e = fe
    FreeMonAlg ._⊗_ x y = x ⊗f y
    FreeMonAlg .idl _ = fidl 
    FreeMonAlg .idr _ = fidr 
    FreeMonAlg .assoc _ _ _ = fassoc


    open import Cubical.Data.List  


    
    ListMonAlg : {A : hSet ℓ} → ob MonCat
    ListMonAlg {A} .carrier = List ⟨ A ⟩  , isOfHLevelList 0 {⟨ A ⟩} (A .snd)
    ListMonAlg {A} .e = [] 
    ListMonAlg {A} ._⊗_ = _++_ 
    ListMonAlg {A} .idl _ = refl
    ListMonAlg {A} .idr _ = ++-unit-r _ 
    ListMonAlg {A} .assoc = ++-assoc 


    ret : {A : hSet ℓ }→ ⟨ A ⟩  → List ⟨ A ⟩  
    ret a = [ a ]

    open import Cubical.Data.Sigma 

    module _ {A : hSet ℓ}
             {i : ⟨ A ⟩ → FreeMon } where 
        
        prove : ∃![ m ∈ (MonoidAlgHom (ListMonAlg {A}) FreeMonAlg) ] m .f ∘S (ret {A}) ≡ i 
        prove = 
            uniqueExists 
                m
                hm 
                (λ _ → isSet→ (fisSet) _ i) 
                final where 

                m' : List ⟨ A ⟩ → FreeMon 
                m' [] = fe
                m' (x ∷ xs) = i x ⊗f m' xs

                prf : (a b : List ⟨ A ⟩ ) → m' (a ++ b) ≡ (m' a ⊗f m' b) 
                prf [] b = sym fidl
                prf (x ∷ a) b = cong (λ h → (i x ⊗f h)) (prf a b) ∙ sym fassoc

                hm : m' ∘S ret {A} ≡ i 
                hm = funExt λ x → fidr

                m : MonoidAlgHom (ListMonAlg {A}) FreeMonAlg
                m .f = m' 
                m .e→ = refl
                m .⊗→ _ _ = prf _ _

                final : (n : MonoidAlgHom (ListMonAlg {A}) FreeMonAlg) → n .f ∘S ret{A} ≡ i → m ≡ n
                final n p = MonHom≡ (funExt prf') where 
                        n' = n .f
                        fact : (a : ⟨ A ⟩) → n' ([ a ]) ≡ i a 
                        fact a i = p i a

                        prf' : (xs : List ⟨ A ⟩) → m' xs ≡ n' xs 
                        prf' [] = sym (n .e→)
                        prf' (x ∷ xs) = cong (λ h → h ⊗f (m' xs)) (sym (fact x)) ∙ cong (λ h → n' [ x ] ⊗f h) (prf' xs) ∙  sym (n .⊗→ [ x ] xs)

                        



    
    open import Cubical.Categories.Limits.Initial

    Init2 : {A : hSet ℓ} → Initial MonCat 
    Init2 {A} = ListMonAlg {A} , {!   !} where 
        isInit : isInitial MonCat (ListMonAlg {A}) 
        isInit X = theMap , isunique where 


            -- but where does this come from?
            i : ⟨ A ⟩ → ⟨ X .carrier ⟩ 
            i = {!   !}
            
            m : List ⟨ A ⟩ → ⟨ X .carrier ⟩ 
            m [] = X .e
            m (x ∷ xs) = X ._⊗_ (i x) (m xs)

            prf : (a b : List ⟨ A ⟩) → m (a ++ b) ≡ X ._⊗_ (m a) (m b)
            prf [] b = sym (X .idl _)
            prf (x ∷ a) b = cong (λ h → X ._⊗_ (i x) h) (prf a b) ∙ sym (X .assoc _ _ _)

            theMap : MonoidAlgHom (ListMonAlg {A})  X 
            theMap .f = m
            theMap .e→ = refl
            theMap .⊗→ = prf

            isunique : (n : MonoidAlgHom (ListMonAlg {A}) X ) → theMap ≡ n
            isunique n = MonHom≡ (funExt prf' ) where 
                prf' : (x : List ⟨ A ⟩) → m x ≡ n .f x 
                prf' [] = sym (n .e→)
                    -- we dont know i x ≡ n .f [x]
                prf' (x ∷ xs) = cong₂ (λ h h' → X ._⊗_ h h') {!   !} (prf' xs) ∙ sym (n .⊗→ [ x ] xs)

    Init : Initial MonCat 
    Init = FreeMonAlg , isInit where 
        isInit : isInitial MonCat FreeMonAlg
        isInit A = goal where 
            goal : isContr (MonCat .Hom[_,_] FreeMonAlg A )
            goal = theMap , isunique where 

                m : FreeMon → ⟨ A .carrier ⟩ 
                m fe = A .e
                m (e₁ ⊗f e₂) = A ._⊗_ (m e₁) (m e₂)
                m (fidl {x} i) = A .idl (m x) i
                m (fidr {x} i) = A .idr (m x) i
                m (fassoc {x} {y} {z} i) = A .assoc (m x) (m y) (m z) i
                m (fisSet e₁ e₂ x y i i₁) = A .carrier .snd (m e₁) (m e₂) (cong m x) (cong m y) i i₁
            
                theMap : MonoidAlgHom FreeMonAlg A
                theMap .f = m
                theMap .e→ = refl 
                theMap .⊗→ _ _ = refl 


                {- 
                    A .idr (m x) : (A ⊗ m x) (e A) ≡ m x
                    i = 0

                    (A ⊗ m x) (e A) ≡ F .f (fidr i0)

                    i = 1
                    m x ≡ F .f (fidr i1)

                -}
                isunique : (F : MonoidAlgHom FreeMonAlg A) → theMap ≡ F
                isunique F = MonHom≡ (funExt proof) where 
                    proof : (x : FreeMon) → m x ≡ F .f x
                    proof fe = sym (F .e→)
                    proof (x ⊗f y) = cong₂ (λ h h' → A ._⊗_ h h') (proof x) (proof y) ∙ sym (F .⊗→ x y)
                    proof (fidl {x} i) = {! A .carrier .snd (A .idl (m x) i) (F .f (fidl i)) _  !}
                    proof (fidr {x} i) j = {!   !}  where 
                        p : (A ⊗ m x) (e A) ≡ m x
                        p = A .idr (m x)

                        q : F .f (x ⊗f fe) ≡ F .f x 
                        q = cong (F .f) (fidr {x})

                        r : m x ≡ F .f x
                        r = proof x

                        s : A ._⊗_ (m x) (A .e) ≡ F .f (x ⊗f fe)
                        s = proof (x ⊗f fe)

                        i0j0 = (A ⊗ m x) (e A)

                        i1j0 = m x

                        i0j1 = F .f (x ⊗f fe)
                        
                        i1j1 = F .f x 

                        _ = Square

                        {-
                            a --p-- b
                            |       |
                            r       s
                            |       |
                            d --q-- c

                            i0 ---- i1
                        -}

                        uhg : (A : hSet ℓ)(a b c d : A .fst)(p : a ≡ b)(q : d ≡ c)(r : a ≡ d)(s : b ≡ c) → p i ≡ q i 
                        uhg A a b c d p q r s j = {!   !}
                        {-
                        
                            F .f (x ⊗f fe)--q--F .f x 
                                |               |
                        j       s               r
                                |               |
                                |               |
                        (A ⊗ m x) (e A) --p-- m x
                                i
                        -}

                        -- goal A .idr (m x) i ≡ F .f (fidr i)
                        
                        idk : {!   !}
                        idk = {!   !}
                    proof (fassoc i) = {!   !}
                    proof (fisSet x x₁ x₂ y i i₁) = {!   !}
                
                {-(funExt λ{fe → sym (F .e→)
                                             ; (x ⊗f y) → cong₂ (λ h h' → A ._⊗_ h h') {!   !} {!   !} ∙ sym (F .⊗→ x y)
                                             ; (fidl i) → {!   !}
                                             ; (fidr i) → {!   !}
                                             ; (fassoc i) → {!   !}
                                             ; (fisSet x x₁ x₂ y i i₁) → {!   !}}) -}

    
{-}
    open import Data.Container
    open import Cubical.Data.Unit

    data Gs : Set where 
        eop mop invop : Gs

    groupSig : Container _ _
    groupSig = Gs ▷ λ { eop → Unit
                      ; mop → Gs × Gs
                      ; invop → Gs}

    data Foo : Set where

    groupAlg : ⟦ groupSig ⟧ Foo 
    groupAlg = eop , λ { tt → {!   !}}
    
-}

{-
--https://gallium.inria.fr/blog/lawvere-theories-and-monads/
    open import Cubical.Data.Sigma 

    -- "single cell" state
    module _ (S : Set) where
        ----------------------signature of the algebra
        data Sig (X : Set) : Set where
            `get : (S → X) → Sig X 
            `set : (S × X) → Sig X

        data Free (X : Set) : Set where 
            ret : X → Free X 
            op : Sig (Free X) → Free X

        

        _>>=_ : ∀{V W} → Free V → (V → Free W) → Free W
        (ret x) >>= mf = mf x
        (op fa) >>= mf = op (ΣStatemap mf fa)
            where
            ΣStatemap : ∀{V W} → (V → Free W) → Sig (Free V) → Sig (Free W)
            ΣStatemap mf (`get k) = `get (λ s → (k s) >>= mf)
            ΣStatemap mf (`set (s , k)) = `set (s , k >>= mf)


        get : Free S 
        get = op (`get λ s → ret s)

        set : S → Free S 
        set s = op (`set (s , ret s))


        -- equations
        data _≃_ {V : Set} : Free V → Free V → Set where
            get-get : ∀{k : S → S → Free V} → 
                (get >>= (λ s → get >>= λ s' → k s s')) ≃ (get >>= λ s → k s s)

        -- congruence closure
        data _~_ {V : Set} : Free V → Free V → Set₁ where
            inc : ∀{p q} → p ≃ q → p ~ q

            trans : ∀{p q r} → p ~ q → q ~ r → p ~ r
            ref : ∀{p} → p ~ p 
            sy : ∀{p q} → p ~ q → q ~ p

            cng : ∀{W}(tm : Free W){ps qs : W → Free V}  → 
                (∀ w → ps w ~ qs w) → 
                (tm >>= ps) ~ (tm >>= qs)


        open import Cubical.HITs.SetQuotients
        State : (X : Set) → Set _
        State X = Free X / _~_

        open import Cubical.Data.Bool 

        ex : State Bool 
        ex = [ get >>= (λ _ → get >>= λ _ → get >>= λ _ → get >>= λ _ → ret true) ]

        ex₂ : State Bool 
        ex₂ = [ get >>= (λ _ → ret true) ]

        hmm : ex ≡ ex₂ 
        hmm = eq/ _ _ (trans (inc get-get) (trans (inc get-get) (trans (inc get-get) ref)))



                

        open import Data.Container.FreeMonad
        open import Data.Container.Core


        data Two : Set where 
            `get `set : Two 
            

        Sig : (X : Set) → Container _ _ 
        Sig X = Two ▷ λ { `get → S 
                        ; `set → S × X}


        F : (X : Set) → Set
        F X = Sig X ⋆ X


        get : F S 
        get = impure (`get , (λ s → pure s))

        set : F S 
        set = impure (`set , (λ x → pure (x .fst)))

)  

        -- free monad stuff
 
      
-}    