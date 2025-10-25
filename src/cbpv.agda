{-# OPTIONS --allow-unsolved-metas #-}
module src.cbpv where 
    open import Cubical.Foundations.Prelude
    open import Cubical.Foundations.HLevels 
    open import Cubical.Data.Unit
    open import Cubical.Data.Nat
    open import Cubical.Data.Fin.Recursive

    mutual 
        data CTy : Set where 
            fun : VTy → CTy → CTy 
            F : VTy → CTy 

        data VTy : Set where 
            one : VTy 
            prod : VTy → VTy → VTy 
            U : CTy → VTy

    Ctx : Set
    Ctx = Σ[ n ∈ ℕ ] (Fin n → VTy)

    ⊘ : Ctx 
    ⊘ = 0 , λ ()

    _,,_ : Ctx → VTy → Ctx  
    _,,_ (n , Γ) A = suc n , λ {zero → A
                              ; (suc x) → Γ x}


    mutual 
        data _⊢v_  : Ctx → VTy →  Set where 
            var : {(n , Γ) : Ctx} →
                 (i : Fin n) → 
                 ----------------
                 (n , Γ) ⊢v (Γ i)

            u : {Γ : Ctx} → 
                ----------
                Γ ⊢v one
            pair : {Γ : Ctx}{A A' : VTy} → 
                Γ ⊢v A → 
                Γ ⊢v A' → 
                -----------------
                Γ ⊢v (prod A A')
            thunk : {Γ : Ctx}{B : CTy} → 
                Γ ⊢c B → 
                ----------
                Γ ⊢v U B

        data _⊢c_ : Ctx → CTy → Set where 
            ret : {Γ : Ctx}{A : VTy} → 
                Γ ⊢v A → 
                --------- 
                Γ ⊢c F A

            lam : {Γ : Ctx}{A : VTy}{B : CTy} →  
                (Γ ,, A) ⊢c B → 
                ---------------- 
                Γ ⊢c fun A B
            app : {Γ : Ctx}{A : VTy}{B : CTy} → 
                Γ ⊢c fun A B → 
                Γ ⊢v A → 
                ---------------- 
                Γ ⊢c B
            
            rec× : { Γ : Ctx} {A A' : VTy}{ B : CTy} → 
                Γ ⊢v (prod A A') → 
                ((Γ ,, A) ,, A') ⊢c B → 
                -------------------- 
                Γ ⊢c B

            bind : {Γ : Ctx}{A : VTy}{B : CTy} → 
                Γ ⊢c F A → 
                (Γ ,, A) ⊢c B → 
                ----------- 
                Γ ⊢c B
            
        data _◂_⊢k_ : Ctx → CTy → CTy → Set where
            varc : {Γ : Ctx}{B : CTy} → Γ ◂ B ⊢k B
            ∙V : {Γ : Ctx}{A : VTy}{B B' : CTy} → 
                Γ ⊢v A → 
                Γ ◂ B ⊢k fun A B' → 
                -----------------------------
                Γ ◂ B ⊢k B'
            x←∙:M : {Γ : Ctx}{A : VTy}{B B' : CTy} →
                Γ ◂ B ⊢k F A → 
                (Γ ,, A) ⊢c B' → 
                -----------------------------------
                Γ ◂ B ⊢k B'

    Sub[_,_] : Ctx → Ctx → Set
    Sub[_,_] Δ Γ = (x : Fin (Γ .fst)) → Δ ⊢v (Γ .snd x)

    idsub : {Γ : Ctx} → Sub[ Γ , Γ ]
    idsub = var

    mutual 
        wkv : {Δ : Ctx}{A A' : VTy} → Δ ⊢v A' → (Δ ,, A) ⊢v A'
        wkv (var i) = var (suc i)
        wkv u = u
        wkv (pair v w) = pair (wkv v) (wkv w)
        wkv (thunk m) = thunk (wkc m)

        {-# TERMINATING #-}
        wkc : {Δ : Ctx}{A : VTy}{B : CTy} → Δ ⊢c B → (Δ ,, A) ⊢c B
        wkc (ret v) = ret (wkv v)
        wkc {Δ}{A}{B}(lam m) = lam {! wkc {Δ = Δ ,, A}   !}
        wkc (app m v) = app (wkc m) (wkv v)
        wkc (rec× v m) = rec× (wkv v) {! wkc {?}{?}{?} m  !}
        wkc {Δ}{A}{B} (bind {A = A'} m m') = bind (wkc m) (wkc {Δ ,, A}{A'}{B}  {!  !})

    wksub : {Δ Γ : Ctx}{A : VTy} → Sub[ Δ , Γ ] →  Sub[ Δ ,, A , Γ ,, A ]
    wksub γ zero = var zero
    wksub γ (suc x) = wkv (γ x)
    
    mutual 
        vsub : {Γ Δ : Ctx}{A : VTy} → Sub[ Δ  , Γ ] → Γ ⊢v A → Δ ⊢v A 
        vsub γ (var i) = γ i
        vsub γ u = u
        vsub γ (pair v w) = pair (vsub γ v) (vsub γ w)
        vsub γ (thunk m) = thunk (csub γ m)

        csub : {Γ Δ : Ctx}{B : CTy} → Sub[ Δ  , Γ ] → Γ ⊢c B → Δ ⊢c B
        csub γ (ret v) = ret (vsub γ v)
        csub γ (lam m) = lam (csub (wksub  γ) m) 
        csub γ (rec× v m ) = rec× (vsub γ v) (csub (wksub (wksub γ)) m)
        csub γ (app m v) = app (csub γ m) (vsub γ v)
        csub γ (bind m m') = bind (csub γ m) (csub (wksub γ) m') 

        ksubCtx : {Γ Δ : Ctx}{B B' : CTy} → Sub[ Δ  , Γ ]  → Γ ◂ B ⊢k B' → Δ ◂ B ⊢k B' 
        ksubCtx γ varc = varc
        ksubCtx γ (∙V v k) = (∙V (vsub γ v) (ksubCtx γ k) )
        ksubCtx γ (x←∙:M k m) = x←∙:M (ksubCtx γ k) (csub (wksub γ) m)

    compsub : {Γ Δ Θ : Ctx} → Sub[ Γ , Δ ] → Sub[ Δ , Θ ] → Sub[ Γ , Θ ]
    compsub γ δ i = vsub γ (δ i)

    mutual 

        lem : {Γ : Ctx}{B : CTy}{A : VTy}{m : (Γ ,, A) ⊢c B} → csub (wksub idsub) m ≡ m
        lem = {! wksub idsub  !}
        
        csubid : {Γ : Ctx}{B : CTy}{m : Γ ⊢c B} → csub idsub m ≡ m
        csubid {m = ret x} = cong ret vsubid
        csubid {m = lam m} = cong lam lem
        csubid {m = app m x} = cong₂ app csubid vsubid
        csubid {m = rec× x m} = cong₂ rec× vsubid {!   !}
        csubid {m = bind m m₁} = cong₂ bind csubid lem

        vsubid : {Γ : Ctx}{A : VTy}{v : Γ ⊢v A} → vsub idsub v ≡ v
        vsubid {v = var i} = refl
        vsubid {v = u} = refl
        vsubid {v = pair v v₁} = cong₂ pair vsubid vsubid
        vsubid {v = thunk x} = cong thunk csubid

    -- Levy book 221
    scomp : {Γ : Ctx}{B₁ B₂ B₃ : CTy}→ Γ ◂ B₁ ⊢k B₂ → Γ ◂ B₂ ⊢k B₃ → Γ ◂ B₁ ⊢k B₃ 
    scomp k varc = k
    scomp k (∙V v k') = ∙V v (scomp k k')
    scomp k (x←∙:M k' m) = x←∙:M (scomp k k') m

    plug : {Γ : Ctx}{B B' : CTy} → Γ ◂ B ⊢k B' → Γ ⊢c B → Γ ⊢c B' 
    plug varc m = m
    plug (∙V v k) m = app (plug k m) v 
    plug (x←∙:M k x) m = bind (plug k m) x


    scompid : {Γ : Ctx}{B B' : CTy}{k : Γ ◂ B ⊢k B'} → k ≡ scomp varc k
    scompid {k = varc} = refl
    scompid {k = ∙V x k} = cong₂ ∙V refl scompid
    scompid {k = x←∙:M k x} = cong₂ x←∙:M scompid refl
 
   