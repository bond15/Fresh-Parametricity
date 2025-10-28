{-# OPTIONS --allow-unsolved-metas  #-}
module src.cbpv where 
    open import Cubical.Foundations.Prelude
    open import Cubical.Foundations.HLevels 
    open import Cubical.Data.Unit
    open import Cubical.Data.Nat
    open import Cubical.Data.Fin.Recursive 
    _∘s_ : {A B C : Set} → (A → B) → (B → C) → A → C 
    _∘s_ f g = λ z → g (f z)
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

            force : {Γ : Ctx}{B : CTy} → 
                Γ ⊢v U B → 
                ----------- 
                Γ ⊢c B

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
            
        -- the typing is off.. 
        -- see Levy page 35
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
       {-}     ∙V : {Γ : Ctx}{A : VTy}{B B' : CTy} → 
                Γ ⊢v A → 
                Γ ◂ B ⊢k fun A B' → 
                -----------------------------
                Γ ◂ B ⊢k B'
            x←∙:M : {Γ : Ctx}{A : VTy}{B B' : CTy} →
                Γ ◂ B ⊢k F A → 
                (Γ ,, A) ⊢c B' → 
                -----------------------------------
                Γ ◂ B ⊢k B' -}


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
        wkc (force v) = {!   !}
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
        csub γ (force v) = {!   !} 
        csub γ (rec× v m ) = rec× (vsub γ v) (csub (wksub (wksub γ)) m)
        csub γ (app m v) = app (csub γ m) (vsub γ v)
        csub γ (bind m m') = bind (csub γ m) (csub (wksub γ) m') 

        ksubCtx : {Γ Δ : Ctx}{B B' : CTy} → Sub[ Δ  , Γ ]  → Γ ◂ B ⊢k B' → Δ ◂ B ⊢k B' 
        ksubCtx γ varc = varc
        ksubCtx γ (∙V v k) = (∙V (vsub γ v) (ksubCtx γ k) )
        ksubCtx γ (x←∙:M k m) = x←∙:M (ksubCtx γ k) (csub (wksub γ) m)

    compsub : {Γ Δ Θ : Ctx} → Sub[ Γ , Δ ] → Sub[ Δ , Θ ] → Sub[ Γ , Θ ]
    compsub γ δ i = vsub γ (δ i)

    open import Cubical.Data.Sigma
    projC : {Γ Δ : Ctx}{A : VTy} → Sub[ Δ , (Γ ,, A) ] → Sub[ Δ , Γ ] × (Δ ⊢v A) 
    projC γ = (λ i → γ (suc i)) , γ zero

    pairC  : {Γ Δ : Ctx}{A : VTy} → Sub[ Δ , Γ ] × (Δ ⊢v A) → Sub[ Δ , (Γ ,, A) ] 
    pairC (γ , a) zero = a
    pairC (γ , a) (suc i) = γ i


    mutual 

        lem : {Γ : Ctx}{B : CTy}{A : VTy}{m : (Γ ,, A) ⊢c B} → csub (wksub idsub) m ≡ m
        lem = {! wksub idsub  !}
        
        csubid : {Γ : Ctx}{B : CTy}{m : Γ ⊢c B} → csub idsub m ≡ m
        csubid {m = ret x} = cong ret vsubid
        csubid {m = lam m} = cong lam lem
        csubid {m = force v} = {!   !}
        csubid {m = app m x} =  {!   !} --cong₂ app csubid vsubid
        csubid {m = rec× x m} = {!   !} -- cong₂ rec× vsubid {!   !}
        csubid {m = bind m m₁} = {!   !} -- cong₂ bind csubid lem

        vsubid : {Γ : Ctx}{A : VTy}{v : Γ ⊢v A} → vsub idsub v ≡ v
        vsubid {v = var i} = refl
        vsubid {v = u} = refl
        vsubid {v = pair v v₁} = cong₂ pair vsubid vsubid
        vsubid {v = thunk x} = cong thunk csubid

    compsubid : {Γ Δ : Ctx}{γ : Sub[ Γ , Δ ]} → compsub idsub γ ≡ γ
    compsubid  = funExt λ _ → vsubid

    
    -- Levy book 221
    scomp : {Γ : Ctx}{B₁ B₂ B₃ : CTy}→ Γ ◂ B₁ ⊢k B₂ → Γ ◂ B₂ ⊢k B₃ → Γ ◂ B₁ ⊢k B₃ 
    scomp k varc = k
    scomp k (∙V v k') = ∙V v (scomp k k')
    scomp k (x←∙:M k' m) = x←∙:M (scomp k k') m

    _++_ : {Γ : Ctx}{B₁ B₂ B₃ : CTy}→  Γ ◂ B₂ ⊢k B₃ → Γ ◂ B₁ ⊢k B₂ → Γ ◂ B₁ ⊢k B₃
    _++_ k k' = scomp k' k

    -- pattern _∷_ k k' = scomp k k'

    data stack (Γ : Ctx) : CTy → CTy → Set where
        nil : {B : CTy} → stack Γ  B B 
        cons : {B₁ B₂ B₃ : CTy} → Γ ◂ B₁ ⊢k B₂ → stack Γ B₂ B₃ → stack Γ B₁ B₃ 

    hmm : (Γ : Ctx)(B B' : CTy) → stack Γ B B' → Γ ◂ B ⊢k B' 
    hmm Γ B .B nil = varc
    hmm Γ B B' (cons k s) = scomp k (hmm Γ _ B' s)

    plug : {Γ : Ctx}{B B' : CTy} → Γ ◂ B ⊢k B' → Γ ⊢c B → Γ ⊢c B' 
    plug varc m = m
    plug (∙V v k) m = app (plug k m) v 
    plug (x←∙:M k x) m = bind (plug k m) x

        {- 
        
    -}
    ex : ⊘ ◂ fun one (F one) ⊢k F one 
    ex = x←∙:M (x←∙:M (∙V  u varc) (ret u)) (ret u)

    ex'  = plug ex (lam (ret (var zero)))

    pattern  _>>=λx,_ M k = bind M k

    _ : ex' ≡ (app (lam (ret (var zero))) u >>=λx, ret u) >>=λx, ret u 
    _ = refl



    scompid : {Γ : Ctx}{B B' : CTy}{k : Γ ◂ B ⊢k B'} → k ≡ scomp varc k
    scompid {k = varc} = refl
    scompid {k = ∙V x k} = cong₂ ∙V refl scompid
    scompid {k = x←∙:M k x} = cong₂ x←∙:M scompid refl

    -- scomp (scomp k₁ k₂) k₃ ≡ scomp k₁ (scomp k₂ k₃)
    scompseq : {Γ : Ctx}{B₁ B₂ B₃ B₄ : CTy}
        {k₁ : Γ ◂ B₁ ⊢k B₂}
        {k₂ : Γ ◂ B₂ ⊢k B₃}
        {k₃ : Γ ◂ B₃ ⊢k B₄} → 
        scomp (scomp k₁ k₂) k₃ ≡ scomp k₁ (scomp k₂ k₃)
    scompseq {k₃ = varc} = refl
    scompseq {Γ}{B₁}{B₂}{B₃}{B₄}{k₁}{k₂}{k₃ = ∙V {A = A} x k₃} = cong₂ ∙V refl (scompseq {Γ}{B₁}{B₂}{B₃}{fun A B₄}{k₁}{k₂}{k₃})
    scompseq {Γ}{B₁}{B₂}{B₃}{B₄}{k₁}{k₂}{k₃ = x←∙:M {A = A} k₃ x} = cong₂ x←∙:M  (scompseq{Γ}{B₁}{B₂}{B₃}{F A}{k₁}{k₂}{k₃}) refl

    ksubid : {Γ : Ctx}{B B' : CTy}{k : Γ ◂ B ⊢k B'} → ksubCtx idsub k ≡ k
    ksubid {k = varc} = refl
    ksubid {k = ∙V x k} = cong₂ ∙V vsubid ksubid
    ksubid {k = x←∙:M k x} = cong₂ x←∙:M ksubid lem

    mutual 
        vsubseq : {Γ Δ θ : Ctx}{A : VTy}{γ : Sub[ Γ  , Δ ]}{δ : Sub[ Δ , θ ]}{v : θ ⊢v A} → 
            vsub γ (vsub δ v) ≡ vsub (compsub γ δ) v
        vsubseq {v = var i} = refl
        vsubseq {v = u} = refl
        vsubseq {v = pair v v₁} = cong₂ pair {!   !} {!   !} 
        vsubseq {v = thunk x} = cong thunk csubseq

        csubseq : {Γ Δ θ : Ctx}{B : CTy}{γ : Sub[ Γ  , Δ ]}{δ : Sub[ Δ , θ ]}{m : θ ⊢c B} → 
            csub γ (csub δ m) ≡ csub (compsub γ δ) m
        csubseq {m = ret x} = cong ret {! vsubseq    !}
        csubseq {m = lam m} =  cong lam {!   !}
        csubseq {m = force v} =  {!   !} -- cong lam {!   !}

        csubseq {m = app m x} = {!   !} -- cong₂ app csubseq {!   !}
        csubseq {m = rec× x m} = {!   !}
        csubseq {m = bind m m₁} = {!   !}

        ksubseq : {Γ Δ θ : Ctx}{B B' : CTy}{γ : Sub[ Γ  , Δ ]}{δ : Sub[ Δ , θ ]}{k : θ ◂ B ⊢k B' }→ 
            ksubCtx γ (ksubCtx δ k) ≡ ksubCtx (compsub γ δ) k 
        ksubseq {k = varc} = refl
        ksubseq {k = ∙V x k} = {!   !} --  cong₂ ∙V vsubseq ksubseq
        ksubseq {k = x←∙:M k x} = cong₂ x←∙:M ksubseq {! csubseq  !}

        compsubseq : {Γ Δ Θ ξ : Ctx} → (γ : Sub[ Γ , Δ ])(δ : Sub[ Δ , Θ ])(ρ : Sub[ Θ , ξ ]) → 
            compsub (compsub γ δ) ρ ≡ compsub γ (compsub δ ρ)
        compsubseq {Γ}{Δ}{Θ}{ξ} γ δ ρ = funExt λ x → vsubseq{Γ}{Δ}{Θ}{{!   !}}{γ}{δ}{{!  !}}

    open import Cubical.Data.Sigma

            
  --      sret : {A : VTy}{v : ⊘ ⊢v A} → ret v ↦ {!   !}

-- stack machine semanticss

{-
    -- data config : Ctx → 

{-
            x←∙:M : {Γ : Ctx}{A : VTy}{B B' : CTy} →
                Γ ◂ B ⊢k F A → 
                (Γ ,, A) ⊢c B' →  
-}
    config : CTy → CTy → Set 
    config B B' = ⊘ ⊢c B × stack ⊘ B B'

    {- 
       Γ  M B  K B'

       note Γ and B' are constant during execution
        we have a computation 
            Γ ⊢c M : B
        and
            Γ ◂ B ⊢ K : B' 
    -}
    -- fix gamma too ?
    data step' (R : CTy) : {B B' : CTy} → ⊘ ⊢c B → ⊘ ◂ B ⊢k R → ⊘ ⊢c B' → ⊘ ◂ B' ⊢k R → Set where 
        s-ret : {A : VTy}{v : ⊘ ⊢v A}{N : (⊘ ,, A) ⊢c R}{k : ⊘ ◂ F A ⊢k F A}{k' : ⊘ ◂ R ⊢k R } → 
            -- ret v : F A 
            -- then we need a stack F A ⊢k R 

            -- for the return 
            -- N[v/x] : R 
            -- so we need a stack R ⊢k R
                step' R (ret v) (scomp {!   !} (x←∙:M varc  N)) (csub (λ { zero → v}) N) k' 
            --step' R (ret v) (x←∙:M {!  k' !} N) (csub (λ { zero → v}) N) k' 
           -- step' R (ret v) (x←∙:M varc N) (csub {! (x←∙:M varc N)  !} N) {!   !} 

     --   s-ret' : {A : VTy}{B B' : CTy}{v : ⊘ ⊢v A}{N : (⊘ ,, A) ⊢c B}{k : ⊘ ◂ F A ⊢k B } →
     --      step' (ret v) {!   !} (csub (λ { zero → v}) N) {!   !} 
           -- step' (ret v) (scomp k (x←∙:M  {!   !} {!   !})) {!   !} k

    data step : {B₁ B₂ B₃ B₄ : CTy} → config B₁ B₂ → config B₃ B₄ → Set where 
        s-ret : {A : VTy}{B B' : CTy}{v : ⊘ ⊢v A} →
                {k : ⊘ ◂ F A ⊢k B }{N : (⊘ ,, A) ⊢c B}{s : stack ⊘ B B' } →  
                step (ret v , cons (x←∙:M  varc  N) s) (csub (λ { zero → v}) N , s)  
                -- k is not used..

        s-ft : {B B' : CTy}{m : ⊘ ⊢c B }{s : stack ⊘ B B' } → 
            step (force (thunk m) , s) (m , s) 

        
 -}