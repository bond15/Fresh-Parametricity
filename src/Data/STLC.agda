{-# OPTIONS --allow-unsolved-metas #-} 
module src.Data.STLC where



    open import Cubical.Data.Unit 
    open import Cubical.Data.Bool hiding (_≤_)
    open import Cubical.Data.Sigma

    open import Cubical.Data.List 
   -- open import Cubical.Data.Fin renaming (elim to felim)
    open import Cubical.Data.Nat
    --open import Cubical.Data.FinData.Base renaming (Fin to FinData) hiding (¬Fin0 ; toℕ)
    open import Cubical.Data.Fin.Recursive
    open import Agda.Builtin.FromNat renaming (Number to HasFromNat)
    open import Cubical.Data.Nat.Order.Recursive 
    open import Cubical.Foundations.Prelude
    open import Cubical.Foundations.HLevels

{-
    instance
        fromNatFin : {n : _ } → HasFromNat (Fin n)
        fromNatFin {n} = record { 
            Constraint = λ m → m < n ; 
            fromNat = λ m ⦃ m<n ⦄ → toFin< m m<n}
-}

    _∘s_ : {A B C : Set} → (A → B) → (B → C) → A → C 
    _∘s_ f g = λ z → g (f z)
    
    <suc : {n : ℕ} → n < suc n 
    <suc {zero} = tt
    <suc {suc n} = ≤-refl n
    
    iS : {n : ℕ} → Fin n → Fin (suc n)
    iS {n = n} = inject< (<suc {n})
    
    data U : Set where 
        unit bool : U
        prod arr : U → U → U


    _ = isSetBool
    isSetU : isSet U 
    isSetU = {!   !}

    El : U → Set 
    El unit = Unit 
    El bool = Bool
    El (arr x y) = El x → El y
    El (prod x y) = El x × El y

    isSetEl : (u : U) → isSet (El u)
    isSetEl unit = isSetUnit
    isSetEl bool = isSetBool
    isSetEl (prod t1 t2) = isSet× (isSetEl t1) (isSetEl t2)
    isSetEl (arr t1 t2) = isSet→ (isSetEl t2)

    Ctx : Set
    Ctx = Σ[ n ∈ ℕ ] (Fin n → U)

    isSetCtx : isSet Ctx 
    isSetCtx = isSetΣ isSetℕ λ x → isSet→ isSetU

    -- \o/ 
    ⊘ : Ctx 
    ⊘ = 1 , λ _ → unit

    gen : {n : ℕ} → (Fin n → U) → U
    gen {zero} f = unit -- won't happen
    gen {suc zero} f = f (toFin 0)
    gen {suc n} f = prod (f (toFin n)) (gen (iS ∘s f))

    genList : {n : ℕ} → (Fin n → U) → List U
    genList {zero} f = []
    genList {suc zero} f = (f (toFin 0)) ∷ []
    genList {suc n} f = (f (toFin n)) ∷ (genList (iS ∘s f))

    ctxToU : Ctx → U 
    ctxToU (n , f) = gen f

    ctxToList : Ctx → List U 
    ctxToList (n , f) = genList f

    update : {n : ℕ}→ (Fin n → U) → U → (Fin (suc n) → U)
    update {n} f u zero = u
    update {n} f u (suc x) = f x

    update' : Ctx → U → Ctx 
    update' (n , f) u = (suc n) , (update f u)
    
    ctxFromList : List U → Ctx 
    ctxFromList [] = 1 , λ _ → unit
    ctxFromList (x ∷ []) = 1 , (λ _ → x)
    ctxFromList (x ∷ xs) = update' (ctxFromList xs) x

    elCtx : Ctx → Set 
    elCtx (n , γ) = (i : Fin n) → El (γ i)

    elCtx' : Ctx → Set
    elCtx' c = El (ctxToU c)


    open import Cubical.Foundations.Isomorphism
    open import Cubical.Data.Empty
    {-}
    lemma : (Γ : Ctx) → Iso (elCtx Γ) (elCtx' Γ) 
    lemma (zero , f) = iso (λ _ → tt) (λ{ tt → λ ()}) (λ _ → isPropUnit _ _) λ _  → funExt λ ()
    lemma (suc n , f) = iso (λ x → {!   !}) {!   !} {!   !} {!   !} where 
        bkwd : elCtx' (suc n , f) → elCtx (suc n , f) 
        bkwd x i = {! gen {suc n} f  !} where 
            _ : El (gen f)
            _ = x

            _ : gen {suc n} f ≡ f i 
            _ = {! refl  !}
    -}
    
    -- include eliminators?
    data _⊢_ : Ctx → U → Set where 
        u : {Γ : Ctx} → El unit → Γ ⊢ unit
        b : {Γ : Ctx} → El bool → Γ ⊢ bool 
        pair : {Γ : Ctx}{t1 t2 : U} → Γ ⊢ t1 → Γ ⊢ t2 → Γ ⊢ (prod t1 t2)
        fun : {Γ : Ctx}{t1 t2 : U} → (El t1 → Γ ⊢ t2) → Γ ⊢ (arr t1 t2)
        app :  {Γ : Ctx}{t1 t2 : U} → Γ ⊢ (arr t1 t2) → Γ ⊢ t1 → Γ ⊢ t2
        var : {(n , Γ) : Ctx} → (i : Fin n) → (n , Γ) ⊢ (Γ i)

    isSetTerm : {Γ : Ctx}{A : U} → isSet (Γ ⊢ A)
    isSetTerm {Γ}{A} = {!   !}
        
    record CtxMap (Γ Δ : Ctx): Set where
        field 
            terms : (i : Fin (Δ .fst)) → Γ ⊢ (Δ .snd i)
    open CtxMap 

    isSetCtxMap : {Γ Δ : Ctx} → isSet (CtxMap Γ Δ)
    isSetCtxMap =  {!   !}

    ≡CtxMap : {Γ Δ : Ctx} {f g : CtxMap Γ Δ} → (f .terms ≡ g .terms) → f ≡ g 
    ≡CtxMap  prf i = record { terms = prf i }

    idCtxMap : {Γ : Ctx} → CtxMap Γ Γ 
    idCtxMap = record { terms = var }

    sub : {Γ Δ : Ctx}{A : U} → CtxMap Γ Δ → Δ ⊢ A → Γ ⊢ A 
    sub f (u x) = u x
    sub f (b x) = b x
    sub f (pair x y) = pair (sub f x) (sub f y)
    sub f (fun x) = fun λ e → sub f (x e)
    sub f (app x y) = app (sub f x) (sub f y)
    sub f (var i) = f .terms i

    subId : {Γ : Ctx}{A : U}{M : Γ ⊢ A} → sub {Γ}{Γ}{A} idCtxMap M ≡ M
    subId {M = u x} = refl
    subId {M = b x} = refl
    subId {M = pair M M₁} = cong₂ pair (subId {M = M}) (subId {M = M₁})
    subId {M = fun x} = cong fun (funExt λ e → subId {M = x e})
    subId {M = app M M₁} = cong₂ app (subId {M = M}) (subId {M = M₁})
    subId {M = var i} = refl

    seqCtxMap : {Γ Δ Θ : Ctx} → CtxMap Γ Δ → CtxMap Δ Θ → CtxMap Γ Θ 
    seqCtxMap f record { terms = g } = 
        record { terms = λ i → sub f (g i) }

    subSeq : {Γ Δ Θ : Ctx}{A : U}{f : CtxMap Γ Δ}{g : CtxMap Δ Θ} →
        (M : Θ ⊢ A) →  
        sub (seqCtxMap f g) M ≡ sub f (sub g M)
    subSeq (u x) = refl
    subSeq (b x) = refl
    subSeq (pair M M₁) = cong₂ pair (subSeq M) (subSeq M₁)
    subSeq (fun x) = cong fun (funExt λ e → subSeq (x e))
    subSeq (app M M₁) = cong₂ app (subSeq M) (subSeq M₁)
    subSeq (var i) = refl

    module examplemap where 
        Γ : Ctx 
        Γ = 3 , λ { zero → bool
                  ; (suc zero) → arr unit bool
                  ; (suc (suc zero)) → unit}

        Δ : Ctx 
        Δ = 4 , λ { zero → bool
                  ; (suc zero) → bool
                  ; (suc (suc zero)) → bool 
                  ; (suc (suc (suc zero))) → bool}

        Γ→Δ : CtxMap Γ Δ 
        Γ→Δ = record { terms = 
            λ{ zero → var (iS (iS (toFin 0)))
             ; (suc zero) → app (var (iS (toFin 1))) (var (toFin 2))
             ; (suc (suc zero)) → b true
             ; (suc (suc (suc zero))) → b false }}

    -- terms that dont use the context
    pure : {Γ : Ctx}{ty : U} → El ty → Γ ⊢ ty 
    pure {Γ}{unit} x = u x
    pure {Γ}{bool} x = b x
    pure {Γ}{prod ty ty₁} (x , y) = pair (pure x) (pure y)
    pure {Γ}{arr ty ty₁} f = fun λ x → pure (f x)


    -- similar to Coqs Program command (proof of equality on match is brought into context)
    module _ {a b} {A : Set a} {B : A → Set b} where

        data Graph (f : ∀ x → B x) (x : A) (y : B x) : Set b where
            ingraph : f x ≡ y → Graph f x y

        inspect : (f : ∀ x → B x) (x : A) → Graph f x (f x)
        inspect _ _ = ingraph refl

    closedTerm : {Γ : Ctx}{t : U} → (M : Γ ⊢ t) → elCtx Γ → ⊘ ⊢ t
    closedTerm {n , Γ} {.unit} (u x) γ = u x
    closedTerm {n , Γ} {.bool} (b x) γ = b x
    closedTerm {n , Γ} {_} (pair x y) γ = pair (closedTerm x γ) (closedTerm y γ) 
    closedTerm {n , Γ} {_} (fun f) γ = fun λ x → closedTerm (f x) γ
    closedTerm {n , Γ} {_} (app f x) γ = app (closedTerm f γ) (closedTerm x γ)
    -- Heres where we eliminate variables using the context
    closedTerm {n , Γ} {.(Γ i)} (var i) γ with (Γ i) | inspect Γ i
    closedTerm {n , Γ} {.(Γ i)} (var i) γ | unit | ingraph p = pure (subst El p (γ i))
    closedTerm {n , Γ} {.(Γ i)} (var i) γ | bool | ingraph p = pure (subst El p (γ i))
    closedTerm {n , Γ} {.(Γ i)} (var i) γ | prod t1 t2 | ingraph p  = pure (((subst El p (γ i)) .fst) , ((subst El p (γ i)) .snd))
    closedTerm {n , Γ} {.(Γ i)} (var i) γ | arr t1 t2 | ingraph p = pure (subst El p (γ i))  
 
    module testing where 
        c1 : Ctx 
        c1 = 1 , (λ{zero → bool})

        c2 : Ctx 
        c2 = 2 , (λ{zero → bool
                ; (suc zero) → prod unit unit})

        c3 : Ctx 
        c3 = 3 , (λ{zero → bool
                ; (suc zero) → prod unit unit
                ; (suc (suc zero)) → arr unit bool})

        c4 : Ctx 
        c4 = 4 , (λ{zero → bool
                ; (suc zero) → prod unit unit
                ; (suc (suc zero)) → arr unit bool
                ; (suc (suc (suc zero))) → arr bool bool})

        t1 : ctxToU c1 ≡ bool 
        t1 = refl

        t2 : ctxToU c2 ≡ prod (prod unit unit) bool
        t2 = refl

        t3 : ctxToU c3 ≡ prod (arr unit bool) (prod (prod unit unit) bool) 
        t3 = refl

        t4 : ctxToU c4 ≡ prod (arr bool bool) (prod (arr unit bool) (prod (prod unit unit) bool)) 
        t4 = refl

        l1 : List U 
        l1 = bool ∷ []

        l2 : List U 
        l2 = bool ∷ (prod unit unit) ∷ []
        
        l3 : List U 
        l3 = bool ∷ (prod unit unit) ∷ (arr unit bool) ∷ []

        l4 : List U 
        l4 = bool ∷ (prod unit unit) ∷ (arr unit bool) ∷ (arr bool bool) ∷ []

        t5 : ctxToU (ctxFromList l1) ≡ bool
        t5 = refl

        t6 : ctxToU (ctxFromList l2) ≡ prod (prod unit unit) bool
        t6 = refl

        t7 : ctxToU (ctxFromList l3) ≡ prod (arr unit bool) (prod (prod unit unit) bool)
        t7 = refl

        t8 : ctxToU (ctxFromList l4) ≡ prod (arr bool bool)(prod (arr unit bool) (prod (prod unit unit) bool))
        t8 = refl

        t9 : elCtx c4
        t9 zero = true
        t9 (suc zero) = tt , tt
        t9 (suc (suc zero)) = λ{ tt → false}
        t9 (suc (suc (suc zero))) = not

        _ : ctxToList c4 ≡ arr bool bool ∷ arr unit bool ∷ prod unit unit ∷ bool ∷ []
        _ = refl

        term1 : c4 ⊢ arr bool (prod (arr bool bool) (arr unit bool)) 
        term1 = fun λ b → pair (var (toFin 3)) (var (iS (toFin 2)))

        -- wtf.. it works
        _ : (closedTerm {c4} term1 t9) ≡ fun (λ x → pair (fun λ b → _⊢_.b (not b)) (fun (λ x₁ → b false))) 
        _ = refl



{- 



    module _ (g : ℕ → Bool) where

        data _⊢'_ : Ctx → U → Set where 
            u : {Γ : Ctx} → El unit → Γ ⊢' unit
            b : {Γ : Ctx} → El bool → Γ ⊢' bool 
            pair : {Γ : Ctx}{t1 t2 : U} → Γ ⊢' t1 → Γ ⊢' t2 → Γ ⊢' (prod t1 t2)
            fun : {Γ : Ctx}{t1 t2 : U} → (El t1 → Γ ⊢' t2) → Γ ⊢' (arr t1 t2)
            var : {(n , Γ) : Ctx} → (i : Fin n) → (n , Γ) ⊢' (Γ i)
            ite : {Γ : Ctx}{A : U} → Γ ⊢' bool → Γ ⊢' A → Γ ⊢' A →  Γ ⊢' A
            pi1 : {Γ : Ctx}{A B : U} → Γ ⊢' (prod A B) → Γ ⊢' A 
            pi2 : {Γ : Ctx}{A B : U} → Γ ⊢' (prod A B) → Γ ⊢' B

            hmm : {Γ : Ctx}{A B : U} → (p :  Γ ⊢' (prod A B)) → 
                p ≡ pair (pi1 p) (pi2 p)

 
        what : ⊘ ⊢' bool → ℕ
        what (b x) = {!   !}
        what (ite t t₁ t₂) = {!   !}
        what (pi1 t) = {!   !}
        what (pi2 t) = {!   !}

        what' : {Γ : Ctx}{A : U}→  Γ  ⊢' A → ℕ
        what' (u x) = {!   !}
        what' (b x) = {!   !}
        what' (pair t t₁) = 0
        what' (fun x) = {!   !}
        what' (var i) = {!   !}
        what' (ite t t₁ t₂) = {!   !}
        what' (pi1 t) = 0
        what' (pi2 t) = 0
        what' (hmm t i) = {!  0 !}





        -- is this cheating the syntax?
        _ : ⊘ ⊢ bool 
        _ = b (g 9)

        _ : ⊘ ⊢ bool 
        _ = {! fun   !}
-}


 --   ctxToU : Ctx → U 
 --   ctxToU (zero , f) = unit
 --   ctxToU (suc n , f) = prod {!   !} (ctxToU (n , (injectSuc ∘s f)))

{- 
-- summation
sumFinGen : ∀ {ℓ} {A : Type ℓ} {n : ℕ} (_+_ : A → A → A) (0A : A) (f : Fin n → A) → A
sumFinGen {n = zero} _+_ 0A f = 0A
sumFinGen {n = suc n} _+_ 0A f = f flast + sumFinGen _+_ 0A (f ∘ injectSuc)
-}

{-
    comparing alternative definitions of Fin 


    -- Cubical.Data.Fin.Recursive does support nice functions
    -- and no indexed match
    foo : FinR 3 → U 
    foo zero = unit
    foo (suc zero) = prod unit bool
    foo (suc (suc zero)) = arr bool bool

    -- Cubical.Data.Fin
    -- not as nice to define functions on...
   -- foo : Fin 2 → U 
    --foo x = {!   !}

    
    Ctx : Set
    Ctx = Σ[ n ∈ ℕ ] (FinData n → U)
    -- indexed match not supported in cubical agda, transports won't compute
    foo : FinData 3 → U 
    foo zero = {!   !} 
    foo one = {!   !}
    foo two = {!   !}

    ctx : Ctx 
    ctx = 3 , foo
    
-}
