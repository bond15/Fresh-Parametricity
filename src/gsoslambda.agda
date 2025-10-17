module src.gsoslambda where
    --open import Cubical.Categories.Presheaf.Base
   -- open import Cubical.Categories.Category 
   -- open Category hiding (_∘_)
    open import Cubical.Data.Nat hiding(_^_)
    open import Cubical.Foundations.HLevels hiding (extend)
    open import Cubical.Data.FinData
    open import Cubical.Foundations.Prelude 
   -- open import Cubical.Categories.Functor
   -- open Functor
    open FinSumChar renaming (inv to invFin; fun to funFin)
   -- open import Cubical.Categories.NaturalTransformation
   -- open Cubical.Categories.NaturalTransformation.NatTrans 
    open import Cubical.Data.Sum renaming (rec to rec⊎ ; map to map⊎)
    open import Cubical.Data.Sigma 
   -- open import Cubical.Categories.Instances.FunctorAlgebras

    _∘_ : {A B C : Set} → (B → C) → (A → B) → A → C 
    _∘_ g f = λ z → g (f z)

    -- presheaf 
    record Pre : Set₁ where 
        constructor mkPre
        field 
            Pob : ℕ → Set 
            Pmap : {n m : ℕ} → (f : Fin n → Fin m) → Pob n → Pob m

    open Pre
   -- ^op : Pre → Pre 
   -- ^op P .Pob = P .Pob
   -- ^op P .Pmap = {!   !}
    
    -- nat trans 
    record PreMor (P Q : Pre) : Set₁ where 
        private module P = Pre P 
        private module Q = Pre Q
        field 
            α : ∀ (n : ℕ) → P.Pob n → Q.Pob n
         --   square : {n m : ℕ} → (f : Fin n → Fin m) → Q.Pmap f ∘ α n ≡ (α m ∘ P.Pmap f)
    open PreMor

    _∘P_ : {P Q R : Pre} → PreMor Q R → PreMor P Q → PreMor P R
    _∘P_ {P}{Q}{R} N M .α n = λ z → α N n (α M n z)

    -- endofunctor on presheaf cat
    record Fun : Set₁ where 
        field 
            Obj : Pre → Pre 
            Mor : {P Q : Pre} → PreMor P Q → PreMor (Obj P) (Obj Q)


    open Pre 
    open PreMor 
    open Fun

    Var : Pre 
    Var = mkPre Fin (λ x → x)


    extend : {n m : ℕ} → (Fin n → Fin m) → Fin (suc n) → Fin (suc m)
    extend {n}{m} f x = funFin 1 m (rec⊎ inl (λ y → inr (f y)) (invFin  1 n x))

    δ : Fun 
    δ .Obj P .Pob n = P .Pob (suc n)
    δ .Obj P .Pmap {n}{m} f = P. Pmap (extend f)
    δ .Mor {P} {Q} N .α n = N .α (suc n)
  --  δ .Mor {P} {Q} N .square f = funExt λ{x  → {!   !}}


    _+Pre_ : Pre → Pre → Pre 
    _+Pre_ P Q .Pob n = Pob P n ⊎ Pob Q n
    (P +Pre Q) .Pmap f (inl x) = inl (Pmap P f x)
    (P +Pre Q) .Pmap f (inr x) = inr (Pmap Q f x)

    _×Pre_ : Pre → Pre → Pre 
    _×Pre_ P Q .Pob n = Pob P n × Pob Q n
    _×Pre_ P Q .Pmap f (x , y) = (Pmap P f x) , (Pmap Q f y)

   -- ΛSig : Fun 
  --  ΛSig .Obj X = Var +Pre (δ .Obj X  +Pre (X ×Pre X))
   -- ΛSig .Mor {P} {Q} f .α n = map⊎ (λ x → x) (map⊎ (f .α (suc n)) λ {(x , y) → f .α n  x , f .α n y})

    -- signature as a data type
    mutual 
        data S (X : Pre )(n : ℕ): Set where 
            vars : Fin n → S X n 
            lam : X .Pob (suc n) → S X n
            app : X .Pob n → X .Pob n → S X n -- applicaiton ..?

        ΛSig : Fun 
        ΛSig .Obj X .Pob = S X
        ΛSig .Obj X .Pmap f (vars x) = vars (f x)
        ΛSig .Obj X .Pmap f (lam x) = lam (Pmap X (extend f) x)
        ΛSig .Obj X .Pmap f (app x x₁) = app (Pmap X f x₁) (Pmap X f x₁)
        ΛSig .Mor f .α n (vars x) = vars x
        ΛSig .Mor f .α n (lam x) = lam (α f (suc n) x)
        ΛSig .Mor f .α n (app Pn Pn') = app (α f n Pn') (α f n Pn')


    mutual
        {-# NO_POSITIVITY_CHECK #-}
        data μ  (F : Fun)(n : ℕ): Set where 
            inn : F .Obj (μPre F) .Pob n → μ F n
            
        {-# TERMINATING #-}
        μPre : Fun → Pre 
        μPre F .Pob = μ F
        μPre F .Pmap {n}{m} f = goal where 

            P = F .Obj (μPre F)

            goal' : P .Pob n → P .Pob m
            goal'  = P .Pmap f
            
            goal : μ F n → μ F m
            goal (inn x) = inn (goal' x)

    mutual 
        {-# NO_POSITIVITY_CHECK #-}
        data Free (F : Fun) (X : Pre)(n : ℕ) : Set where 
            var : X .Pob n → Free F X n
            op : F .Obj (FreeP F X) .Pob n → Free F X n
       
        {-# TERMINATING #-}
        FreeP : Fun → Pre → Pre 
        FreeP F P .Pob = Free F P
        FreeP F P .Pmap f (var x) = var (Pmap P f x) -- renaming
        FreeP F P .Pmap f (op x) = op (Pmap (Obj F (FreeP F P)) f x)
        

    Fam : Pre → Pre → ℕ → Set 
    Fam X Y m = ∃[ n ∈ ℕ ] X .Pob n × (Fin n → Y .Pob m)


    -- quotient this
    data End (X Y : Pre) (m : ℕ) : Set where 
        elem : Fam X Y m → End X Y m
        

    -•_ : Pre → Fun 
    -•_ Y .Obj X = Z where 
        Z : Pre 
        Z .Pob m = ∃[ n ∈ ℕ ] {!   !}
        Z .Pmap = {!   !}
    -•_ Y .Mor = {!   !}

    
    Lam : Pre 
    Lam = μPre ΛSig
    module examples where 
        {-

        _ = {! Lam .Pmap  !}
        
        -- 3 variables
        ty₃ : Set 
        ty₃ = Lam .Pob 3
        


        -- here we did a lambda abstraction so we could use another variable
        _ : ty₃ 
        _ = inn (lam (inn (vars (fromℕ 3))))

        ty₂ : Set 
        ty₂ = Lam .Pob 2

        e' : ty₂ 
        e' = inn  (vars zero)

        sub : (Fin 3 → Fin 2) → ty₃ → ty₂ 
        sub γ = Lam .Pmap γ

        γ : Fin 3 → Fin 2 
        γ zero = one
        γ one = zero
        γ two = one

        γ' : Fin 2 → Fin 3 
        γ' zero = one 
        γ' one = two

        e : ty₃ 
        e = inn (app (inn (vars one)) (inn (vars zero)))
        -- something is off
        _ : sub γ e ≡ inn (app (inn (vars one)) (inn (vars one))) 
        _ = refl

        _ : Lam .Pmap γ' e' ≡ inn (vars one)
        _ = refl


        data V₃ : Set where 
            a b c : V₃ 

        V₃' : Pre 
        V₃'  .Pob _ = V₃
        V₃' .Pmap = λ f z → z

        -- metavariables and variables distinction..
        Lam' : Pre 
        Lam' = FreeP ΛSig V₃'

        ty' : Set 
        ty' = Lam' .Pob 3 
        
        _ : ty' 
        _ = var b

        _ : ty' 
        _ = op (vars (suc zero))
-}

    record Alg (F : Fun) : Set₁ where 
        field 
            car : Pre 
            alg : PreMor (F .Obj car) car

    open Alg

    record AlgHom {F : Fun}(A B : Alg F) : Set₁ where 
        private module A = Alg A 
        private module B = Alg B
        field 
            algmap : PreMor A.car B.car 
          --  comm : (B.alg ∘P Mor F algmap) ≡ (algmap ∘P A.alg)

    open AlgHom 
    
    module _ {F : Fun}{X : Pre} where 
        freeAlg : Alg F 
        freeAlg .car = FreeP F X
        freeAlg .alg .α n = op

        {-# TERMINATING #-}
        freeHom : {A : Alg F} → PreMor X (car A) → AlgHom freeAlg A 
        freeHom {A} f .algmap = h* where 
            private module A = Alg A
        
            h* : PreMor (car freeAlg) (car A)
            h* .α n (var x) = α f n x
            h* .α n (op x) = A.alg .α n (Mor F h* .α n x)



    FreeF : Fun → Fun 
    FreeF F .Obj X = FreeP F X
    FreeF F .Mor {P}{Q} f = freeHom {F}{P}{freeAlg{F}{Q}} (record { α = λ n z → var (α f n z) }) .algmap

    -- ⟪ P , Q ⟫ 
    -- substitution of P-terms in m variables for the n variables of a fixed term, giving a Q term in m variables
    ⟪_,_⟫ : Pre → Pre → Pre
    ⟪_,_⟫ P Q .Pob n = (m : ℕ) → (Fin n → P .Pob m) → Q .Pob m -- is a PreHom , but inlining here to avoid size issues
    ⟪_,_⟫ P Q .Pmap {n}{n'} f g m v = g m (λ z → v (f z))


    record BiFun : Set₁ where 
        field 
            BObj : Pre → Pre → Pre 
            BMor : {P Q R S : Pre} → PreMor Q P → PreMor R S → PreMor (BObj P R) (BObj Q S)
    
    open BiFun

    -- \b1
    𝟙 : Pre 
    𝟙 .Pob n = Unit
    𝟙 .Pmap _ _ = tt

    Yo :  ℕ → Pre 
    Yo n .Pob m = Fin n → Fin m
    Yo n .Pmap f = λ z z₁ → f (z z₁)

    Exp : Pre → Pre → ℕ → Set 
    Exp P Q n = (m : ℕ) → (Fin n → Fin m) × P .Pob m → Q .Pob m

    _^_ : Pre → Pre → Pre 
    _^_ P Q .Pob n = Exp P Q n
    _^_ P Q .Pmap f p^qn m (g , Pm) = p^qn m ( g ∘ f  , Pm)

-- (Q +Pre ((Q ^ P) +Pre 𝟙)
    data Beh' (X Y : Pre) (n : ℕ ): Set where 
        step : Y .Pob n → Beh' X Y n     -- reduction step
        vlam : Exp X Y  n → Beh' X Y n   -- lambda abstraction
        stuck  : Beh' X Y n              -- stuck term

    record Behave (X Y : Pre) (n : ℕ) : Set where 
        constructor _◂_ 
        field 
            bb : Beh' X Y n
            subst' : (m : ℕ) → (Fin n → X .Pob m) → Y .Pob m

    -- auto filled most of this in
    -- idk what is going on here
    Beh : BiFun 
    Beh .BObj P Q = R where 
        R : Pre 
        R .Pob = Behave P Q
        R .Pmap f ((step x) ◂ s) = (step (Pmap Q f x))                                                      ◂ (λ m g → s m (g ∘ f))
        R .Pmap f ((vlam x) ◂ s) = (vlam (λ{m g → s m (λ _ → snd g)}))                                      ◂ (λ m g → s m (g ∘ f))
        R .Pmap f (stuck ◂ s) = stuck                                                                       ◂ (λ m g → s m (g ∘ f))
    Beh .BMor {P} {Q} {R} {S} f g .α n ((step x) ◂ s) = (step (α g n x))                                    ◂ (λ m z → α g m (s m (λ z₁ → α f m (z z₁))))
    Beh .BMor {P} {Q} {R} {S} f g .α n ((vlam x) ◂ s) = (vlam λ{k (h , Sk) → α g k (s k (λ _ → α f k Sk))}) ◂ (λ m z → α g m (s m (λ z₁ → α f m (z z₁))))
    Beh .BMor {P} {Q} {R} {S} f g .α n (stuck ◂ s) = stuck                                                  ◂ (λ m z → α g m (s m (λ z₁ → α f m (z z₁))))


    Q : {X Y : Pre} → PreMor (ΛSig .Obj (X ×Pre Beh .BObj X Y)) (Beh .BObj X (FreeP ΛSig (X +Pre Y))) 
    Q {X} {Y} .α n x = {!   !}


    
