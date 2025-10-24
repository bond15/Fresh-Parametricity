{-# OPTIONS --allow-unsolved-metas --guardedness #-}

module src.gsos where
    open import Cubical.Data.Unit
    open import Cubical.Data.Bool renaming (not to neg ; _and_ to _&&_; _or_ to _||_) hiding (_≤_)
    open import Cubical.Data.Sigma
    open import Cubical.Data.Empty
    open import Cubical.Data.Sum renaming (rec to rec⊎)
    open import Cubical.Foundations.Prelude hiding(_∧_;_∨_;subst)
    open import Cubical.Foundations.Isomorphism
    open Iso

    record Functor : Set₁ where  
        field 
            F₀ : Set → Set 
            F₁ : {X Y : Set}(f : X → Y) → F₀ X → F₀ Y 
    
    open Functor

    record Monad (F : Functor): Set₁ where 
        private module F = Functor F 
        field 
            η : {X : Set} → X → F.F₀ X
            join : {X  : Set}→  F.F₀ (F.F₀ X) → F.F₀ X

    open Monad
    _∘_ : {A B C : Set} → (B → C) → (A → B) → A → C 
    _∘_ g f = λ z → g (f z)

    record Alg (F : Functor) : Set₁ where  
        field  
            car : Set
            alg : (F .F₀) car → car 

    open Alg
    
    record AlgHom {F}(A B : Alg F) : Set₁ where 
        private module A = Alg A
        private module B = Alg B
        field 
            algmap : A.car → B.car
            comm : 
                (B.alg ∘ F .F₁ algmap) ≡ (algmap ∘ A.alg)


    open AlgHom

     -- Now for coalgebras 
    record Coalg (F : Functor) : Set₁ where  
        field  
            car : Set
            coalg : car → (F .F₀) car 

    open Coalg
    
    record CoalgHom {F}(A B : Coalg F) : Set₁ where 
        private module A = Coalg A
        private module B = Coalg B
        field 
            coalgmap : A.car → B.car
            comm : 
                ((F .F₁) coalgmap ∘  A.coalg) ≡ (B.coalg ∘ coalgmap)

    record NatTrans (F G : Functor) : Set₁ where 
        private module F = Functor F 
        private module G = Functor G 
        field
            α : ∀ (X : Set) → F.F₀ X → G.F₀ X
            square : ∀ {X Y : Set}(f : X → Y) → (G.F₁ f ∘ α X) ≡ (α Y ∘ F.F₁ f)
    open NatTrans

    {-# NO_POSITIVITY_CHECK #-}
    data μ (F : Functor) : Set where  
        ⟨_⟩ : (F₀ F) (μ F) → μ F

    un : {F : Functor} → μ F → (F₀ F) (μ F)
    un ⟨ x ⟩ = x

    record FreeSigAlg (F : Functor)(X : Set): Set₁ where 
        field 
            alg : Alg F
            η : X → Alg.car alg
            cond : {A : Alg F}{h : X → Alg.car A} → 
                ∃! (AlgHom alg A) λ h* → h ≡  (h* .algmap ∘ η)
    open FreeSigAlg

    -- Free Sigma algebra on an object X
    -- The object X is a set of metavariables
    {-# NO_POSITIVITY_CHECK #-}
    data Free (F : Functor) (X : Set) : Set where 
        var : X → Free F X 
        op : (F₀ F) (Free F X) → Free F X

    module _ {F : Functor}{X : Set} where 

        freeF : Alg F 
        freeF .car = Free F X
        freeF .alg x = op x 


        {-# TERMINATING #-}
        freeHom  : {A : Alg F}{h : X → car A} → AlgHom freeF A 
        freeHom {A} {h}.algmap = h* where 

            η' : X → Free F X
            η' x = var x

            h* : Free F X → car A 
            h* (var x) = h x -- renaming
            h* (op e) = (alg A) ((F₁ F) h* e) -- recursion

        freeHom {A} .comm = refl
        
        freeAlg : FreeSigAlg F X
        freeAlg .alg = freeF
        freeAlg .η x = var x
        freeAlg .cond {A} {h} = 
            uniqueExists 
                (freeHom {A}{h})
                refl -- h = h* ∘ ηₓ
                {!   !} 
                {!   !}
    
    FreeF : Functor → Functor 
    FreeF F .F₀ X = Free F X
    FreeF F .F₁ {X} {Y} f = -- renaming functor, f is used to map from variables X to Y
        freeHom {F}{X}{freeF {F}{Y} }{var ∘ f} .algmap 

    {-# TERMINATING #-}
    FreeM : {F : Functor} → Monad (FreeF F)
    FreeM .η = var
    FreeM {F} .join {X} = joinfree where 
        joinfree : Free F (Free F X) → Free F X
        joinfree (var x) = x -- 
        joinfree (op e) = op ((F₁ F) joinfree e)


    initial : {F : Functor} → Alg F
    initial {F} .car = μ F
    initial .alg = ⟨_⟩

    {-# TERMINATING #-}
    ! : {F : Functor}{A : Alg F} → AlgHom (initial {F}) A 
    ! {F} {A} .algmap  = recc where 
        recc = alg A ∘ (F₁ F recc ∘ un)
    ! .comm = refl

    -- a "closed" program is the same as just taking the fixpoint of the functor
    -- closed here is represented by the fact that the set used for variables ⊥ is empty
    fact : {F : Functor} → Iso (μ F) (Free F ⊥)  
    fact {F} = 
        iso 
            (! {F} {freeF {F}} .algmap)
            (freeHom {F}{⊥}{initial{F}}{λ()} .algmap) 
            (λ b → {! refl  !}) 
            λ a  → {!  refl !}

    _×F_ : Functor → Functor → Functor 
    _×F_ F G .F₀ X = F₀ F X × F₀ G X
    _×F_ F G .F₁ f (FX , GX) = F₁ F f FX , F₁ G f GX

    IdF : Functor 
    IdF .F₀ X = X 
    IdF .F₁ f x = f x

    _∘F_ : Functor → Functor → Functor 
    _∘F_ G F .F₀ X = (F₀ G) (F₀ F X)
    _∘F_ G F .F₁ f GFX = F₁ G (F₁ F f) GFX


    -- figure 8 bialgebr stateful 
    module generalRun 
        (Sig : Functor) 
        (B : Functor) 
        (Q : NatTrans (Sig ∘F (IdF ×F B)) (B ∘F FreeF Sig) ) where 


        private module B = Functor B
        private module Sig = Functor Sig
        private module Q = NatTrans Q

        {-# TERMINATING #-}
        γ : Coalg B 
        γ .car = μ Sig
        γ .coalg = run  where 
            run : μ Sig → B.F₀ (μ Sig) 
            run = ((B.F₁ (freeHom {Sig}{μ Sig}{initial {Sig}}{λ x → x} .algmap) ∘ Q.α (μ Sig)) ∘ Sig.F₁ (λ x → (x , run x))) ∘ un       

        -- closed terms, no metavars
        run : μ Sig → B.F₀ (μ Sig) 
        run = γ .coalg 

    module NatLang where 

        open import Cubical.Data.Nat 

        -- F X := ℕ + (X × X)
        data NatEx (X : Set) : Set where 
            const : ℕ → NatEx X 
            plus : X → X → NatEx X 

        -- F X := ℕ + X
        data NatBeh (X : Set) : Set where 
            done : ℕ → NatBeh X 
            step : X → NatBeh X


        NatF : Functor 
        NatF .F₀ = NatEx
        NatF .F₁ f (const x) = const x
        NatF .F₁ f (plus x y) = plus (f x) (f y)

        Nat : Set 
        Nat = μ NatF

        Natℬ : Functor 
        Natℬ .F₀ = NatBeh
        Natℬ .F₁ f (done x) = done x
        Natℬ .F₁ f (step x) = step (f x)
        
        NatQ : NatTrans (NatF ∘F (IdF ×F Natℬ)) (Natℬ ∘F FreeF NatF) 
        NatQ .α X = s where 
            s : NatEx (X × NatBeh X) → NatBeh (Free NatF X)
            s (const x)                             = done x
            s (plus (x , step x') (y , _))          = step (op (plus (var x') (var y))) -- reduce left
            s (plus (x , done n) (y , step y'))     = step (op (plus (var x) (var y'))) -- reduce right
            s (plus (x , done n) (y , done m))      = done (n + m)                      -- Not step ⟨ inl (const (n + m)) ⟩
        
    
        NatQ .square f = funExt λ{ (const x) → refl
                                 ; (plus (x , done n) (y , done m)) → refl
                                 ; (plus (x , done n) (y , step y')) → refl
                                 ; (plus (x , step x') (y , done m)) → refl
                                 ; (plus (x , step x') (y , step y')) → refl }


        open generalRun NatF Natℬ NatQ 
        -- Next, do the denotaitonal model, the dual
        -- see page 2 of Towards HOMOS

        {-# NO_POSITIVITY_CHECK #-}
        record ν (F : Functor) : Set where 
            coinductive 
            constructor ⟪_⟫
            field 
                 out : (F₀ F) (ν F)
        open ν 

        _ : {F : Functor} → ν F → F₀ F (ν F)
        _ = out

        _ : {F : Functor} → F₀ F (ν F) → ν F 
        _ = ⟪_⟫

        module generalDen
            (Sig : Functor) 
            (B : Functor) 
            (Q : NatTrans (Sig ∘F (IdF ×F B)) (B ∘F FreeF Sig) ) where 


            private module B = Functor B
            private module Sig = Functor Sig
            private module Q = NatTrans Q

            ρ : Alg Sig
            ρ .car = ν B
            ρ .alg = corun where 
                corun : Sig .F₀ (ν B) → ν B 
                corun = {!   !}
                    --({! ? ∘ Q .α (ν B)   !} ∘ Sig .F₁ (λ x → (x , x))) ∘ Sig .F₁ out
{-}
            {-# TERMINATING #-}
            et : Coalg B 
            γ .car = μ Sig
            γ .coalg = run  where 
                run : μ Sig → B.F₀ (μ Sig) 
                run = ((B.F₁ (freeHom {Sig}{μ Sig}{initial {Sig}}{λ x → x} .algmap) ∘ Q.α (μ Sig)) ∘ Sig.F₁ (λ x → (x , run x))) ∘ un       
-}
            -- closed terms, no metavars
      --      run : μ Sig → B.F₀ (μ Sig) 
      --      run = γ .coalg 


        
        record StreamF (X : Set) : Set where 
            constructor S
            field 
                str : Bool × X  
        open StreamF

        StF : Functor
        StF .F₀ = StreamF 
        StF .F₁ f (S (b , s)) = S (b , f s)
            
        Stream : Set 
        Stream = ν StF

        head : Stream → Bool 
        head s = s .out .str .fst

        tail : Stream → Stream 
        tail s = s .out .str .snd

        hrm : Stream 
        hrm .out .str = true , ⟪ S (false , hrm) ⟫
        
        _ : head (tail (tail hrm)) ≡ true
        _ = refl

        hm : ν Natℬ
        hm = ⟪ (step ⟪ (step ⟪ (done 7) ⟫) ⟫) ⟫

        
        
        module _ {F : Functor} where 
            
            final : Coalg F 
            final .car = ν F
            final .coalg = out




        num : ℕ → Nat 
        num n = ⟨ (const n) ⟩

        _⊹_ : Nat → Nat → Nat 
        m ⊹ n = ⟨ (plus m n) ⟩

        expr : Nat 
        expr = (num 3 ⊹ num 3) ⊹ num 8

        _ : run (num 8) ≡ done 8 
        _ = refl

        --_ : run (num 1 ⊹ num 1 ) ≡ step (num 2)
        --_ = refl

        _ : run expr ≡ done 14
        _ = refl

        _ : run (expr ⊹ (expr ⊹ expr)) ≡ done 42 
        _ = refl

    module BoolLang where 
        
                -- F X := ℕ ⊎ (X × X)
        data Sig (X : Set) : Set where 
            const : Bool → Sig X 
            and or : X → X → Sig X
            not : X → Sig X 

        -- F X := ℕ ⊎ X
        data B (X : Set) : Set where 
            done : Bool → B X 
            step : X → B X


        SigF : Functor 
        SigF .F₀ = Sig
        SigF .F₁ f (const x) = const x
        SigF .F₁ f (and x y) = and (f x) (f y)
        SigF .F₁ f (or x y) = or (f x) (f y)
        SigF .F₁ f (not x) = not (f x) 

        BExp : Set 
        BExp = μ SigF

        BF : Functor 
        BF .F₀ = B
        BF .F₁ f (done x) = done x
        BF .F₁ f (step x) = step (f x)


        BQ : NatTrans (SigF ∘F (IdF ×F BF)) (BF ∘F FreeF SigF) 
        BQ .α X = s where 
            s : Sig (X × B X) → B (Free SigF X) 
            s (const b)                         = done b
            s (and (x , done b) (y , done b'))  = done (b && b')
            s (and (x , done b) (y , step y'))  = step (op (and (var x) (var y')))
            s (and (x , step x') (y , _))       = step (op (and (var x')  (var y)))
            s (or (x , done b) (y , done b'))   = done (b || b')
            s (or (x , done b) (y , step y'))   = step (op (or (var x) (var y'))) 
            s (or (x , step x') (y , _))        = step (op (or (var x')  (var y))) 
            s (not (x , done b))                = done (neg b)
            s (not (x , step x'))               = step (op (not (var x'))) 
        BQ .square = {!   !} 

        open generalRun SigF BF BQ 

        b : Bool → BExp 
        b x = ⟨ (const x) ⟩

        and' : BExp → BExp → BExp 
        and' b b' = ⟨ (and b b') ⟩

        or' : BExp → BExp → BExp 
        or' b b' = ⟨ (or b b') ⟩

        not' : BExp → BExp 
        not' b = ⟨ (not b) ⟩

        e : BExp 
        e = and' (or' (b true) (b false)) (and' (not' (b true)) (b true))

        _ : run e ≡ done false
        _ = refl


        -- With Variables
        BExpᵒ : Set → Set
        BExpᵒ V = Free SigF V

        data Var₃ : Set where 
            x y z  : Var₃


        openTerm : BExpᵒ Var₃ 
        openTerm = op (and (var x) (var z))

        -- closing substitution 
        γ₃ : Var₃ → Free SigF ⊥ 
        γ₃ x = op (const true)
        γ₃ y = op (or (op (const true))(op (const false)))
        γ₃ z = op (const false)

        -- note that this is just bind of the free monad
        subst : {X Y : Set} → BExpᵒ X → (X → BExpᵒ Y) → BExpᵒ Y 
        subst {X} {Y} e γ = freeHom {SigF} {X} {freeF {SigF} {Y}} {γ} .algmap  e


        cast : BExpᵒ ⊥ → BExp 
        cast = fact {SigF} .inv

        _ : run (cast (subst openTerm γ₃)) ≡ done false
        _ = refl

        