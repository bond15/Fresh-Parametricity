module src.gsos where
    open import Cubical.Data.Unit
    open import Cubical.Data.Bool renaming (not to neg ; _and_ to _&&_; _or_ to _||_)
    open import Cubical.Data.Sigma
    open import Cubical.Data.Empty
    open import Cubical.Data.Sum
    open import Cubical.Foundations.Prelude hiding(_∧_;_∨_;subst)
    open import Cubical.Foundations.Isomorphism

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
    FreeOn : Functor → Set → Functor 
    FreeOn F X = 
        record { 
            F₀ = λ Y → (F .F₀) Y ⊎ X ; 
            F₁ = λ{f (inl x) → inl ((F .F₁) f x)
                 ; f (inr x) → inr x} }

    Free : Functor → Set → Set 
    Free F X = μ (FreeOn F X)

    var : {F : Functor}{X : Set} → X → Free F X 
    var x = ⟨ inr x ⟩

    op : {F : Functor}{X : Set} → ((F₀ F) (Free F X)) → Free F X  
    op e = ⟨ inl e ⟩

    pattern Var x =  ⟨ inr x ⟩ 
    pattern Op o =  ⟨ inl o ⟩  

    pattern Var' x =  inr x
    pattern Op' o =  inl o 

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
            h* (Var x) = h x -- renaming
            h* (Op e) = (alg A) ((F₁ F) h* e) -- recursion

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
        joinfree (Var x) = x -- 
        joinfree (Op e) = op ((F₁ F) joinfree e)


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
    -- fact : {F : Functor} → Iso (μ F) (Free F ⊥)  
    --fact = {!   !}

    _×F_ : Functor → Functor → Functor 
    _×F_ F G .F₀ X = F₀ F X × F₀ G X
    _×F_ F G .F₁ f (FX , GX) = F₁ F f FX , F₁ G f GX

    IdF : Functor 
    IdF .F₀ X = X 
    IdF .F₁ f x = f x

    _∘F_ : Functor → Functor → Functor 
    _∘F_ G F .F₀ X = (F₀ G) (F₀ F X)
    _∘F_ G F .F₁ f GFX = F₁ G (F₁ F f) GFX



    module generalRun 
        (Sig : Functor) 
        (B : Functor) 
        (Q : NatTrans (Sig ∘F (IdF ×F B)) (B ∘F FreeF Sig) ) where 


        module B = Functor B
        module Sig = Functor Sig
        module Q = NatTrans Q

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

        -- F X := ℕ ⊎ (X × X)
        data NatEx (X : Set) : Set where 
            const : ℕ → NatEx X 
            plus : X → X → NatEx X 

        -- F X := ℕ ⊎ X
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
            s (plus (x , step x') (y , _))          = step ⟨ (inl (plus (var x') (var y))) ⟩ -- reduce left
            s (plus (x , done n) (y , step y'))     = step ⟨ (inl (plus (var x) (var y'))) ⟩ -- reduce right
            s (plus (x , done n) (y , done m))      = done (n + m)                           -- Not step ⟨ inl (const (n + m)) ⟩
        NatQ .square f = funExt λ{ (const x) → refl
                                 ; (plus (x , done n) (y , done m)) → refl
                                 ; (plus (x , done n) (y , step y')) → refl
                                 ; (plus (x , step x') (y , done m)) → refl
                                 ; (plus (x , step x') (y , step y')) → refl }


        open generalRun NatF Natℬ NatQ 
        
        
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
            s (and (x , done b) (y , step y'))  = step ⟨ (inl (and (var x) (var y'))) ⟩
            s (and (x , step x') (y , _))       = step ⟨ (inl (and (var x')  (var y))) ⟩
            s (or (x , done b) (y , done b'))   = done (b || b')
            s (or (x , done b) (y , step y'))   = step ⟨ (inl (or (var x) (var y'))) ⟩
            s (or (x , step x') (y , _))        = step ⟨ (inl (or (var x')  (var y))) ⟩
            s (not (x , done b))                = done (neg b)
            s (not (x , step x'))               = step ⟨ (inl (not (var x'))) ⟩
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

        



--- CRUFT 
    -- basic distributive law 
   {-} Q' : NatTrans (Sig ∘F ℬ) (ℬ ∘F Sig) 
    Q' .α X (inl Tru') = Tru'
    Q' .α X (inl Fls' ) = Fls'
    Q' .α X (inl (And' x y)) = {!   !}
    Q' .α X (inl d) = {!   !}
    Q' .α X (inr false) = Fls'
    Q' .α X (inr true) = Tru'
    Q' .square = {!   !} -}

{-
    -- can't reduce And Tru Tru ?
    Q' : {X : Set} → (F₀ Sig)(X × Maybe X) → Maybe (Free Sig X)
    Q' Tru' = nothing
    Q' Fls'  = nothing 
    Q' (And' (x , nothing) (y , nothing))   = nothing
    Q' (And' (x , nothing) (y , just y'))   = just (op (And' (var x) (var y')))
    Q' (And' (x , just x') (y , _))         = just (op (And' (var x') (var y)))

    Q' (Or' (x , nothing) (y , nothing))    = nothing
    Q' (Or' (x , nothing) (y , just y'))    = just (op (Or' (var x) (var y')))
    Q' (Or' (x , just x') (y , _))          = just (op (Or' (var x') (var y)))
    
    Q' (Not' (x , nothing))                 = nothing
    Q' (Not' (x , just x'))                 = just (op (Not' (var x')))


    Q : {X : Set} → (F₀ Sig)(Free Sig X × Maybe X) → Maybe (Free Sig X)
    Q Tru'                                              = nothing                       -- terminal
    Q Fls'                                              = nothing                       -- terminal

    Q (And' (Op Fls' , nothing) (Op Tru' , nothing))    = just (op Fls')                -- reduce value
    Q (And' (Op Fls' , nothing) (Op Fls' , nothing))    = just (op Fls')                -- reduce value
    Q (And' (Op Tru' , nothing) (Op Fls' , nothing))    = just (op Fls')                -- reduce value
    Q (And' (Op Tru' , nothing) (Op Tru' , nothing))    = just (op Tru')                -- reduce value
    Q (And' (x , just x') (y , _))                      = just (op (And' (var x') y))   -- reduce left
    Q (And' (x , nothing) (y , just y'))                = just (op (And' x (var y')))   -- reduce right
    Q (And' (x , nothing) (y , nothing))                = nothing                       -- stuck


    Q (Or' (Op Tru' , nothing) (Op Tru' , nothing))     = just (op Tru')                -- reduce value
    Q (Or' (Op Tru' , nothing) (Op Fls' , nothing))     = just (op Tru')                -- reduce value
    Q (Or' (Op Fls' , nothing) (Op Tru' , nothing))     = just (op Tru')                -- reduce value
    Q (Or' (Op Fls' , nothing) (Op Fls' , nothing))     = just (op Fls')                -- reduce value
    Q (Or' (x , just x') (y , _))                       = just (op (And' (var x') y))   -- reduce left
    Q (Or' (x , nothing) (y , just y'))                 = just (op (And' x (var y')))   -- reduce right
    Q (Or' (x , nothing) (y , nothing))                 = nothing                       -- stuck


    Q (Not' (Op Tru' , just x'))                        = just (op Fls')                -- reduce value
    Q (Not' (Op Fls' , just x'))                        = just (op Tru')                -- reduce value
    Q (Not' (x  , just x'))                             = just (op (Not' (var x')))     -- reduce 
    Q (Not' (x , nothing))                              = nothing                       -- stuck

    Qtrans : NatTrans (Sig ∘F ((FreeF Sig ×F ℬ))) (ℬ ∘F FreeF Sig) 
    Qtrans .α X = Q {X} 
    Qtrans .square f = funExt λ{(Op' x) → {!   !}
                              ; (Var' x) → {! refl  !}}



    SigI : Alg Sig 
    SigI = initial {Sig}
-}


{-
    -- Concrete Signature
    pattern Tru' =  inl tt 
    pattern Fls' =  (inr (inl tt)) 
    pattern And' x y =  (inr (inr (inl (x , y)))) 
    pattern Or' x y =  (inr (inr (inr (inl (x , y))))) 
    pattern Not' x =  (inr (inr (inr (inr x)))) 

    pattern Tru =  ⟨ inl tt ⟩ 
    pattern Fls =  ⟨ (inr (inl tt)) ⟩ 
    pattern And x y =  ⟨ (inr (inr (inl (x , y)))) ⟩ 
    pattern Or x y = ⟨ (inr (inr (inr (inl (x , y))))) ⟩ 
    pattern Not x = ⟨ (inr (inr (inr (inr x)))) ⟩ 

    Sig : Functor
    Sig .F₀ X = Unit ⊎ (Unit ⊎ ((X × X) ⊎ ((X × X) ⊎ X)))
    Sig .F₁ f Tru' = Tru'
    Sig .F₁ f Fls' = Fls'
    Sig .F₁ f (And' x y) = And' (f x) (f y)
    Sig .F₁ f (Or' x y) = Or' (f x) (f y)
    Sig .F₁ f (Not' x) = Not' (f x)
 

    Bexp : Set 
    Bexp = μ Sig

    t : Bexp 
    t = Tru

    f : Bexp 
    f = Fls

    and : Bexp → Bexp → Bexp 
    and x y = And x y 

    or  : Bexp → Bexp → Bexp 
    or x y = Or x y  

    not : Bexp → Bexp 
    not x = Not x 

    val : Bexp → Set₀ 
    val Tru = Unit
    val Fls = Unit 
    val _ = ⊥

    val' : Bexp → Bool 
    val' Tru = true
    val' Fls = true
    val' _ = false
{-
    sand : Bexp → Bexp → Bexp 
    sand Tru Tru = Tru 
    sand _ _ = Fls

    sor : Bexp → Bexp → Bexp 
    sor Fls Fls = Fls 
    sor _ _ = Tru

    snot : Bexp → Bexp 
    snot Tru = Fls 
    snot Fls = Tru 
    snot _ = Fls -}

    data _↓ : Bexp →  Set where 
        Vtrue : Tru ↓
        Vfalse : Fls ↓ 
--        VAnd : {e₁ e₂ : Bexp}{b₁ b₂ : Bool} → e₁ ↓ b₁ → e₂ ↓ b₂ → (And e₁ e₂) ↓ (b₁ && b₂) 

    data _↦_ : Bexp → Bexp → Set where 
        andL : {e₁ e₁' e₂ : Bexp} → e₁ ↦ e₁' → and e₁ e₂ ↦ and e₁' e₂ 
        andR : {v₁ e₂ e₂' : Bexp} → val v₁ → e₂ ↦ e₂' → and v₁ e₂ ↦ and v₁ e₂' 
       -- andV : {v₁ v₂ : Bexp} → val v₁ → val v₂ → and v₁ v₂ ↦ sand v₁ v₂
        andV₁ : and Tru Tru ↦ Tru
        andV₂ : and Tru Fls ↦ Fls
        andV₃ : and Fls Tru ↦ Fls
        andV₄ : and Fls Fls ↦ Fls

        orL : {e₁ e₁' e₂ : Bexp} → e₁ ↦ e₁' → or e₁ e₂ ↦ or e₁' e₂ 
        orR : {v₁ e₂ e₂' : Bexp} → val v₁ → e₂ ↦ e₂' → or v₁ e₂ ↦ or v₁ e₂' 
        orV₁ : or Tru Tru ↦ Tru 
        orV₂ : or Tru Fls ↦ Tru 
        orV₃ : or Fls Tru ↦ Tru 
        orV₄ : or Fls Fls ↦ Fls 

        notL : {e e' : Bexp} → e ↦ e' → not e ↦ not e' 
        notV₁ : not Tru ↦ Fls 
        notV₂ : not Fls ↦ Tru



    -- directly encode free monad
    -- var is metavariables. not binder in the syntax of the given functor singnature
    module foo where
        {-# NO_POSITIVITY_CHECK #-}
        data FreeM (F : Functor)(X : Set) : Set where 
            var : X → FreeM F X 
            op : (F₀ F) (FreeM F X) → FreeM F X


        data Var₃ : Set where 
            a b c : Var₃
        
        exF : Functor 
        exF .F₀ X = Unit ⊎ ((X × X) ⊎ (X × X))
        exF .F₁ f (inl x) = inl x
        exF .F₁ f (inr (inl (x , x'))) = inr (inl ((f x) , (f x')))
        exF .F₁ f (inr (inr (x , x'))) = inr (inr ((f x) , (f x')))

        _ : FreeM exF Var₃ 
        _ = op (inr (inl ((var a) , op (inl tt))))
-} 