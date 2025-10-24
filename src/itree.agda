{-# OPTIONS --guardedness #-}
module src.itree where
    open import Cubical.Data.Nat
    open import Cubical.Data.Sigma
    open import Cubical.Data.Unit
    open import Cubical.Foundations.Prelude hiding(_∧_;_∨_;subst)

    S = ℕ

    _∘_ : {A B C : Set} → (B → C) → (A → B) → A → C 
    _∘_ g f = λ z → g (f z)

    --data FreeSt (X : Set) : Set where 
    --    var : X → FreeSt X 
    --    get : (S → X) → FreeSt X
    --    set : S × FreeSt X → FreeSt X
        
    record Functor : Set₁ where  
        field 
            F₀ : Set → Set 
            F₁ : {X Y : Set}(f : X → Y) → F₀ X → F₀ Y 
    
    open Functor

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

    {-# NO_POSITIVITY_CHECK #-}
    data Free (F : Functor) (X : Set) : Set where 
        var : X → Free F X 
        op : (F₀ F) (Free F X) → Free F X

    record Monad (F : Functor): Set₁ where 
        private module F = Functor F 
        field 
            η : {X : Set} → X → F.F₀ X
            μ : {X  : Set}→  F.F₀ (F.F₀ X) → F.F₀ X

        _>>=_ : {X Y : Set} → F.F₀ X → (X → F.F₀ Y) → F.F₀ Y 
        _>>=_ {X} Fx f = μ (F.F₁  f Fx)

        _>>_ : {X Y : Set} → F.F₀ X → F.F₀ Y → F.F₀ Y 
        _>>_ f g = f >>= λ _ → g

    open Monad {{...}}

    record NatTrans (F G : Functor) : Set₁ where 
        private module F = Functor F 
        private module G = Functor G 
        field
            α : ∀ (X : Set) → F.F₀ X → G.F₀ X
            square : ∀ {X Y : Set}(f : X → Y) → (G.F₁ f ∘ α X) ≡ (α Y ∘ F.F₁ f)
    open NatTrans

    record MonadMor {F G : Functor}(M : Monad F)(N : Monad G) : Set₁ where 
        field 
            nt : NatTrans F G
         --   ηpres : {! η   !} ≡ N .η

    module freestuff {F : Functor}{X : Set} where 

        record FreeSigAlg (F : Functor)(X : Set): Set₁ where 
            field 
                alg : Alg F
                η : X → Alg.car alg
                cond : {A : Alg F}{h : X → Alg.car A} → 
                    ∃! (AlgHom alg A) λ h* → h ≡  (h* .algmap ∘ η)
        open FreeSigAlg

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

    
    open freestuff


    FreeF : Functor → Functor 
    FreeF F .F₀ X = Free F X
    FreeF F .F₁ {X} {Y} f = -- renaming functor, f is used to map from variables X to Y
        freeHom {F}{X}{freeF {F}{Y} }{var ∘ f} .algmap 

    {-# TERMINATING #-}
    FreeM : {F : Functor} → Monad (FreeF F)
    FreeM .η = var
    FreeM {F} .μ  {X} = joinfree where 
        joinfree : Free F (Free F X) → Free F X
        joinfree (var x) = x -- 
        joinfree (op e) = op ((F₁ F) joinfree e)

    data StΣ' (X : Set)  : Set where 
        get : (S → X) → StΣ' X 
        set : S × X → StΣ' X 

    StF : Functor 
    StF .F₀ = StΣ'
    StF .F₁ f (get k) = get (f ∘ k)
    StF .F₁ f (set (s , x)) = set (s , f x)

    StateΣF = FreeF StF

    StateF : Set → Set 
    StateF = Free StF

    St : Set → Set 
    St A = S → A × S 

    State : Functor 
    State .F₀ = St 
    State .F₁ {X} f Sx s = f (xs .fst) , xs .snd  where 
        xs : X × S 
        xs = Sx s



    instance 
        StMon :  Monad State
        StMon .η x s = x , s
        StMon .μ {X} ssx s = f .fst (f .snd) where 
            f : St X × S 
            f = ssx s

        FreeStMon : Monad StateΣF
        FreeStMon = FreeM


    get-free : StateF S
    get-free = op (get var)

    set-free : ℕ → StateF Unit 
    set-free n = op (set (n , var tt))

    -- see that there is no apriori way to verify this equation for the free state monad
    test : get-free >> get-free ≡ get-free 
    test = {!  !}

    prog : StateF Unit 
    prog = get-free >>= (λ x → set-free (1 + x))

    hmm : Alg StF 
    hmm .car = {!  !}
    hmm .alg = {!   !}

    up : {X : Set}{A : Alg StF} → (X → car A) → StateF X → car A 
    up {X} {A} h = freeHom {StF}{X}{A}{h} .algmap


    -- the state monad supports these operations and these equations
    get' : St S 
    get' s = (s , s)

    set' : ℕ → St Unit 
    set' n s = tt , n

    get'-set' : get' >>= (λ x → set' x ) ≡ η tt 
    get'-set' = refl
    
    get'-get' : get' >> get' ≡ get'
    get'-get' = refl

    set'-get' : {n : ℕ} → set' n >> get' ≡ set' n >> η n
    set'-get' = refl

    set'-set' : {n m : ℕ} → set' n >> set' m ≡ set' m 
    set'-set' = refl


        
        


