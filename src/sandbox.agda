module src.sandbox where 
    open import Cubical.Data.FinSet
    open import Cubical.Data.FinSet.Constructors
    open import Cubical.Data.FinSet.DecidablePredicate 
    open import Cubical.Data.Sigma
    open import Cubical.Data.Bool
    open import Cubical.Data.Unit
    open import Cubical.Foundations.Equiv
    open import Cubical.Foundations.Isomorphism
    open import Cubical.Foundations.Prelude
    open Iso

    module _ {ℓ}
        {X : FinSet ℓ}
        {A : Set ℓ}
        (el : A → Set ℓ)
        (a : A)
        (f : X .fst → A)
        ((x , fx≡a) : Σ[ x ∈ X .fst ] f x ≡ a )
        ((y , fy) : Σ[ y ∈ X .fst ] el (f y))
        (default : el a)
         where 

        test : el a 
        test with (isDecProp≡ X x y )
        ... | false , _ = default
        ... | true , eq = transport prf fy where 
            prf : el (f y) ≡ el a 
            prf = cong el (cong f (sym (equivToIso eq .inv tt)) ∙ fx≡a)

    
    data Syn : Type where 
        _⇒_ : Syn → Syn → Syn 
    
    el : Syn → Type 
    el (x ⇒ y) = el x → el y

    open import Effect.Monad.State 
    open import Cubical.Data.Nat
    open import Cubical.Data.Unit

    S : Type 
    S = ℕ → ℕ

    T : Type → Type 
    T A = State S A
   -- T A = State (ℕ → T ℕ) A

    open import Effect.Monad

    open import Effect.Monad.State.Transformer hiding (monad)
    open import Effect.Monad.Identity hiding(monad)
    open RawMonad {ℓ-zero} (monad {ℓ-zero}{S})
    
    get : T (ℕ → ℕ)
    get = mkStateT (λ s → mkIdentity (s , s))

    put : (ℕ → ℕ) → T Unit
    put f = mkStateT (λ s → mkIdentity (f , tt))

    idℕ : ℕ → ℕ 
    idℕ x = x 

    r : T Unit
    r = put idℕ

    f : ℕ → T ℕ
    f n = (λ g → return (g n)) =<< get
    -- but you can't store f in T
    -- T would need to store elements of ℕ → T ℕ 
    -- which is already recursive
    


{- 
    module boring {X : Type} where 

        postulate 
            Xset : isSet X
        open import Cubical.Data.Sum

        data T : Type where 
            c : X → T

        _ : {x y : X} → c x ≡ c y → x ≡ y
        _ = cong λ {(c x) → x}

        inlinj : {Y : Set}{x y : X} → inl{B = Y} x ≡ inl y → x ≡ y 
        inlinj {x = x} = cong λ { (inl x) → x
                                ; (inr _) → x}


        open import Cubical.Foundations.Isomorphism
        open import Cubical.Foundations.Equiv 
        open import Cubical.Data.Sigma.Properties
        open import Agda.Builtin.Cubical.Equiv


        XisoT : Iso X T 
        XisoT = iso c ((λ{ (c x) → x})) (λ{ (c x) → refl}) (λ b → refl)
        
        cEquiv : isEquiv c 
        cEquiv = isoToIsEquiv XisoT

        injectivity : {x y : X} → c x ≡ c y → x ≡ y
        injectivity {x} {y} p i = cEquiv .equiv-proof (c x) .snd ( y , (sym p) ) i .fst 
        
        TisoX : Iso T X 
        TisoX = (iso (λ{ (c x) → x}) c (λ b → refl) λ{ (c x) → refl})

        cEquiv' : isEquiv c 
        cEquiv' = isoToIsEquiv ( invIso TisoX )

        injectivity' : {x y : X} → c x ≡ c y → x ≡ y
        injectivity' {x} {y} p i = thing i .fst where 
            thing : fst (cEquiv' .equiv-proof (c x)) ≡ (y , sym p)
            thing = cEquiv' .equiv-proof (c x) .snd ( y , sym p )

        l₁ : {X : Set ℓS} → ⊥ ⊎ X → X
        l₁ (inr x) = x
        l₁ (inl ())

        _ : {X : Set ℓS} → (Fin 0 ) ⊎ X ≡ X
        _ = isoToPath (iso l₁ inr (λ b → refl) λ{ (inr x) → refl })

        module sanity (X Y Z W : ob (FinSetMono{ℓS}))
                      (f : (FinSetMono{ℓS}) [ X , Y ])
                      (g : (FinSetMono{ℓS}) [ Z , W ]) where

            X⊎Z : ob (FinSetMono{ℓS})
            X⊎Z = (fst X) ⊎ (fst Z) , isFinSet⊎ X Z

            Y⊎W : ob (FinSetMono{ℓS})
            Y⊎W = (fst Y) ⊎ (fst W) , isFinSet⊎ Y W
            open import  Cubical.Functions.Embedding

            fin : (w x : fst X) → fst f w ≡ fst f x → w ≡ x
            fin = isEmbedding→Inj (snd f)

            gin : (w x : fst Z) → fst g w ≡ fst g x → w ≡ x
            gin = isEmbedding→Inj (snd g)

            inlinj : {X Y : Set ℓS}{x y : X} → inl{B = Y} x ≡ inl y → x ≡ y 
            inlinj {x = x} = cong λ { (inl x) → x
                                    ; (inr _) → x}

            inrinj : {X Y : Set ℓS}{x y : Y} → inr{A = X} x ≡ inr y → x ≡ y 
            inrinj {x = x} = cong λ { (inl _) → x
                                    ; (inr x) → x}

            prf : (w x : fst X⊎Z) → map (fst f) (fst g) w ≡ map (fst f) (fst g) x → w ≡ x 
            prf (inl x₁) (inl x) p = cong inl (fin x₁ x (inlinj p) )
            prf (inl x₁) (inr x) p = {!   !}
            prf (inr x₁) (inl x) p = {!   !}
            prf (inr x₁) (inr x) p = cong inr (gin x₁ x (inrinj p))

            thing : (FinSetMono{ℓS}) [ X⊎Z , Y⊎W ]
            thing = map (fst f) (fst g) , λ e₁ e₂ → record { equiv-proof = λ p → (prf e₁ e₂ p , {! refl  !}) , (λ y₁  → {!   !}) } 




      
-}

            
 