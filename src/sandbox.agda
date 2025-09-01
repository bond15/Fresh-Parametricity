{-# OPTIONS --guardedness --type-in-type #-}
module src.sandbox where
    open import Agda.Builtin.String
    open import IO
    postulate 
        ex' : String

        
    {-# FOREIGN GHC
        {-# LANGUAGE ForeignFunctionInterface #-}
        import Data.Text
        foreign import ccall "exp" c_exp :: Double -> Double



        ex :: Text
        ex = pack $ show $ c_exp 2
    #-}

    {-# COMPILE GHC ex' = ex #-}
    main = run (putStrLn ex')
 
 {-   -- {-# OPTIONS --backtracking-instance-search #-}
   -- ctrl-C ctrl-= to see instance issues
    module src.sandbox where
        open import Cubical.Data.Bool
        open import Cubical.Data.Unit
        open import Cubical.Foundations.Prelude
        open import Cubical.Data.Sigma
        open import Cubical.Data.Sum
        open import Cubical.Foundations.HLevels
        open import Cubical.Functions.Logic
        open import Cubical.Foundations.Structure
        open import Cubical.HITs.PropositionalTruncation as PropTrunc
-}
{-         record Inhabited (A : Set): Set where 
            field 
                prf : Σ A λ _ → isProp A

            default = fst prf
            prop = snd prf
            
        open Inhabited {{...}}
        
        instance 
            topInhabited : Inhabited (Lift Unit)
            topInhabited = record { prf = tt* , isPropUnit* }

            andInhabited : 
                {P Q : Set}
                {{ _ : Inhabited P}}
                {{ _ : Inhabited Q }} 
                → Inhabited ( P × Q)
            andInhabited = record { prf = (default , default) , isProp× prop prop }

            impInhabited : 
                {P Q : Set}
                {{ _ : Inhabited P}}
                {{ _ : Inhabited Q }} 
                → Inhabited ( P → Q)
            impInhabited = record { prf = (λ x → default) , isProp→ prop }
            
            truncInhabited : { P : Set} → {{ _ : Inhabited P}} → Inhabited ( ∥ P ∥₁ )
            truncInhabited = record { prf = ∣ default ∣₁ , isPropPropTrunc } 

            -- issue 
            -- isProp⊎ : isProp A → isProp B → (A → B → ⊥) → isProp (A ⊎ B)
            sumLInhabited : { P Q : Set} → {{ _ : Inhabited P}} → Inhabited ( P ⊎ Q )
            sumLInhabited = record { prf = _⊎_.inl default , isProp⊎ prop {!   !} {!   !} }
           -- pTruncInhabited : {P : Set} → {{ _ : Inhabited P}} → Inhabited (∥ P ∥ₚ)
           -- pTruncInhabited  = ? -}

    {- _⊔′_ : Type ℓ → Type ℓ' → Type _
A ⊔′ B = ∥ A ⊎ B ∥₁

_⊔_ : hProp ℓ → hProp ℓ' → hProp _
P ⊔ Q = ∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥ₚ}


∥_∥ₚ : Type ℓ → hProp ℓ
∥ A ∥ₚ = ∥ A ∥₁ , isPropPropTrunc

-}

     {-    record Inhabited (A : Set): Set where 
            field 
                default : A

            
        open Inhabited {{...}}
        
        instance 
            topInhabited : Inhabited (Lift Unit)
            topInhabited = record { default = tt* }

            andInhabited : 
                {P Q : Set}
                {{ _ : Inhabited P}}
                {{ _ : Inhabited Q }} 
                → Inhabited ( P × Q)
            andInhabited = record { default = default , default}

            impInhabited : 
                {P Q : Set}
                {{ _ : Inhabited P}}
                {{ _ : Inhabited Q }} 
                → Inhabited ( P → Q)
            impInhabited = record { default = λ x → default }
            
            truncInhabited : { P : Set} → {{ _ : Inhabited P}} → Inhabited ( ∥ P ∥₁ )
            truncInhabited = record { default = ∣ default ∣₁ }

            -- issue 
            -- isProp⊎ : isProp A → isProp B → (A → B → ⊥) → isProp (A ⊎ B)
            sumLInhabited : { P Q : Set} → {{ _ : Inhabited P}} → Inhabited ( P ⊎ Q )
            sumLInhabited = record { default = _⊎_.inl default }

            -- this overlaps with arrow type
            --forallInhabited : {P : Set}{Q : P → Set}{{ _ : Inhabited P}} → Inhabited (∀ (x : P) → Q x)
           -- forallInhabited = {!   !}

            -- need to handle overlapping instances ..?
           -- sumRInhabited : { P Q : Set} → {{ _ : Inhabited Q}} → Inhabited ( P ⊎ Q )
          --  sumRInhabited = record { default = _⊎_.inr default }


{-
    --    {-# OVERLAPS sumRInhabited  #-}
        solve : {P Q : hProp ℓ-zero } {{ _ : Inhabited ⟨ P ⟩ }}{{ _ : Inhabited ⟨ Q ⟩ }} → P ≡ Q 
        solve = ⇔toPath default default

        module _
            {P Q R : hProp ℓ-zero }
            {{ _ : Inhabited ⟨ P ⟩ }}
            {{ _ : Inhabited ⟨ Q ⟩ }}
            {{ _ : Inhabited ⟨ R ⟩ }} where

            _ : P ⊓ Q ≡ Q ⊓ P
            _ = solve

            _ : ⊤ {ℓ-zero} ⊓ P ≡ P
            _ = solve
            
            _ : P ⊔ P ≡ P 
            _ = solve
            
            _ : P ⊔ (Q ⊓ R) ≡ (P ⊔ Q) ⊓ (P ⊔ R)
            _ = solve

            _ : P ⊔ ⊥ ≡ P
            _ = solve

            _ : P ⊔ (Q ⊔ R) ≡ (P ⊔ Q) ⊔ R 
            _ = solve

            _ : P ⇒ (Q ⊓ R) ≡ (P ⇒ Q) ⊓ (P ⇒ R) 
            _ = solve
            
            myProp : hProp ℓ-zero 
            myProp = 1 ≡ₚ 1

            instance
                myPropInhabited : Inhabited ⟨ myProp ⟩ 
                myPropInhabited = record { default = ∣ refl ∣₁ }
                
 -}


    

        







{-
        instance 
            andInhabited : 
                {P Q : hProp (ℓ-zero)}
                {{ _ : Inhabited ⟨ P ⟩ }}
                {{ _ : Inhabited ⟨ Q ⟩ }} 
                → Inhabited ⟨ P ⊓ Q ⟩ 
            andInhabited = record { default = default , default }

       -- P : hProp ℓ-zero 
       -- P = ⊤ 
-}
      --  module _ {P : hProp ℓ-zero }{{ _ : Inhabited ⟨ P ⟩ }} where 
  --          foo : ⟨ P ⊓ P ⟩ 
   --         foo = testing {P ⊓ P} default


{-
        record isPropSearch (A : Set) : Set where 
            field 
                isP : isProp A 

        open isPropSearch {{...}}

        --{{ _ : isPropSearch A}}
        record Inhabited (A : Set): Set where 
            field 
                default : {{ _ : isPropSearch A }} → A 
          --  instance 
         --       isPropA : isProp 


        open Inhabited {{...}}


        instance
            trueIsProp : isPropSearch (⊤ .fst)
            trueIsProp = record { isP = ⊤ .snd }
            
            trueInhabited : Inhabited(⊤ .fst)
            trueInhabited = record { default = (lift tt) }

            andInhabited : 
                {P Q : hProp (ℓ-zero)}
                {{ _ : Inhabited (P .fst)}}
                {{ _ : isPropSearch (P .fst) }}
                {{ _ : Inhabited (Q .fst)}} 
                {{ _ : isPropSearch (Q .fst) }}
                → Inhabited ((P ⊓ Q) .fst)
            andInhabited = record { default = default , default }

            impIsProp : 
                {P Q : hProp (ℓ-zero)}
                {{ _ : Inhabited (P .fst)}}
                {{ _ : isPropSearch (P .fst) }}
                {{ _ : Inhabited (Q .fst)}} 
                {{ _ : isPropSearch (Q .fst) }} 
                → isPropSearch ⟨ P ⇒ Q ⟩
            impIsProp = record { isP = isProp→ isP }

            impInhabitedImp : 
                {P Q : hProp (ℓ-zero)}
                {{ _ : Inhabited (P .fst)}}
                {{ _ : isPropSearch (P .fst) }}
                {{ _ : Inhabited (Q .fst)}} 
                {{ _ : isPropSearch (Q .fst) }}
                → Inhabited ((P ⇒ Q) .fst)
            impInhabitedImp = record { default = λ x → default }


        myProp : hProp ℓ-zero 
        myProp = ⊤
        
        _ : myProp .fst 
        _ = default

        module _ 
            {P Q : hProp ℓ-zero}
            {{ _ : Inhabited (P .fst) }}
            {{ _ : isPropSearch (P .fst) }}
            {{ _ : isPropSearch (Q .fst) }}
            {{ _ : Inhabited (Q .fst) }} where
-- ⊓-idem : (P : hProp ℓ) → P ⊓ P ≡ P



          -- solve : P ≡ P
          -- solve = ⇔toPath default {!   !}

      --  _ : (⊤ ⊓ ⊤) .fst
        --_ = {!  default !}

        -- hProp
       -- search : (P : hProp (ℓ-zero)) → P .fst × {! P .snd  !}
      --  search P = {!   !}
-}

    {-
        goal: try to solve these using instance resolution ...

        ⇔toPath : ⟨ P ⇒ Q ⟩ → ⟨ Q ⇒ P ⟩ → P ≡ Q

        ⊓-assoc : (P : hProp ℓ) (Q : hProp ℓ') (R : hProp ℓ'')
        → P ⊓ Q ⊓ R ≡ (P ⊓ Q) ⊓ R
        ⊓-assoc _ _ _ =
        ⇒∶ (λ {(x , (y , z)) →  (x , y) , z})
        ⇐∶ (λ {((x , y) , z) → x , (y , z) })

        ⊓-comm : (P : hProp ℓ) (Q : hProp ℓ') → P ⊓ Q ≡ Q ⊓ P
        ⊓-comm _ _ = ⇔toPath (\ p → p .snd , p .fst) (\ p → p .snd , p .fst)
    
    -}

{-

        record isPropSearch (A : Set) : Set where 
            field 
                isP : isProp A 

        open isPropSearch {{...}}


        record Inhabited (A : Set) : Set where
            field
                {{ isPropSearch A }}
                default : A

        open Inhabited {{...}}

        instance
            boolInhabited : Inhabited Bool
            boolInhabited = record { default = true }


        _ : Bool
        _ = default

        module _ (A : Set) {{ _ : Inhabited A }}  where

            _ : A
            _ = default


        _ : hProp (ℓ-zero)
        _ = {!   !} , {!   !}
        data Hold (A : Set) : Set where 
            HoldC : A -> Hold A

        open import  Cubical.HITs.PropositionalTruncation.Base

        instance
            
            trueInhabited : Inhabited (⊤ .fst)
            trueInhabited = record { default = (lift tt) }

            trueIsProp : isPropSearch (⊤ .fst)
            trueIsProp = record { isP = ⊤ .snd }

            andInhabited : 
                {P Q : hProp (ℓ-zero)}
                {{ _ : Inhabited (P .fst)}}
                {{ _ : Inhabited (Q .fst)}} → Inhabited ((P ⊓ Q) .fst)
            andInhabited = record { default = default , default }

            andIsProp :
                {P Q : hProp (ℓ-zero)}
                {{ _ : isPropSearch (P .fst)}}
                {{ _ : isPropSearch (Q .fst)}} → 
                isPropSearch ((P ⊓ Q) .fst)
            andIsProp = record { isP = isProp× isP isP }

            orInhabitedInl : 
                {P Q : hProp (ℓ-zero)}
                {{ _ : Inhabited (P .fst)}}
                 → Inhabited ((P ⊔ Q) .fst)
            orInhabitedInl = record { default = inl default }

            -- maybe make this dependent on the inhabited instance ?
            orInlIsProp :
                {P Q : hProp (ℓ-zero)}
                {{ _ : isPropSearch (P .fst)}} → 
                {{ _ : isPropSearch (Q .fst)}} → 
                isPropSearch ((P ⊓ Q) .fst)
            orInlIsProp = record { isP = {!   !}}

            orInhabitedInR : 
                {P Q : hProp (ℓ-zero)}
                {{ _ : Inhabited (Q .fst)}}
                 → Inhabited ((P ⊔ Q) .fst)
            orInhabitedInR = record { default = inr default }

            impInhabitedImp : 
                {P Q : hProp (ℓ-zero)}
              --  {{ _ : Inhabited (P .fst)}}
                {{ _ : Inhabited (Q .fst)}} → Inhabited ((P ⇒ Q) .fst)
            impInhabitedImp = record { default = λ x → default }


        
        module _ {P Q R : hProp (ℓ-zero)}
            {{ _ : Inhabited (P .fst)}}
            {{ _ : Inhabited (Q .fst)}}
            {{ _ : Inhabited (R .fst)}}
            {{ _ : isPropSearch (P .fst)}}
            {{ _ : isPropSearch (Q .fst)}} 
            {{ _ : isPropSearch (R .fst)}} 
             where
            
            test1 : hProp (ℓ-zero)
            test1 = (P ⊓ Q) -- ⇒ (Q ⊓ P)

            test1' : test1 .fst
            test1' = default

        


        data formula : Set where 
            tru : formula
            and or imp : formula → formula → formula

        
        El : formula → hProp (ℓ-zero)
        El tru = ⊤
        El (and p q) = El p ⊓ El q
        El (or p q) = El p ⊔ El q
        El (imp p q) = El p ⇒  El q



        -- but you could already do this via a recursive function...
        -- but the formulas are not extensible.....?
        search' : (P : formula) → ((El P) .fst) × (isProp ((El P) .fst ))
        search' tru = (lift tt) , isPropUnit*
        search' (and x x₁) = {!   !} , {!   !}
        search' (or x x₁) = {!   !}
        search' (imp x x₁) = {!   !}

        search : {P : formula} {{ _ : Inhabited ((El P).fst)}}{{ _ : isPropSearch ((El P).fst)}} → ((El P) .fst) × (isProp ((El P) .fst ))
        search = default , isP
-}
        --example : 
{-
        module _ {A B : Set} where 
            instance
                --foo : isSet Unit 
                --foo = isSetUnit

                summon : ⦃ _ : isSet A ⦄ → isSet A 
                summon ⦃ x ⦄ = x

                foo : ⦃ _ : isSet A ⦄ ⦃ _ : isSet B ⦄ → isSet (A × B)
                foo ⦃ a ⦄ ⦃ b ⦄  = isSet× a b


        _ : isSet (Bool × (Bool × Bool))
        _ = {! summon  !}
         {-}Cubical.Foundations.HLevels

-}

        module foo {A B : Set} where 
            open import Cubical.Relation.Nullary.Base
            open import Cubical.Data.Sum
            instance
                Dec-⊎ : ⦃ _ : Dec A ⦄ ⦃ _ : Dec B ⦄ → Dec (A ⊎ B)
                Dec-⊎ ⦃ yes A ⦄ ⦃ _ ⦄ = yes (inl A)
                Dec-⊎ ⦃ no ¬A ⦄ ⦃ yes B ⦄ = yes (inr B)
                Dec-⊎ ⦃ no ¬A ⦄ ⦃ no ¬B ⦄ = no [ ¬A , ¬B ]

                Dec-× : ⦃ _ : Dec P ⦄ ⦃ _ : Dec Q ⦄ → Dec (P × Q)
                Dec-× {Q = _} ⦃ yes p ⦄ ⦃ yes q ⦄ = yes (p , q)
                Dec-× {Q = _} ⦃ yes p ⦄ ⦃ no ¬q ⦄ = no λ z → ¬q (snd z)
                Dec-× {Q = _} ⦃ no ¬p ⦄ ⦃ _ ⦄     = no λ z → ¬p (fst z)

                Dec-→ : ⦃ _ : Dec P ⦄ ⦃ _ : Dec Q ⦄ → Dec (P → Q)
                Dec-→ {Q = _} ⦃ yes p ⦄ ⦃ yes q ⦄ = yes λ _ → q
                Dec-→ {Q = _} ⦃ yes p ⦄ ⦃ no ¬q ⦄ = no λ pq → ¬q (pq p)
                Dec-→ {Q = _} ⦃ no ¬p ⦄ ⦃ q ⦄ = yes λ p → absurd (¬p p)

                Dec-⊤ : Dec ⊤
                Dec-⊤ = yes tt

                Dec-⊥ : Dec ⊥
                Dec-⊥ = no id
                 -}
    -- open import Cubical.Data.FinSet
    -- open import Cubical.Data.FinSet.Constructors
    -- open import Cubical.Data.FinSet.DecidablePredicate 
        open import Cubical.Data.Sigma
        open import Cubical.Data.Bool
        --open import Cubical.Data.Unit
        --open import Cubical.Foundations.Equiv
        --open import Cubical.Foundations.Isomorphism
    -- open import Cubical.Foundations.Prelude
        --open Iso

        record Monad (F : Set → Set) : Set₁ where 
            field
                return : ∀ {A} → A → F A
                _>>=_ : ∀{A B} → F A → (A → F B) → F B
            
            _>>_ : ∀{A B} → F A → F B → F B
            x >> y = x >>= λ _ → y
            
        -- notice the currly brakes and elipse ...
        open Monad{{...}}

        data Maybe (A : Set) : Set where 
            just : A → Maybe A 
            none : Maybe A

        State : (S A : Set) → Set
        State S A = S → (A × S)



        -- a module that takes in any monad
        module usage {F : Set → Set} {{ M : Monad F }} where

            exampleProgram : F Bool 
            exampleProgram = return true >>= λ b → return (not b)

        -- automatic instance resolution
       -- _ : Maybe Bool 
       -- _ = return true

       -- _ : State Bool Bool 
       -- _ = return true

{-
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

            
   -}