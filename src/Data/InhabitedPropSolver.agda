{-# OPTIONS --cubical --safe --overlapping-instances #-}
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Logic
open import Cubical.Foundations.Structure
open import Cubical.HITs.PropositionalTruncation 

module src.Data.InhabitedPropSolver where
    
    record Inhabited (A : Set ): Set  where 
        constructor inhab
        field 
            default : A

    open Inhabited {{...}}

    -- this is just a contractible type.
    --record iProp : Set  where 
   --     field 
    --        p : hProp ℓ-zero
   --        point : Inhabited ⟨ p ⟩ 
    
   -- open iProp

    -- no, this won't work for existentials
    -- you need a pair of SOME a :A and a proof that B a is inhabited
    -- NOT foall a
    record InhabitedFam (A : Set)(B : A → Set): Set where 
        constructor inhab'
        field 
            def : {x : A} → Inhabited (B x) 
    open InhabitedFam {{...}}


    record InhabitedPair (A : Set)(B : A → Set) : Set where 
        field 
            a : A 
            Ba : Inhabited (B a)
    open InhabitedPair {{...}}

    idfam : {A : Set} → (A → Set) 
    idfam {A} x = A

    -- TODO
    -- metaprogramming task 
    -- use a GHC generic type approach to 
    -- Derive instances of Inhabited for any complete proof/term w/o a hole in a development?

    -- Free Theorems for Free
    -- 

    instance 

        topInhabited : Inhabited (Lift Unit)
        topInhabited = record { default = tt* }

        IDInhabitedFam : {A : Set}{{_ : Inhabited A}} → InhabitedFam A idfam
        IDInhabitedFam = inhab' (inhab default)

        andInhabited : 
            {P Q : Set}
            {{ _ : Inhabited P }}
            {{ _ : Inhabited Q }} 
            → InhabitedPair P (λ _ → Q) 
        andInhabited {Q}{P}{{_}}{{Q'}}= record { a = default ; Ba = Q' }

        impInhabited : 
            {P Q : Set}
            {{ _ : Inhabited Q}}
            → InhabitedFam P (λ _ → Q)
        impInhabited = inhab' (inhab default)
        
        truncInhabited : { P : Set} → {{ _ : Inhabited P}} → Inhabited ( ∥ P ∥₁ )
        truncInhabited = record { default = ∣ default ∣₁ }

        sumLInhabited : { P Q : Set} → {{ _ : Inhabited P}} → Inhabited ( P ⊎ Q )
        sumLInhabited = record { default = _⊎_.inl default }
        
        --{-# OVERLAPS sumRInhabited  #-}
        -- need to use something like this to guide resolution search, overlapping at sum
        sumRInhabited : { P Q : Set} → {{ _ : Inhabited Q}} → Inhabited ( P ⊎ Q )
        sumRInhabited = record { default = _⊎_.inr default }

        forallInhabited : {P : Set}{Q : P → Set}{{ _ : InhabitedFam P Q}} → Inhabited (∀ (x : P) → Q x)
        forallInhabited {P}{Q}{{r}} = inhab (λ x → def{P}{Q}{{r}}{x} .default)

        existsInhabited : {P : Set}{Q : P → Set}{{ _ : InhabitedPair P Q}} → Inhabited (Σ[ x ∈ P ] Q x)
        existsInhabited {P}{Q}{{Qi}}= inhab ( Qi .a , Qi .Ba .default)
{- 
        impInhabited' : 
            {P Q : Set}
            {{ _ : Inhabited Q}} → 
            Inhabited (P → Q)
        impInhabited' = {!   !}
 -}     



    --module _ {{overlap x : Inhabited ⊤}} where 
 
    module _ where
        open import Cubical.Data.Nat 
        _ : Inhabited (∀ (n : ℕ)→ Σ[ b ∈ Bool ] {! b  !} )
        _ = {!   !}


    -- REALLY....?
    solve : {P Q : hProp ℓ-zero } {{ _ : Inhabited ⟨ P ⟩ }}{{ _ : Inhabited ⟨ Q ⟩ }} → P ≡ Q 
    solve = ⇔toPath default default


    --yes, explaination is simple
    contr : (P : hProp ℓ-zero) → {{ _ : Inhabited ⟨ P ⟩}}  → isContr ⟨ P ⟩  
    contr P = default , P .snd default 

    instance
        -- basically just solve
        eqPropInhabited : {P : hProp ℓ-zero}{x y : ⟨ P ⟩}{{ _ : Inhabited ⟨ P ⟩ }} → Inhabited ⟨ x ≡ₚ y ⟩ 
        eqPropInhabited {P}{x}{y}{{P'}}= 
            --inhab ∣ {! solve  !} ∣₁ where
            inhab ∣ sym (Pcontr .snd x) ∙ Pcontr .snd y ∣₁ where 
                Pcontr : isContr ⟨ P ⟩ 
                Pcontr = contr P {{P'}} 

    module _  {P Q : hProp ℓ-zero }
        {{ _ : Inhabited ⟨ P ⟩ }}
        {{ _ : Inhabited ⟨ Q ⟩ }} where 

        open import Cubical.Foundations.Isomorphism 

        yeah : Iso ⟨ P ⟩ ⟨ Q ⟩ 
        yeah = iso (λ _ → default) (λ _ → default) (contr Q ⦃ _ ⦄ .snd) (contr P ⦃ _ ⦄ .snd)

        duh : ⟨ P ⟩ ≡ ⟨ Q ⟩ 
        duh = isoToPath yeah
        
 
    module _
        {P Q R : hProp ℓ-zero }
        {{ _ : Inhabited ⟨ P ⟩ }}
        {{ _ : Inhabited ⟨ Q ⟩ }}
        {{ _ : Inhabited ⟨ R ⟩ }} where

        --d : (x y : ⟨ P ⟩) → ⟨ x ≡ₚ y ⟩  
        --d x y = default

        _ : hProp ℓ-zero 
        _ = ∀[ b ∶ Bool ] b ≡ₚ true


        instance
            myPropInhabitedd : InhabitedFam Bool (λ b → ⟨ not (not b) ≡ₚ b ⟩  )
            myPropInhabitedd = inhab' (inhab ∣ notnot _ ∣₁)

            nope : InhabitedPair Bool (λ b → ⟨ b ≡ₚ true ⟩ )
            nope = record { a = true ; Ba = inhab ∣ refl ∣₁ }

        _ : P ≡ ⊤
        _ = solve
        
        _ : (∃[ b ∶ Bool ] b ≡ₚ true) ≡ (∀[ b ∶ Bool ] ( not (not b) ≡ₚ b )) ⊓ P
        _ = solve

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
        
        instance
            myPropInhabited : Inhabited ⟨ 1 ≡ₚ 1 ⟩ 
            myPropInhabited = inhab ∣ refl ∣₁ 

        _ : P ⊔ (1 ≡ₚ 1 ⊔ R) ≡ (P ⊔ Q) ⊔ 1 ≡ₚ 1  
        _ = solve 
         
    module test where
        instance 
            -- problematic, infinite recursion in resolution?
            mp : {P Q : Set}{{_ : Inhabited (P → Q)}}{{_ : Inhabited P}} → Inhabited Q
            mp {P}{Q}{{R}}{{S}}= inhab (f x) where
                f : P → Q 
                f = R .default

                x : P 
                x = S .default

        open import Cubical.Data.Nat
        hmm : Bool → ℕ 
        hmm false = 0 
        hmm true = 1

        instance 
            _ : Inhabited (Bool → ℕ)
            _ = inhab hmm

            _ : Inhabited Bool 
            _ = inhab true

            --_ : ℕ 
            --_ = default --{ℕ} {{_}}