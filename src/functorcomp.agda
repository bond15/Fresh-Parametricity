module src.functorcomp where

    open import Cubical.Foundations.Powerset
    open import Cubical.Foundations.Prelude
    open import Cubical.Foundations.HLevels
    open import Cubical.Functions.Logic
    open import Cubical.Foundations.Function
    open import Cubical.Data.Sigma
    
    sub : {X : Set} → ℙ X  → Set 
    sub {X} P = Σ[ x ∈ X ] P x .fst

    sing : {X : Set} → X → ℙ X
    sing x y = x ≡ₚ y

    lemma : {A : Set} → (X : ℙ A) → (prf : isContr (sub X)) → X ≡ sing (prf .fst .fst)
    lemma X prf = {! prf  .snd  !}
    
    functComp : {(A , _) (B , _) : hSet ℓ-zero} → 
        (P : A → ℙ B) → 
        (∀ (a : A) → isContr (sub (P a))) → 
        ∃![ f ∈ (A → B) ] P ≡ sing ∘ f
    functComp P prf = 
        uniqueExists
            (λ a → prf a .fst .fst) 
            (funExt (λ a → {! P a .snd _     !})) 
            {!   !}  
            {!   !}
