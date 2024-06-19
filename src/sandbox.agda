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

            
