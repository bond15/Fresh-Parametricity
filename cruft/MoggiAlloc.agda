{-# OPTIONS --safe #-}
-- Example of an allocation monad provided by Moggi in An Abstract View of Programming Languages (4.1.4)
module cruft.MoggiAlloc where
    open import Cubical.Categories.Category        
    open import Cubical.Categories.Functor
    open import Cubical.Categories.Instances.Functors
    open import Cubical.Categories.Instances.Sets
    open import Cubical.Categories.Monad.Base
    open import Cubical.Categories.NaturalTransformation

    open import Cubical.Foundations.HLevels hiding (extend)
    open import Cubical.Foundations.Prelude
        
    open import Cubical.Data.FinSet
    open import Cubical.Data.FinSet.Constructors       
    open import Cubical.Data.Nat 
    open import Cubical.Data.Sigma
    open import Cubical.Data.Sum
    open import Cubical.Data.Unit

    open import src.FinSet    

    open Category 
    open Functor 

    -- this is the one instantiation of the monad Moggi gives 
    module AllocFinSet where 
            
        UnitF : FinSet ℓ-zero
        UnitF = Unit , isFinSetUnit

        -- increase size by one, coproduct for convenience
        inc : FinSet ℓ-zero → FinSet ℓ-zero
        inc X = ((X .fst ⊎ Unit) , isFinSet⊎ X UnitF)

        -- This is an endofunctor on your category of worlds which "takes one step"
        F : Functor (FinSetMono {ℓ-zero}) (FinSetMono {ℓ-zero})
        F .F-ob = inc
        F .F-hom (f , emb) = map f (λ x → x) , {! fsuc  !}
        F .F-id = {!   !}
        F .F-seq = {!   !}

        -- used in Strength of monad
        --σ : NatTrans (Id {C = (FinSetMono {ℓ-zero})}) F 
        --σ = natTrans (λ x → inl , {!   !}) λ f → {!   !}

        finToH : {ℓ : Level} → FinSet ℓ → hSet ℓ 
        finToH (ty , fin) = ty , isFinSet→isSet fin 
        
        -- the "reference" types
        L : Functor (FinSetMono {ℓ-zero}) (SET ℓ-zero)
        L .F-ob = finToH
        L .F-hom = fst
        L .F-id = refl
        L .F-seq f g = refl

        Term : Functor (FinSetMono {ℓ-zero}) (SET ℓ-zero)
        Term .F-ob _ = Unit , λ{ tt tt _ _ → refl }
        Term .F-hom f tt = tt
        Term .F-id = refl
        Term .F-seq f g = refl

        -- gives you the new reference
        new : NatTrans Term (L ∘F F) 
        new = natTrans (λ x → inr) λ f → refl

        Cat : Category (ℓ-suc ℓ-zero) (ℓ-suc ℓ-zero) 
        Cat = (FUNCTOR (FinSetMono {ℓ-zero}) (SET ℓ-zero))

        -- this stuff is dumb, formulate using a map to a future world
        iterateF : (n : ℕ) → FinSet ℓ-zero → FinSet ℓ-zero 
        iterateF zero X = X
        iterateF (suc n) X =  F ⟅ iterateF n X ⟆ 

        F₀ⁿ : (A : ob Cat) → Functor (FinSetMono {ℓ-zero}) (SET ℓ-zero)
        F₀ⁿ A .F-ob k = (Σ[ n ∈ ℕ ] ( A ⟅ iterateF n k ⟆ ) .fst) , {!   !}
        F₀ⁿ A .F-hom = {!   !}
        F₀ⁿ A .F-id = {!   !}
        F₀ⁿ A .F-seq = {!   !}
        
        TF : Functor Cat Cat
        TF .F-ob = F₀ⁿ
        TF .F-hom f = natTrans (λ{ A' → λ {(n , a) → n , {!   !}}}) {!   !}
        TF .F-id = {!   !}
        TF .F-seq = {!   !}

        pluslemma : (A : ob Cat)(n m : ℕ)(X : FinSet ℓ-zero) → 
                (A ⟅ iterateF n (iterateF m X) ⟆) .fst → (A ⟅ iterateF (n + m) X ⟆) .fst
        pluslemma = {!   !}

        -- use extension system
        T : Monad Cat
        T = TF , record { 
                    η = natTrans (λ A → natTrans (λ n a → 0 , a) {!   !}) {!   !} ; 
                    μ = natTrans (λ A → natTrans (λ{n (m' , n' , a) → (n' + m') , pluslemma A n' m' n a}) {!   !}) {!   !} ; 
                    idl-μ = {!   !} ; 
                    idr-μ = {!   !} ; 
                    assoc-μ = {!   !} }

        -- the interpretation of alloc
        alloc : NatTrans Term (TF ⟅ L ⟆ )
        alloc = natTrans (λ k tt → 1 , (new ⟦ k ⟧) tt) λ f → {!   !}
