{-# OPTIONS --allow-unsolved-metas #-} 
module src.Data.HeytingAlg where 
    open import Cubical.Foundations.Prelude
    open import Cubical.Foundations.HLevels
    open import Cubical.Relation.Binary.Preorder
    open import Cubical.Foundations.Powerset
    open import Cubical.Algebra.Lattice
    open import Cubical.Functions.Logic hiding (⊥)
    open import Cubical.Data.Empty hiding (⊥)

    Poset : {ℓ  : Level} → Set (ℓ-suc ℓ)
    Poset {ℓ} = Σ[ P ∈ Preorder ℓ ℓ ] isUnivalent P

    -- See this could get messy with the order defined using equality...
    module PosetFromLattice {ℓ}(L : Lattice ℓ)(LisSet : isSet (L .fst)) where 
        open import Cubical.Relation.Binary.Base 
        --open import Cubical.Algebra.Semilattice.Base
        --open import Cubical.Algebra.CommMonoid.Base
        --open import Cubical.Algebra.Monoid.Base
        --open import Cubical.Algebra.Semigroup.Base
        open BinaryRelation hiding (isUnivalent)
        
        X : Set ℓ
        X = L .fst

        open LatticeStr (L .snd)

        _≤X_ : X → X → Set ℓ
        _≤X_ x y = x ≡ (x ∧l y)

        ref : isRefl _≤X_ 
        ref x = sym (∧lIdem  x) -- show x ≡ x ∧ x

        trn : isTrans _≤X_ 
        trn x y z x≤y y≤z = x≤y ∙ cong (x ∧l_) y≤z ∙ ∧lAssoc x y z ∙ cong (_∧l z) (sym x≤y)
            -- given x ≡ x ∧ y, y ≡ y ∧ z 
            -- prove x ≡ x ∧ z
            -- x ≡ x ∧ y ≡ x ∧ (y ∧ z) ≡ (x ∧ y) ∧ z ≡ x ∧ z
        
        pre : PreorderStr ℓ X 
        pre = preorderstr _≤X_ 
                (ispreorder (λ a b x y → LisSet a (a ∧l b) x y) 
                ref 
                trn)

        univ : isUnivalent (L .fst , pre)
        univ = record { univ = λ x y → {!   !}}
        
        P : Poset {ℓ}
        P = (X , pre) , univ

    -- based off of mathlib3
    -- https://github.com/leanprover-community/mathlib3/blob/65a1391a0106c9204fe45bc73a039f056558cb83/src/order/complete_lattice.lean#L85
    record CompleteLattice {ℓ}(Po : Poset {ℓ}) : Set(ℓ-suc ℓ) where 
        -- every subset has a least up

        open PreorderStr (Po .fst .snd)
        X = Po .fst .fst 
        XisSet = Po .fst .snd
        field 
            sup : ℙ X → X
            le_sup : (S : ℙ X)(x : X) → x ∈ S → x ≤ (sup S)
            -- uniqueness 
            sup_le : (S : ℙ X)(x : X) → ((y : X)→ y ∈ S → y ≤ x) → sup S ≤ x
            {- (le_Sup : ∀ s, ∀ a ∈ s, a ≤ Sup s)
            (Sup_le : ∀ s a, (∀ b ∈ s, b ≤ a) → Sup s ≤ a)  -}

            inf : ℙ X → X
            inf_le : (S : ℙ X)(x : X) → x ∈ S → inf S ≤ x
            -- uniqueness
            le_inf : (S : ℙ X)(x : X) → ((y : X) → y ∈ S → x ≤ y) → x ≤ inf S
            {- (Inf_le : ∀ s, ∀ a ∈ s, Inf s ≤ a)
                (le_Inf : ∀ s a, (∀ b ∈ s, a ≤ b) → a ≤ Inf s) -}


    record isHeytingAlg {ℓ}(X' : hSet ℓ ) : Set (ℓ-suc ℓ) where
        X = X' .fst
        field 
            islat : LatticeStr X
        module L = LatticeStr islat 
            renaming (
                1l to top ; 
                0l to bot )
        field 
            ⇒l : X → X → X
            l₁ : (x : X) → ⇒l x x ≡ L.top
            l₂ : (x y : X) → L._∧l_ x (⇒l x y) ≡ L._∧l_ x y
            l₃ : (x y : X) → L._∧l_ y (⇒l x y) ≡ y 
            l₄ : (x y z : X) → ⇒l x (L._∧l_ y z) ≡ L._∧l_ (⇒l x y) (⇒l x z)
        
        open PosetFromLattice 
        poset : Poset {ℓ}
        poset = P (X' .fst , islat) (X' .snd)

    record isCompleteHeytingAlg {ℓ}(X : hSet ℓ) : Set (ℓ-suc ℓ) where
        field 
            isHA : isHeytingAlg X 

        open isHeytingAlg isHA
            
        field 
            complete : CompleteLattice poset

    -- hmm ...
    -- See Lean definition of Heyting Algebra
    -- https://github.com/leanprover-community/mathlib4/blob/c1d47161522b8d5e570c10245776cc33c69ae085/Mathlib/Order/Heyting/Basic.lean
    -- The cubical agda library definition of lattice does not mention an order, 
    --      it is presented as an algebraic structure
    -- The lean library builds a lattice from a poset
    --  
    -- These two notions of lattice are convertible https://en.wikipedia.org/wiki/Lattice_(order)
    -- a ≤ b if a = a ∧ b
    -- OR altenate
    -- a ≤ b if b = a ∨ b
    -- https://en.wikipedia.org/wiki/Complete_Heyting_algebra
    -- For defining completenes.. it may be beter to work with the poset notion of lattice..?
    -- to algebraic presentation of lattice


        
    -- Definition 4.5. A complete Heyting algebra is a Heyting algebra that is complete as a lattice.
    -- A heyting algebra is a lattice but, with the addition of "implication" or a "right adjoint to meet"


    -- See Mathlib in Lean for definition of complete lattice
    -- https://github.com/leanprover-community/mathlib3/blob/65a1391a0106c9204fe45bc73a039f056558cb83/src/order/complete_lattice.lean#L85
    -- also fixpoints, which is dope 
    -- https://github.com/leanprover-community/mathlib3/blob/65a1391a0106c9204fe45bc73a039f056558cb83/src/order/fixed_points.lean#L45
   
   
    module PosetToLattice {ℓ}{Po : Poset {ℓ}} (C : CompleteLattice Po) where 
        open import Cubical.Algebra.Semilattice.Base
        open import Cubical.Algebra.CommMonoid.Base
        open import Cubical.Algebra.Monoid.Base
        open import Cubical.Algebra.Semigroup.Base
        open CompleteLattice C

        -- singleton
        ⟪_⟫ : X → ℙ X 
        ⟪ x ⟫ = λ y → x ≡ₚ y

        _∪_ : {X : Set ℓ} → ℙ X → ℙ X → ℙ X 
        A ∪ B = λ x → A x ⊔ B x

        ⊥ : hProp ℓ
        ⊥ = ⊥* , λ () 

        -- greatest element of the full set X
        top : X 
        top = sup λ _ → ⊤

        -- least element of the full set X
        bot : X 
        bot = inf λ _ → ⊥

        or : X → X → X 
        or x y = sup (⟪ x ⟫ ∪ ⟪ y ⟫)

        and : X → X → X 
        and x y = inf (⟪ x ⟫ ∪ ⟪ y ⟫)

        orSG : IsSemigroup or
        orSG = issemigroup {!   !} {!   !}
        -- λ x y z → cong sup (⊆-extensionality  _ _  ((λ x₁ x₂ → {!   !}) , {!   !}))

        orMon : IsMonoid bot or 
        orMon = ismonoid {!   !} {!   !} {!   !}

        orCmon : IsCommMonoid bot or 
        orCmon = iscommmonoid orMon {!   !}

        orSemi : IsSemilattice bot or
        orSemi = issemilattice orCmon {!   !}

        andSemi : IsSemilattice top and 
        andSemi = {!   !}

        islat : IsLattice bot top or and
        islat = islattice orSemi andSemi {!   !}

        lstr : LatticeStr X 
        lstr = latticestr 
            bot -- 0
            top -- 1 
            or -- or 
            and -- and 
            islat

        L : Lattice ℓ
        L = X , lstr
        