{-# OPTIONS --type-in-type #-}
module src.Data.Iris where

open import Cubical.Data.Nat 
open import Cubical.Relation.Binary
open import Cubical.Data.Sigma
open import Cubical.Data.Nat.Order
open import Cubical.Functions.Logic
open BinaryRelation
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Relation.Binary.Order.Poset
open import  Cubical.Foundations.Powerset
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Categories.Category

-- just use prop valued relations?
open PosetDownset

module _ {ℓ} where 
    _⊆R_ : {X : Set ℓ} → (R R' : PropRel X X ℓ) → Set ℓ
    _⊆R_ {X} R R' = ((x y : X) → R .fst x y → R' .fst x y) 
    --, isPropΠ2 λ x y  → isProp→ (R' .snd x y)



    record OFE  : Set (ℓ-suc ℓ) where
        field 
            X : hSet ℓ
            Rn : (n : ℕ) → PropRel (fst X) (fst X) ℓ
        R⟨_⟩ : ℕ → Rel (fst X) (fst X) ℓ
        R⟨ n ⟩ = Rn n .fst
        field --isProp≤ 
            eqv : (n : ℕ) → isEquivRel (R⟨ n ⟩ )
            mon : (n m : ℕ) → n ≤ m → Rn m ⊆R Rn n
            lim : (x y : fst X) → ((x ≡ y) →  ((n : ℕ) → R⟨ n ⟩ x y)) × (((n : ℕ) → R⟨ n ⟩ x y)→ x ≡ y)

    open OFE

    discreteElem : {O : OFE} → O .X .fst → Set 
    discreteElem {O} x = (y : O .X .fst) → O .Rn 0 .fst x y → x ≡ y

    isDiscrete : OFE → Set
    isDiscrete O = (x : O .X .fst) → discreteElem {O} x

    -- this is a functor that is full and faithful
    D : (S : hSet _) → OFE 
    D S .X = S
    D S .Rn n = _≡_ , S .snd
    D S .eqv n = equivRel (λ _ → refl) (λ _ _ → sym) λ _ _ _ → _∙_
    D S .mon n m n≤m p q p≡q = p≡q
    D S .lim n m = (λ x _ → x) , λ f → f 0

    DisDiscrete : (S : hSet _) → isDiscrete (D S) 
    DisDiscrete S x y x≡y = x≡y

    record nonExpansive (A B : OFE) : Set where 
        private
            module A = OFE A 
            module B = OFE B
        field 
            fn : A.X .fst → B.X .fst 
            ne : (n : ℕ)(x y : A.X .fst) → A.R⟨ n ⟩ x y → B.R⟨ n ⟩ (fn x) (fn y)
    open nonExpansive 

    record contractive {A B : OFE}(f : A .X .fst → B .X .fst) : Set where
        private 
            module A = OFE A 
            module B = OFE B
        field 
            cont : (n : ℕ)(x y : A.X .fst) → ((m : ℕ)→ m < n → A.R⟨ m ⟩ x y) → B.R⟨ n ⟩ (f x) (f y)

    idne : {O : OFE} → nonExpansive O O 
    idne .fn x = x
    idne .ne _ _ _ x = x

    ofecomp : {P Q R : OFE} → nonExpansive P Q → nonExpansive Q R → nonExpansive P R 
    ofecomp record { fn = f ; ne = fne } record { fn = g ; ne = gne } = record { fn = λ z → g (f z) ; ne = λ n x y z → gne n (f x) (f y) (fne n x y z) }

    ne≡ : {A B : OFE}{f g : nonExpansive A B} → (f .fn ≡ g .fn) → f ≡ g 
    ne≡ p i .fn = p i
    ne≡ {A}{B}{f}{g} p i .ne n x y RAnxy = isProp→PathP (λ i → B .Rn n .snd (p i x) (p i y)) (f .ne n x y RAnxy) (g .ne n x y RAnxy) i


   -- record Chain (T : hSet _) : Set where
  --      field 
  --          crel : (n : ℕ) → PropRel (fst T) (fst T) ℓ
 --           crelequiv : (n : ℕ) → isEquivRel (crel n .fst )

    Chain : (T : Set) → (eqR : Σ[ R ∈ ((n : ℕ) → PropRel T T ℓ) ] ((n : ℕ) → isEquivRel (R n .fst)) ) → Set
    Chain T (R , eqR) = Σ[ c ∈ (ℕ → T) ] ((n m : ℕ) → n ≤ m → R n .fst (c m) (c n))

    record COFE : Set where 
        field 
            ofe : OFE 
        Chain' = Chain (ofe .X .fst) ((ofe .Rn) , ofe .eqv)
        field 
            clim : Chain' → ofe .X .fst
            cofe-compl : (n : ℕ)(c : Chain') → ofe .Rn n .fst (clim  c) (c .fst n)
            
            
    
    -- could just have this as a displayed category over SET
    open Category
    OFECat : Category _ _ 
    OFECat .ob = OFE
    OFECat .Hom[_,_] = nonExpansive
    OFECat .id = idne
    OFECat ._⋆_ = ofecomp
    OFECat .⋆IdL f = ne≡ refl
    OFECat .⋆IdR f = ne≡ refl
    OFECat .⋆Assoc f g h = ne≡ refl
    OFECat .isSetHom = λ x₁ y₁ x₂ y₂  → {!   !}

    -- step indexed propositions
    -- downwards closed sets
    SProp : hSet _
    SProp = (Σ[ X ∈ ℙ ℕ ] ((n m : ℕ) → m ≤ n → n ∈ X → m ∈ X)) , {!   !}


    R' : ℕ → PropRel (SProp .fst) (SProp .fst) ℓ
    R' n = r , rprop where
        r : Rel (SProp .fst) (SProp .fst) ℓ 
        r (X , _) (Y , _) = (m : ℕ) → m ≤ n → ((m ∈ X) → (m ∈ Y)) × ((m ∈ Y) → (m ∈ X))

        rprop : (a b : fst SProp) → isProp (r a b) 
        rprop a b = isPropΠ λ z → isProp→ (isProp× (isProp→ (∈-isProp (fst b) z)) (isProp→ (∈-isProp (fst a) z)) )

    _∘s_ :{A B C : Set} → (A → B) → (B → C) → A → C 
    _∘s_ = λ z z₁ z₂ → z₁ (z z₂)

    ex : OFE 
    ex .X = SProp
    ex .Rn = R'
    ex .eqv n = 
        equivRel 
            ref
            sn 
            tn where 

        ref : isRefl (R' n .fst) 
        ref X m m≤n = X .snd m m  ≤-refl , X .snd m m  ≤-refl

        sn : isSym (R' n .fst) 
        sn X Y RnXY m m≤n = RnXY m m≤n .snd , RnXY m m≤n .fst

        tn : isTrans (R' n .fst)
        tn X Y Z RnXY RnYZ m m≤n = (RnXY m m≤n .fst ∘s RnYZ m m≤n .fst) , (RnYZ m m≤n .snd ∘s RnXY m m≤n .snd)

    ex .mon n m n≤m X Y RmXY p p≤n = RmXY p (≤-trans p≤n n≤m) .fst , RmXY p (≤-trans p≤n n≤m) .snd
    ex .lim (X , sX) (Y , sY) = g1 , g2 where 
        g1 : (X , sX) ≡ (Y , sY) → (n : ℕ) → Rn ex n .fst (X , sX) (Y , sY)
        g1 X≡Y n m m≤n = subst (λ h → m ∈ h) (cong fst X≡Y) , subst (λ h → m ∈ h) (cong fst (sym X≡Y)) 


        g2 : ((n : ℕ) → Rn ex n .fst (X , sX) (Y , sY)) → (X , sX) ≡ (Y , sY)
        g2 f = cong₂ _,_ (funExt λ n → ⇔toPath {P = X n}{Q = Y n} (f n n ≤-refl .fst) ((f n n ≤-refl .snd))) 
                (isProp→PathP (λ i → isPropΠ2 λ x y → isProp→ (isProp→ (∈-isProp (funExt (λ n → ⇔toPath {P = X n}{Q = Y n}(f n n ≤-refl .fst) (f n n ≤-refl .snd)) i) y))) sX sY)


    spropCoffe : COFE 
    spropCoffe = record { 
        ofe = ex ; 
        clim = λ{(f∶ℕ→sProp , fisChain) → (λ n → f∶ℕ→sProp n .fst n) , (λ n m m≤n x∈ → {!   !}) }; 
        cofe-compl = {!   !} }


    open import Cubical.Data.Maybe renaming (elim to melim)
    open import Cubical.Data.Unit 
    open import Cubical.Data.Empty renaming (⊥ to Empty)

    isJust : {A : Set} → Maybe A → Set 
    isJust nothing = Empty 
    isJust _ = Unit 


    record RA : Set where 
        field 
            M : Set 
            𝓥 : M → hProp _ 
            ||_|| : M → Maybe M
            _⊚_ : M → M → M
            ra-assoc : (a b c : M) → (a ⊚ b) ⊚ c ≡ a ⊚ (b ⊚ c)
            ra-comm : (a b : M) → a ⊚ b ≡ b ⊚ a 
            --ra-core-id : (a : M) → isJust (|| a ||) → {!  !}

    singleton : ℕ → ℙ ℕ
    singleton n m = n ≡ₚ m

    lessThan : ℕ → ℙ ℕ
    lessThan n m = (m ≤ n) , isProp≤

    p : fst SProp 
    p = (lessThan 7) , λ{ n m m≤n (q , q+n≡7) → q , {!   !} }
    --p = singleton 7 , λ n m m≤n n∈sing7 → ∣ {!   !} ∣₁
    exdisc : discreteElem {ex} {!   !}
    exdisc  = λ y x  → {!   !}



{-
    Pℕ : Poset _ _ 
    Pℕ = (ℙ ℕ) , posetstr _⊆_ (isposet isSetℙ ⊆-isProp ⊆-refl (λ _ _ _ P Q x z → Q x (P x z)) λ a b  P Q → ⊆-extensionality a b  (P , Q)) 

    P↓ℕ : Poset _ _ 
    P↓ℕ = {! ↓ᴾ Pℕ  !}
-}

