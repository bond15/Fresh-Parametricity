module src.Data.Free where 
    open import Cubical.Foundations.Prelude hiding (Sub)
    open import Cubical.Data.Bool hiding (_⊕_)

    record Monoid : Set₁ where 
        field 
            M : Set
            e : M
            _⊗_ : M → M → M
        -- equations
            idl : (x : M) → e ⊗ x ≡ x
            idr : (x : M) → x ⊗ e ≡ x
            assoc : (x y z : M) → x ⊗ (y ⊗ z) ≡ (x ⊗ y) ⊗ z

    -- Free Monoid on a set X
    data F (X : Set): Set where
        i_ : X → F X 
        e : F X 
        _⊗_ : F X → F X → F X 
        -- equations
        idl : (x : F X) → e ⊗ x ≡ x
        idr : (x : F X) → x ⊗ e ≡ x
        assoc : (x y z : F X) → x ⊗ (y ⊗ z) ≡ (x ⊗ y) ⊗ z
        -- truncate
        -- trunc : isSet (Fm X)

    module exbool where 
        B = F Bool

        ex : ( i true) ⊗ ((i false) ⊗ e) ≡ (i true) ⊗ (i false)
        ex = cong ((i true) ⊗_) (idr _)

    -- The free monoid is a monoid
    free : (X : Set) → Monoid 
    free X = record { M = F X ; e = e ; _⊗_ = _⊗_ ; idl = idl ; idr = idr ; assoc = assoc }

    -- homomorphism
    record MonoidMorphism (M N : Monoid) : Set₁ where
        module M = Monoid M 
        module N = Monoid N
        field
            f : M.M → N.M
            -- equations
            pe : f (M.e) ≡ N.e
            p⊗ : (x y : M.M) → f(x M.⊗ y) ≡ ((f x) N.⊗ (f y))


    {-
        Say we have a free monoid over some type X
        Given 
            - some other Monoid M
            - a way to map from elements of X to elements of the carrier of Monoid M
        we get a monoid homomorphism from (free X) to M
    -}
    rec : {X : Set} → (M : Monoid)(m : X → Monoid.M M) → F X → Monoid.M M
    rec {X} M m = go
        where 
            module M = Monoid M
            go : F X → M.M
            go (i x) = m x
            go e = M.e
            go (x ⊗ y) = go x M.⊗ go y
            go (idl x p) = M.idl (go x) p
            go (idr x p) = M.idr (go x) p
            go (assoc x y z p) = M.assoc (go x) (go y) (go z) p
    
    -- recursor for F 
    recF : {X : Set} → (M : Monoid)(m : X → Monoid.M M) → MonoidMorphism (free X) M 
    recF {X} M m = record { f = rec {X} M m ; pe = refl ; p⊗ = λ _ _ → refl}


    -- monoids to map to..
    open import Cubical.Data.Nat 
    nat : Monoid 
    nat = record { 
            M = ℕ ; 
            e = 0 ; 
            _⊗_ = _+_ ; 
            idl = λ _ → refl ; 
            idr = +-zero ; 
            assoc = +-assoc }

    open import Cubical.Data.List hiding (rec)
    list : {X : Set} → Monoid 
    list {X} = record { M = List X ; e = [] ; _⊗_ = _++_ ; idl = λ _ → refl ; idr = ++-unit-r ; assoc = λ x y z → sym (++-assoc x y z) }

    -- term of the free monoid over bool
    ex : F Bool
    ex = ((i true)  ⊗ e) ⊗ ((i false) ⊗ (i false))

    -- mapping Bool to nat 
    bn : Bool → ℕ 
    bn false = 7 
    bn true = 3

    -- recursor into nats
    recFℕ : (Bool → ℕ) → MonoidMorphism (free Bool) nat
    recFℕ = recF {Bool} nat
  
    recℕ : (Bool → ℕ) → (F Bool → ℕ)
    recℕ m = MonoidMorphism.f (recFℕ m)

    _ : recℕ bn ex ≡ 17 
    _ = refl 

    bl : Bool → List ℕ 
    bl false = 7 ∷ 2 ∷ [] 
    bl true = 1 ∷ 1 ∷ 1 ∷ 1 ∷ []

    _ : rec (list {ℕ}) bl ex ≡ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 7 ∷ 2 ∷ 7 ∷ 2 ∷ []
    _ = refl