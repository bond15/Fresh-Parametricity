
{-
    module HDsyntax
        (𝓒 : Category _ _ ) 
        (term : Terminal 𝓒)
        (bp : BinProducts 𝓒)
        (exp : Exponentials 𝓒 bp )
        (Hyp : HyperDoctrine 𝓒 term bp exp) where

        open HyperDoctrine Hyp
        open FirstOrderHyperDoc isFO 
        open bpOps 𝓒 bp


        data Formula : ob 𝓒 → Set where 
            -- predicate
            ⊤  ⊥ : {X : ob 𝓒} → Formula X
            _&_ _||_ _⟹_ : {X : ob 𝓒} →  Formula X → Formula X → Formula X
            ≣_ : {X : ob 𝓒} → Formula X → Formula (X ×𝓒 X)
            ⋀_ ⋁_ : {Γ X : ob 𝓒} → Formula (Γ ×𝓒 X) → Formula Γ


        open import Cubical.Data.List

        fP : {Γ : ob 𝓒} → List (Formula Γ) → Formula Γ 
        fP [] = ⊤
        fP (x ∷ []) = x
        fP (x ∷ xs) = x & fP xs
{-
       -- derivations
        data _-_⊢_ : (Γ : ob 𝓒) → Formula Γ → Formula Γ →  Set where 
            exchange : {Γ : ob 𝓒}{xs ys : List (Formula Γ)}{φ : Formula Γ } → 
                Γ - fP(xs ++ ys) ⊢ φ → 
                ------------------
                Γ - fP(ys ++ xs) ⊢ φ  
            truth : {Γ : ob 𝓒}{xs : List (Formula Γ)} → 
                -----------------
                Γ - fP xs ⊢ ⊤
            andIntro : {Γ : ob 𝓒}{xs : List (Formula Γ)}{φ ψ : Formula Γ } → 
                Γ - fP xs ⊢ φ →  
                Γ - fP xs ⊢ ψ → 
                -----------------
                Γ - fP xs ⊢ (φ & ψ)
            andElim1 : {Γ : ob 𝓒}{xs : List (Formula Γ)}{φ ψ : Formula Γ } → 
                Γ - fP xs ⊢ (φ & ψ) → 
                -----------------
                Γ - fP xs ⊢ φ 

            andElim2 : {Γ : ob 𝓒}{xs : List (Formula Γ)}{φ ψ : Formula Γ } → 
                Γ - fP xs ⊢ (φ & ψ) → 
                -----------------
                Γ - fP xs ⊢ φ 

            -- this is cheating..?
         --   allIntro : {Γ X : ob 𝓒}{xs : List (Formula (Γ ×𝓒 X))}{φ : Formula (Γ ×𝓒 X) } → 
        --        (Γ ×𝓒 X ) - fP xs ⊢ φ → 
        --        Γ - {!   !} ⊢ (⋀ φ)
        -}
        -- derivations 
        data _-_⊢_ : (Γ : ob 𝓒) → List (Formula Γ) → Formula Γ →  Set where 
            exchange : {Γ : ob 𝓒}{xs ys : List (Formula Γ)}{φ : Formula Γ } → 
                Γ - xs ++ ys ⊢ φ → 
                ------------------
                Γ - ys ++ xs ⊢ φ  
            truth : {Γ : ob 𝓒}{xs : List (Formula Γ)} → 
                -----------------
                Γ - xs ⊢ ⊤
            andIntro : {Γ : ob 𝓒}{xs : List (Formula Γ)}{φ ψ : Formula Γ } → 
                Γ - xs ⊢ φ →  
                Γ - xs ⊢ ψ → 
                -----------------
                Γ - xs ⊢ (φ & ψ)
            andElim1 : {Γ : ob 𝓒}{xs : List (Formula Γ)}{φ ψ : Formula Γ } → 
                Γ - xs ⊢ (φ & ψ) → 
                -----------------
                Γ - xs ⊢ φ 

            andElim2 : {Γ : ob 𝓒}{xs : List (Formula Γ)}{φ ψ : Formula Γ } → 
                Γ - xs ⊢ (φ & ψ) → 
                -----------------
                Γ - xs ⊢ φ 

            -- this is cheating..?
            allIntro : {Γ X : ob 𝓒}{xs : List (Formula (Γ ×𝓒 X))}{φ : Formula (Γ ×𝓒 X) } → 
                (Γ ×𝓒 X ) - xs ⊢ φ → 
                Γ - map ⋀_ xs ⊢ (⋀ φ)

        
        module den {X  : ob 𝓒} where 
            open isHeytingAlg (isHA X)
            open LatticeStr islat
            _⇒'_ = ⇒l
            ⊤' = 1l
            ⊥' = 0l
            _∧'_ = _∧l_ 
            _∨'_ = _∨l_


        ⟪_⟫F : {Γ : ob 𝓒} → Formula Γ → (𝓟 .F-ob Γ .fst .fst)
        ⟪_⟫F {Γ} ⊤ =  ⊤' where open den{Γ}  
        ⟪_⟫F {Γ} ⊥ = ⊥' where open den{Γ}  
        ⟪_⟫F {Γ} (f₁ & f₂) = ⟪_⟫F {Γ} f₁ ∧' ⟪_⟫F {Γ} f₂ where open den{Γ}  
        ⟪_⟫F {Γ} (f₁ || f₂) = ⟪_⟫F {Γ} f₁ ∨' ⟪_⟫F {Γ} f₂ where open den{Γ}  
        ⟪_⟫F {Γ} (f₁ ⟹ f₂) = ⟪_⟫F {Γ} f₁ ⇒' ⟪_⟫F {Γ} f₂ where open den{Γ} 
        ⟪_⟫F {Γ} (≣_ {X = X} f) = MonFun.f (=F {X}) (⟪_⟫F {X} f)
        ⟪_⟫F {Γ} (⋀_ {X = X} f) = MonFun.f (∀F {Γ}{X}) (⟪_⟫F {Γ ×𝓒 X} f)
        ⟪_⟫F {Γ} (⋁_ {X = X} f) = MonFun.f (∃F {Γ}{X}) (⟪_⟫F {Γ ×𝓒 X} f)  


        _≤F_ : {Γ : ob 𝓒} → 𝓟 .F-ob Γ .fst .fst →  𝓟 .F-ob Γ .fst .fst → Set 
        _≤F_ {Γ} = 𝓟 .F-ob Γ .fst .snd ._≤_

        module rules {Γ : ob 𝓒} (x y : 𝓟 .F-ob Γ .fst .fst ) where 
            open den{Γ}
            
            top : x ≤F ⊤'
            top = {!   !}

        ⟪⟫D : {Γ : ob 𝓒}{xs : List (Formula Γ)}{ φ : Formula Γ} → Γ - xs ⊢ φ → (⟪_⟫F (fP xs)) ≤F (⟪_⟫F φ)
        ⟪⟫D {Γ} {.(_ ++ _)} {φ} (exchange d) = {!   !}
        ⟪⟫D {Γ} {xs} {.⊤} truth = {! top  !}
        ⟪⟫D {Γ} {xs} {.(_ & _)} (andIntro d d₁) = {!   !}
        ⟪⟫D {Γ} {xs} {φ} (andElim1 d) = {!   !}
        ⟪⟫D {Γ} {xs} {φ} (andElim2 d) = {!   !}
        ⟪⟫D {Γ} {.(map ⋀_ _)} {.(⋀ _)} (allIntro d) = {!   !}
   -} 

   {-
        
        sub : Set → Set 
        sub X = X → Bool

        _∈'_ : {X : Set} → X → sub X → Set 
        x ∈' f = Bool→Type (f x)

        dec∈' : {X : Set} → (x : X) → (f : sub X) → Dec (x ∈' f)
        dec∈' x f = DecBool→Type {f x}

        ex : sub ℕ 
        ex (suc zero) = true 
        ex _ = false

        _ : 1 ∈' ex 
        _ = tt
        -- no.. potentially infinite
        finmap = Σ[ D ∈ sub ℕ ] ((n : ℕ) → n ∈' D → X)
        
        dom : finmap → sub ℕ 
        dom = fst

        _∩'_ : {X : Set} → sub X → sub X → sub X 
        _∩'_ f g x = f x and g x

        ∅' : {X : Set} → sub X 
        ∅' x = false

        _#_ : (f g : finmap) → Set 
        f # g = dom f ∩' dom g ≡ ∅'


            -- dom f ∩ dom g ≡ ∅ 

      

        finmap = Σ[ N ∈ ℙ ℕ ] ((n : ℕ)→ n ∈ N → X) 

        dom : finmap → ℙ ℕ 
        dom = fst

        _#_ : (f g : finmap) → Set 
        f # g = dom f ∩ dom g ≡ ∅ 

        isProp# : {f g : finmap} → isProp (f # g)
        isProp# = isSetℙ _ _

 

        decℕ : (x y : ℕ) → Dec (x ≡ y)
        decℕ zero zero = yes refl
        decℕ zero (suc y) = no (znots {y})
        decℕ (suc x) zero = no (snotz {x})
        decℕ (suc x) (suc y) with (decℕ x y)
        decℕ (suc x) (suc y) | yes p = yes (cong suc p)
        decℕ (suc x) (suc y) | no notp = no λ p → notp (injSuc p)


        decSub : (f g : sub ℕ) → Dec (f ≡ g)
        decSub f g = {!  !}

        decHprop : (p q : hProp _) → Dec (p ≡ q)
        decHprop p q = {!   !}

        --DecidablePropositions
      --  _ = {! Dec !}
     --   isDecℙℕ : (X Y : ℙ ℕ) → Dec (X ≡ Y)
     --   isDecℙℕ X Y = {! X  !}
      -}      