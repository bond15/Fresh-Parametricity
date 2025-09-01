{-# OPTIONS --type-in-type #-}
module src.Data.Glue where 
    open import Cubical.Foundations.Prelude hiding (Sub)
    -- the following is from Gluing for Type Theory
    -- see also 
   --  Type Theory in Type Theory using Quotient Inductive Types
    -- in the simply typed case, we don't need type to depend on context...
    -- context extension will be normal product instead of dependent product
    record Syn {ℓ} : Set (ℓ-suc ℓ)  where 
        field 
            Con : Set ℓ
            Ty : Con → Set ℓ
            Sub : Con → Con → Set ℓ
            Tm : (Γ : Con) → Ty Γ → Set ℓ

            id : {Γ : Con} → Sub Γ Γ 
            _∘_ : {Γ Δ Θ : Con} → Sub Θ Δ → Sub Γ Θ → Sub Γ Δ

            ass : {Γ Δ Θ Φ : Con}{c : Sub Γ Δ}{b : Sub Δ Θ}{a : Sub Θ Φ} → 
                ((a ∘ b) ∘ c) ≡ (a ∘ (b ∘ c))
            idl : {Γ Δ : Con}{a : Sub Γ Δ} → 
                id ∘ a ≡ a
            idr : {Γ Δ : Con}{a : Sub Γ Δ} → 
                a ∘ id ≡ a

            -- type substitution
            _[_]ty : {Γ Δ : Con} → 
                Ty Δ → Sub Γ Δ → Ty Γ
            -- tm substitution 
            _[_]tm : {Γ Δ : Con}{A : Ty Δ} → 
                Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]ty)

            -- type substitution rules
            TySubId : {Γ : Con}{A : Ty Γ} → 
                A [ id ]ty ≡ A 
            TySubHom : {Γ Δ Θ : Con}{A : Ty Δ}{b : Sub Θ Δ}{a : Sub Γ Θ} → 
                (A [ b ∘ a ]ty) ≡ (A [ b ]ty) [ a ]ty

            -- term substitution rules
            TmSubId : {Γ : Con}{A : Ty Γ}{a : Tm Γ A} →
                PathP 
                    (λ i → Tm Γ (TySubId{Γ}{A}i)) 
                    (a [ id ]tm) 
                    a
            TmSubHom : {Γ Δ Θ : Con}{A : Ty Δ}{a : Tm Δ A}{g : Sub Θ Δ}{f : Sub Γ Θ} →
                PathP 
                    (λ i → Tm Γ (TySubHom{Γ}{Δ}{Θ}{A}{g}{f} i)) 
                    (a [ g ∘ f ]tm) 
                    ((a [ g ]tm) [ f ]tm) 

            -- empty context 
            ∅ : Con 
            -- terminal substitution morphism
            ε : {Γ : Con} → Sub Γ ∅ 
            ∅η : {Γ : Con}{σ : Sub Γ ∅} → σ ≡ ε

            -- context extension
            -- \t5
            _▸_  : (Γ : Con) → (Ty Γ) → Con 
            -- extend substitution
            _,,_ : {Γ Δ : Con}{A : Ty Δ} →
                (σ : Sub Γ Δ) → Tm Γ (A [ σ ]ty) → Sub Γ (Δ ▸ A)

            -- context projection, type
            p : {Γ : Con}{A : Ty Γ} →
                Sub (Γ ▸ A) Γ
            -- context projection, term
            q : {Γ : Con}{A : Ty Γ} →
                Tm (Γ ▸ A) (A [ p ]ty)

            -- rules for projection
            ▸β₁ : {Γ Δ : Con}{A : Ty Δ}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]ty)} →
                p ∘ (σ ,, t) ≡ σ
            ▸β₂ : {Γ Δ : Con}{A : Ty Δ}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]ty)} →
            -- ((A [ p ]ty) [ σ ,, t ]ty) ＝ A [ σ ]ty
            -- via TySubHom : (A₁ [ b ∘ a ]ty) ≡ ((A₁ [ b ]ty) [ a ]ty)
            -- and ▸β₁ :  p ∘ (σ ,, t) ≡ σ
                PathP 
                    (λ i → Tm Γ ((sym (TySubHom {b = p}{σ ,, t}) ∙ cong (λ h → A [ h ]ty) ▸β₁) i)) 
                    (q [ σ ,, t ]tm) 
                    t
        -- types
            -- Unit
            unit : {Γ : Con} → Ty Γ 
            ttt : {Γ : Con} → Tm Γ unit
            -- computation rules
            unitη : {Γ : Con}{ x : Tm Γ unit} → 
                x ≡ ttt
            -- substitution rules
            TySubUnit : {Γ Δ : Con}{σ : Sub Γ Δ} → 
                unit [ σ ]ty ≡ unit
            TmSubTTT : {Γ Δ : Con}{σ : Sub Γ Δ} →  
                PathP 
                    (λ i → Tm Γ (TySubUnit {Γ}{Δ}{σ} i))
                    (ttt {Δ} [ σ ]tm)
                    (ttt {Γ})

            -- Pair 
            -- formation rule
            _⊗_ : {Γ : Con} → 
                Ty Γ → Ty Γ → Ty Γ
            -- intro rule
            _/_ : {Γ : Con}{A B : Ty Γ} → 
                Tm Γ A → Tm Γ B → Tm Γ (A ⊗ B)
            -- elim rules
            p1 : {Γ : Con}{A B : Ty Γ} → 
                Tm Γ (A ⊗ B) → Tm Γ A
            p2 : {Γ : Con}{A B : Ty Γ} → 
                Tm Γ (A ⊗ B) → Tm Γ B
            -- computation rules
            ⊗β₁ : {Γ : Con}{A B : Ty Γ}{M : Tm Γ A}{N : Tm Γ B} →
                p1 (M / N) ≡ M
            ⊗β₂ : {Γ : Con}{A B : Ty Γ}{M : Tm Γ A}{N : Tm Γ B} →
                p2 (M / N) ≡ N
            ⊗η : {Γ : Con}{A B : Ty Γ}{pp : Tm Γ (A ⊗ B)} →
                p1 pp / p2 pp ≡ pp
            -- substitution rules
                -- type constructor ("commutes" is homo?) w.r.t. substitution
            -- if this was monoidal instead of cartesian
            -- and our model for the monoidal product was day convolution
            -- then this substitution property does not hold
            TySub⊗ : {Γ Δ : Con}{A B : Ty Δ}{σ : Sub Γ Δ} → 
                (A ⊗ B) [ σ ]ty ≡ ((A [ σ ]ty) ⊗ (B [ σ ]ty))
            TmSub⊗ : {Γ Δ : Con}{A B : Ty Δ}{a : Tm Δ A}{b : Tm Δ B}{σ : Sub Γ Δ} →  
                PathP 
                    (λ i → Tm Γ (TySub⊗ {Γ}{Δ}{A}{B}{σ} i))
                    ((a / b) [ σ ]tm) -- Tm Γ ((A ⊗ B) [ σ ]ty)
                    ((a [ σ ]tm) / (b [ σ ]tm)) -- Tm Γ ((A [ σ ]ty) ⊗ (B [ σ ]ty))

    module  syntacticProgram (S : Syn) where 
        open Syn S

        prog : {Γ : Con} → Tm Γ (unit ⊗ (unit ⊗ unit)) 
        prog = ttt / (ttt / ttt)

    -- there is a recursor that is the unique map
    open Syn
    record Map (M N : Syn) : Set₁ where 
        module M = Syn M 
        module N = Syn N 
        field 
            H : M.Con → N.Con
            HTy : (Γ : M.Con) → M.Ty Γ → N.Ty (H Γ)
            HSub : (Γ Δ : M.Con) → M.Sub Γ Δ → N.Sub (H Γ) (H Δ)
            HTm : (Γ : M.Con)(A : M.Ty Γ) → M.Tm Γ A → N.Tm (H Γ) (HTy Γ A)
        -- which preserve all the equations

    -- there is an eliminator that is the unique section
    record DisplayedMap (M : Syn) : Set₁ where 
        module M = Syn M 
        field 
            D : M.Con → Set
            DTY : {Γ : M.Con} → D Γ → M.Ty Γ → Set
            DSub : {Γ Δ : M.Con} → D Γ → D Δ → M.Sub Γ Δ → Set
            DTm : {Γ : M.Con}{A : M.Ty Γ}→ (ΓQ : D Γ) → DTY {Γ} ΓQ A → M.Tm Γ A → Set 

    record Section (M : Syn) (DM : DisplayedMap M) : Set₁ where
        module M = Syn M
        module DM = DisplayedMap DM
        field 
            I' : (Γ : M .Con) → DM.D Γ
            ITy : {Γ : M.Con} → (A : M.Ty Γ) → DM.DTY {Γ} (I' Γ) A
            ISub : {Γ Δ : M.Con} → (σ : M.Sub Γ Δ) → DM.DSub (I' Γ) (I' Δ) σ

    module _ where
        -- Monoid
        record Monoid : Set where 
            field 
                carrier : Set

        -- Free Monoid
        data Fm (X : Set): Set where
            i_ : X → Fm X 
            e : Fm X 
            _⊕_ : Fm X → Fm X → Fm X 
            -- equations
            idl' : (x : Fm X) → e ⊕ x ≡ x
            idr' : (x : Fm X) → x ⊕ e ≡ x
            assoc' : (x y z : Fm X) → x ⊕ (y ⊕ z) ≡ (x ⊕ y) ⊕ z
            -- truncate
            -- trunc : isSet (Fm X)
        open import Cubical.Data.Bool hiding (_⊕_)
        
        B = Fm Bool

        ex : ( i true) ⊕ ((i false) ⊕ e) ≡ (i true) ⊕ (i false)
        ex = cong ((i true) ⊕_) (idr' _)

        


        

    -- Initial Model
    data Init : Set where 


    -- The Set Model
    open import Cubical.Data.Unit 
    open import Cubical.Data.Sigma hiding (Sub)

    -- simply typed version.. no type dependency on context
    SetModel : Syn 
    SetModel .Con = Set₀
    SetModel .Ty _ = Set₀
    SetModel .Sub Γ Δ = Γ → Δ
    SetModel .Tm Γ A = Γ → A
    SetModel .id Γ = Γ
    SetModel ._∘_ f g = λ z → f (g z)
    SetModel .ass = refl
    SetModel .idl = refl
    SetModel .idr = refl 
    SetModel ._[_]ty = λ z _ → z
    SetModel ._[_]tm = λ z σ γ → z (σ γ)
    SetModel .TySubId = refl
    SetModel .TySubHom = refl
    SetModel .TmSubId = refl
    SetModel .TmSubHom = refl
    SetModel .∅ = Unit    
    SetModel .ε = λ x → tt
    SetModel .∅η = funExt λ _ → refl
    SetModel ._▸_ Γ A = Γ × A   
    SetModel ._,,_ = λ σ z z₁ → σ z₁ , z z₁  
    SetModel .p = fst
    SetModel .q = snd
    SetModel .▸β₁ = refl
    SetModel .▸β₂ = {!   !}
    SetModel .unit = Unit
    SetModel .ttt γ = tt
    SetModel .unitη = refl
    SetModel .TySubUnit = refl
    SetModel .TmSubTTT = refl
    SetModel ._⊗_ A B = A × B 
    SetModel ._/_ = λ z z₁ γ → z γ , z₁ γ
    SetModel .p1 = λ z γ → fst (z γ)
    SetModel .p2 = λ z γ → snd (z γ)
    SetModel .⊗β₁ = refl
    SetModel .⊗β₂ = refl
    SetModel .⊗η = refl
    SetModel .TySub⊗ = refl
    SetModel .TmSub⊗ = refl

    open syntacticProgram SetModel
    _ : prog {Unit} ≡ λ _ → tt , (tt , tt)
    _ = refl

    {-}
    -- context with type dependnency
    SetModel : Syn 
    SetModel .Con = Set₀
    SetModel .Ty Γ = Γ → Set₀
    SetModel .Sub Γ Δ = Γ → Δ
    SetModel .Tm Γ A = (γ : Γ) → A γ
    SetModel .id Γ = Γ
    SetModel ._∘_ f g = λ z → f (g z)
    SetModel .ass = refl
    SetModel .idl = refl
    SetModel .idr = refl 
    SetModel ._[_]ty = λ z z₁ z₂ → z (z₁ z₂)
    SetModel ._[_]tm = λ z σ γ → z (σ γ)
    SetModel .TySubId = refl
    SetModel .TySubHom = refl
    SetModel .TmSubId = refl
    SetModel .TmSubHom = refl
    SetModel .∅ = Unit    
    SetModel .ε = λ x → tt
    SetModel .∅η = funExt λ _ → refl
    SetModel ._▸_ Γ A = Σ[ γ ∈ Γ ] A γ  
    SetModel ._,,_ = λ σ z z₁ → σ z₁ , z z₁  
    SetModel .p = fst
    SetModel .q = snd
    SetModel .▸β₁ = refl
    SetModel .▸β₂ = {!   !}
    SetModel .unit Γ = Unit
    SetModel .ttt γ = tt
    SetModel .unitη = refl
    SetModel .TySubUnit = refl
    SetModel .TmSubTTT = refl
    SetModel ._⊗_ A B Γ = A Γ × B Γ
    SetModel ._/_ = λ z z₁ γ → z γ , z₁ γ
    SetModel .p1 = λ z γ → fst (z γ)
    SetModel .p2 = λ z γ → snd (z γ)
    SetModel .⊗β₁ = refl
    SetModel .⊗β₂ = refl
    SetModel .⊗η = refl
    SetModel .TySub⊗ = refl
    SetModel .TmSub⊗ = refl -}

{-}
            --Bool
            bool : {Γ : Con} → Ty Γ

            tru : {Γ : Con} → Tm Γ bool 
            fls : {Γ : Con} → Tm Γ bool

            TySubBool : {Γ Δ : Con}{σ : Sub Γ Δ} → 
                bool [ σ ]ty ≡ bool

            TmSubTru : {Γ Δ : Con}{σ : Sub Γ Δ} →  
                PathP 
                    (λ i → Tm Γ (TySubBool {Γ}{Δ}{σ} i))
                    (tru {Δ} [ σ ]tm)
                    (tru {Γ})
            TmSubFls : {Γ Δ : Con}{σ : Sub Γ Δ} →  
                PathP 
                    (λ i → Tm Γ (TySubBool {Γ}{Δ}{σ} i))
                    (fls {Δ} [ σ ]tm)
                    (fls {Γ})
-}
  

            
           
            

             