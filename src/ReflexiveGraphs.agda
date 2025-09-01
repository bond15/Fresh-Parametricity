module src.ReflexiveGraphs where
    open import Cubical.Foundations.Prelude
    open import Cubical.Data.Sigma 
    open import Cubical.Foundations.HLevels

    module _ {ℓ : Level} where 

        record rgraph : Set ((ℓ-suc (ℓ-suc ℓ))) where
            field 
                V E : Set (ℓ-suc ℓ) 
               -- E : Set (ℓ-suc (ℓ-suc ℓ))
                ∂₀ ∂₁ : E → V
                Id : V → E
                prop1 : {A : V} → (∂₀ (Id A) ≡ A) 
                prop2 : {A : V} → (∂₁ (Id A) ≡ A)

        open rgraph

        record relator (A B : rgraph) : Set ((ℓ-suc (ℓ-suc ℓ))) where 
            field 
                Fv : A . V → B .V  
                Fe : A . E → B .E 
                F₀ : {r : A .E} → (B .∂₀) (Fe r) ≡ Fv ((A .∂₀ r)) 
                F₁ : {r : A .E} → (B .∂₁) (Fe r) ≡ Fv ((A .∂₁ r)) 
                Fi : {a : A .V} → Fe (A .Id a) ≡ B .Id (Fv a)

        open relator

        relator≡ : {A B : rgraph}{f g : relator A B} → 
            f .Fv ≡ g .Fv → 
            f .Fe ≡ g .Fe → 
            f ≡ g 
        relator≡ = {!   !}

        IDrelator : {A : rgraph} → relator A A 
        IDrelator {A} .Fv v = v
        IDrelator {A} .Fe e = e
        IDrelator {A} .F₀ = refl
        IDrelator {A} .F₁ = refl
        IDrelator {A} .Fi = refl
        open import Cubical.Foundations.Function

        relcomp : {A B C : rgraph} → relator A B → relator B C → relator A C 
        relcomp {A} {B}{C} f g .Fv = g .Fv ∘S f .Fv
        relcomp {A} {B}{C} f g .Fe = g .Fe ∘S f .Fe
        relcomp {A} {B}{C} f g .F₀ = {!   !}
        relcomp {A} {B}{C} f g .F₁ = {!   !}
        relcomp {A} {B}{C} f g .Fi = {!   !}
                
        open import Cubical.Categories.Category
        open Category
        
        RG : Category _ _ 
        RG .ob = rgraph
        RG .Hom[_,_] = relator
        RG .id = IDrelator
        RG ._⋆_ = relcomp
        RG .⋆IdL _ = relator≡ refl refl
        RG .⋆IdR _ = relator≡ refl refl
        RG .⋆Assoc _ _ _ = relator≡ refl refl
        RG .isSetHom = {!   !}

        --record paramTrans {𝓕 𝓖 : ob RG}{F G : relator 𝓕 𝓖} : Set ℓ where 
        --    field 
        --        η : (A : 𝓕 .V) → {! F .Fv A → ? !}


        RG× : ob RG → ob RG → ob RG 
        RG× X Y = record{ 
                    V = X . V × Y .V
                    ; E = X .E × Y .E
                    ; ∂₀ = λ (xe , ye) → (X .∂₀ xe) , (Y .∂₀ ye)
                    ; ∂₁ = λ (xe , ye) → (X .∂₁ xe) , (Y .∂₁ ye)
                    ; Id = λ (xe , ye) → (X .Id xe) , (Y .Id ye)
                    ; prop1 = λ {(xv , yv)} → cong₂ _,_ (X .prop1 {xv}) (Y .prop1 {yv})
                    ; prop2 = λ {(xv , yv)} → cong₂ _,_ (X .prop2 {xv}) (Y .prop2 {yv})}


        Rel : {ℓ : Level}→ (A B : Set ℓ) → Set (ℓ-suc ℓ) 
        Rel {ℓ} a b = a → b → Set ℓ

        set : ob RG 
        set = record{ 
                V = Set ℓ; 
                E = Σ ((Set _) × (Set _)) λ (A , B) → Rel A B ;
                ∂₀ = λ f → f .fst .fst; 
                ∂₁ = λ f → f .fst .snd; 
                Id = λ x → (x , x) , _≡_ ; 
                prop1 = refl; 
                prop2 = refl}

        hmm→ : relator (RG× set set) set 
        hmm→ = record { 
                Fv = λ (A , B) → A → B ; 
                Fe = λ (((A , A'), raa') , ((B , B'), rbb')) → 
                    -- related inputs to related outputs
                    ((A → B) , (A' → B')) , λ f f' → ∀(a : A)(a' : A') → raa' a a' → rbb' (f a) (f' a') ; 
                F₀ = refl ; 
                F₁ = refl ; 
                    -- goal : ((a a' : A) → a ≡ a' → f a ≡ f' a') ≡ (f ≡ f')
                Fi = λ { {(A , B)} → ΣPathP (refl , funExt λ f → funExt λ f' → {!   !})} }

        record paramTransSet (F G : relator set set) : Set _ where 
            field 
                η : (A : set .V) → F .Fv A → G .Fv A
                cond : (A A' : set .V) → (ηA : η A) → ?
                

        what×  : relator (RG× set set) set 
        what×  = record { 
            Fv = λ (x , y) → x × y ; 
            Fe = λ (((A , A') , raa') , ((B , B'), rbb')) → 
                -- pairwise related
                ((A × B) , (A' × B')) , λ (a , b) (a' , b') → raa' a a' × rbb' b b' ; 
            F₀ = refl ; 
            F₁ = refl ; 
                -- goal : (fst X ≡ fst Y) × (snd X ≡ snd Y) ≡ (X ≡ Y)
            Fi = λ { {A , B} → ΣPathP (refl , funExt λ X → funExt λ Y → {!   !})  }}


        algF : (G : ob RG)→ (F : relator G set) → ob RG 
        algF G F = record{ 
                    V = Σ (G .V) λ A → F .Fv A;
                    E = {!   !}; 
                    ∂₀ = {!   !}; 
                    ∂₁ = {!   !}; 
                    Id = {!   !}; 
                    prop1 = {!   !}; 
                    prop2 = {!   !}}