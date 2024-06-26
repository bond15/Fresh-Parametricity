{-# OPTIONS --type-in-type #-}
module src.SimpleState where 
    open import src.Data.FinSet
    open import Cubical.Foundations.HLevels hiding (extend)
    open import Cubical.Foundations.Prelude   
    open import Cubical.Categories.Category
    open import Cubical.Categories.Functor
    open import Cubical.Categories.Instances.Functors
    open import Cubical.Categories.Instances.Sets
    open import Cubical.Data.FinSet.Base
    open import Cubical.Categories.NaturalTransformation
    open import Cubical.Categories.Functors.Constant



    module _ {ℓS} where 
        module Levy where 
            Inj = FinSetMono {ℓS}

            𝒱 : Category (ℓ-suc ℓS) (ℓ-suc ℓS) 
            𝒱 = FUNCTOR Inj (SET ℓS)
            
            open Category
            open Functor
            open NatTrans

            𝒞 : Category (ℓ-suc ℓS) (ℓ-suc ℓS) 
            𝒞 = FUNCTOR (Inj ^op) (SET ℓS)

            open import Cubical.Categories.Instances.Discrete

            postulate Injset : isSet (ob Inj)
            |Inj| : Category (ℓ-suc ℓS) (ℓ-suc ℓS) 
            |Inj| = DiscreteCategory ((ob Inj) , (isSet→isGroupoid Injset))
            open import Cubical.Data.Bool
            open import Cubical.Data.Sigma

            S : Functor |Inj| (SET ℓS)
            S = DiscFunc λ {(X , Xfin) → ((SET ℓS) [ (X , isFinSet→isSet Xfin) , (Lift Bool , {!   !}) ]) , (SET ℓS) .isSetHom}

            F : Functor 𝒱 𝒞
            F .F-ob A .F-ob X = Σ (ob Inj) (λ Y → Σ (Inj [ X , Y ]) λ f → fst (S .F-ob  Y) × fst (A .F-ob Y)) , {!   !}
            F .F-ob A .F-hom {X} {Y} f (Z , X→Z , SZ , AZ) = Z , (f ⋆⟨ Inj ⟩ X→Z , (SZ , AZ))
            F .F-ob A .F-id = {!   !}
            F .F-ob A .F-seq = {!   !}
            F .F-hom nt = natTrans (λ {X (Y , f , SY , AY) → Y , (f , (SY , nt .N-ob Y AY))}) {!   !}
            F .F-id = {!   !}
            F .F-seq = {!   !}

            U : Functor 𝒞 𝒱 
            U .F-ob B .F-ob X = ((Y : ob Inj) → (f : Inj [ X , Y ]) → S .F-ob Y .fst  → B .F-ob Y .fst) , {!   !}
            U .F-ob B .F-hom {X} {Y} f m Z g SZ = m Z (f ⋆⟨ Inj ⟩ g) SZ
            U .F-ob B .F-id = {!   !}
            U .F-ob B .F-seq f g = {!   !}
            U .F-hom nt = natTrans (λ X m Y f SY → nt .N-ob Y (m Y f SY)) {!   !}
            U .F-id = {!   !}
            U .F-seq = {!   !}

            T : Functor 𝒱 𝒱 
            T = U ∘F F

            Ref : ob 𝒱 
            Ref .F-ob X = (fst X) , (isFinSet→isSet (snd X))
            Ref .F-hom (f , _) X = f X 
            Ref .F-id = refl
            Ref .F-seq f g = refl

            BoolF : ob 𝒱 
            BoolF = Constant _ _ (Bool* , isOfHLevelLift 2 isSetBool)
            open import Cubical.Data.Unit 

            UnitF : ob 𝒱 
            UnitF = Constant _ _ (Unit* , isOfHLevelLift 2 isSetUnit)
            open import Cubical.Foundations.Isomorphism
            open Iso

            open import Cubical.Data.Bool
            open import Cubical.Data.FinSet.Properties
            open import Cubical.Data.Sum
            open import Cubical.Data.FinSet.Constructors
            open import Cubical.Data.Sigma    
            open import Cubical.Functions.Embedding


            Unit*Fin : FinSet ℓS
            Unit*Fin = Unit* , EquivPresIsFinSet 
                                (isoToEquiv (iso 
                                                (λ{tt  → tt*}) 
                                                (λ{tt* → tt}) 
                                                (λ{ tt*  → refl}) 
                                                (λ{ tt → refl }))) isFinSetUnit

            inc : FinSet ℓS → FinSet ℓS
            inc X = ((X .fst ⊎ Unit*) , isFinSet⊎ X Unit*Fin)
            
            inlemb : {ℓ : Level}{A B : Type ℓ} → isEmbedding (inl {ℓ}{ℓ}{A}{B})
            inlemb = λ w x → record { equiv-proof = λ y → ({!   !} , {!   !}) , (λ y₁ → {!   !}) }
            
            alloc : {Γ : ob 𝒱} → (M : 𝒱 [ Γ , T .F-ob BoolF ]) → 𝒱 [ Γ , T .F-ob Ref ]
            alloc {Γ} (natTrans N-ob N-hom) = natTrans goal {!   !} where 
                goal : N-ob-Type Γ (T .F-ob Ref)
                goal X ΓX Y f SY = inc Y , ((inl , inlemb) , (λ {(inl y) → SY y
                                                               ; (inr tt*) → N-ob X ΓX Y f SY .snd .snd .snd}) , (inr tt*))
            

            get2 : 𝒱 [ Ref , T .F-ob BoolF ]
            get2  = natTrans (λ X x Y f SY → Y , ((Inj .id) , (SY , (SY (fst f x))))) {!   !}

            get' : {Γ : ob 𝒱} → 𝒱 [ Γ , Ref ] → 𝒱 [ Γ , T .F-ob BoolF ]
            get' {Γ} (natTrans N-ob N-hom) = natTrans goal {!   !} where 
                goal : N-ob-Type Γ  (T .F-ob BoolF)
                goal X ΓX Y f SY = Y , (Inj .id , SY , (SY (f .fst (N-ob X ΓX))))

            open import Cubical.Data.FinSet.DecidablePredicate
            update : {X : ob Inj} → Ref .F-ob X .fst → Lift Bool → (fst X → Lift Bool)→ (fst X → Lift Bool)
            update {X} r b f x = if isDecProp≡ X r x .fst then b else f x


            set : {Γ : ob 𝒱} → 𝒱 [ Γ , Ref ] → 𝒱 [ Γ , BoolF ] →  𝒱 [ Γ , T .F-ob UnitF ]
            set {Γ} (natTrans N-ob₁ N-hom₁) (natTrans N-ob₂ N-hom₂) = natTrans (λ X ΓX Y f SY → Y , ((Inj .id) , ((update {Y} (f .fst (N-ob₁ X ΓX)) (N-ob₂ X ΓX) SY) , tt*))) {!   !}

            get : {Γ : ob 𝒱} → 𝒱 [ Γ , T .F-ob Ref ] → 𝒱 [ Γ , T .F-ob BoolF ]
            get {Γ} (natTrans N-ob N-hom) = natTrans goal {!   !} where 
                goal : N-ob-Type Γ (T .F-ob BoolF)
                goal X ΓX Y f SY = Y , ((Inj .id) , (SY , SY {! N-ob X ΓX Y f SY !})) where 
                    p : (F ⟅ Ref ⟆) .F-ob Y .fst
                    p =  N-ob X ΓX Y f SY 
    
                    q : (F ⟅ Ref ⟆) .F-ob Y .fst
                    q = N-ob Y (Γ .F-hom f ΓX) Y (Inj .id) SY 

                    Z : ob Inj 
                    Z = p .fst

                    g : Inj [ Y , Z ]
                    g =  p .snd .fst

                    SZ : S .F-ob Z .fst
                    SZ = p .snd .snd .fst 

                    RefZ : fst Z --Ref .F-ob Z  .fst
                    RefZ = p .snd .snd .snd

            open import Cubical.Categories.Constructions.BinProduct 
            open import Cubical.Categories.Monoidal.Base
            open import Cubical.HITs.PropositionalTruncation hiding(rec ; map)
            _⨂_ : Functor (Inj ×C Inj) Inj
            _⨂_ .F-ob (X , Y) = ((fst X ⊎ fst Y)) , (isFinSet⊎ X Y)
            _⨂_ .F-hom{X , Y}{W , Z} (f , g) = (map (fst f) (fst g)) , {!   !}
            _⨂_ .F-id = {!  refl !}
            _⨂_ .F-seq = {!   !}

            open import Cubical.Data.Empty
            emptyFin* : isFinSet {ℓS} (Lift ⊥)
            emptyFin* = 0 , ∣ (λ()) , record { equiv-proof = λ() } ∣₁

            emptymap : ob Inj 
            emptymap = (Lift ⊥) , emptyFin*

            mon : StrictMonStr Inj
            mon = record { tenstr = 
                record { ─⊗─ = _⨂_ ; 
                        unit = emptymap } ; 
                    assoc = {!   !} ; 
                    idl =  {!   !} ; 
                    idr = {!   !} }

            strmon : StrictMonCategory (ℓ-suc ℓS) ℓS 
            strmon = record { C = Inj ; sms = mon }
            
            open import src.Data.Semicartesian
            open import src.Data.DayConv
            
            _⨂ᴰᵥ_ : ob 𝒱 → ob 𝒱 → ob 𝒱
            A ⨂ᴰᵥ B =  _⊗ᴰ_ {MC = strmon ^opMon } A B 

            open import Cubical.HITs.SetCoequalizer renaming (inc to incs)

            test : (A B : ob 𝒱)(X : ob Inj) → (A ⨂ᴰᵥ B) .F-ob X .fst
            test A B X = incs ((Y , Z) , ((f , {!   !}) , {!   !})) where 
                Y : ob Inj 
                Y = {!   !}

                Z : ob Inj 
                Z = {!   !}

                f : Inj [ _⨂_ .F-ob (Y , Z) , X ]
                f = {!   !}
                
            _⊸_ : ob 𝒱 → ob 𝒱 → ob 𝒱
            -- todo make a Set^Inj
            _⊸_ A B .F-ob X = (∀ (Y : ob Inj) → (SET ℓS) [ A .F-ob Y , B .F-ob (_⨂_ .F-ob (X , Y)) ]) , isSetΠ  λ _ → (SET ℓS) .isSetHom
            _⊸_ A B .F-hom {X} {Y} f FX Z AZ = B .F-hom (_⨂_ .F-hom (f , (Inj .id))) (FX Z AZ)
            _⊸_ A B .F-id = {!   !}
            _⊸_ A B .F-seq = {!   !}

            test2 : (X : ob Inj) → (Ref ⊸ BoolF) .F-ob X .fst
            test2 X = λ Y y → lift true

            -- if reference y is supposed to be fresh.. why can i use it?!
            test3 : (X : ob Inj) → (Ref ⊸ T .F-ob BoolF) .F-ob X .fst
            test3 X = λ Y y → λ Z X+Y→Z Sz → Z , ((Inj .id) , (Sz , (Sz ((inr ⋆⟨ SET ℓS ⟩ (fst X+Y→Z)) y))))

            test4 : (X : ob Inj) → (Ref ⊸ T .F-ob BoolF) .F-ob X .fst
            test4 X = λ Y y → {!  (get2 .N-ob Y y) !}
            --{!  (get2 .N-ob Y y)  !}

            
            {- 

            -- separating function type
        sep : ob 𝒱 → ob 𝒞 → ob 𝒞 
            -- should be an end ?
        sep A B .F-ob w = (∀ (w' : ob W) → (SET ℓ)[ A .F-ob w' , B .F-ob (_⨂_ .F-ob (w , w')) ]) , isSetΠ  λ _ → (SET ℓ) .isSetHom
        sep A B .F-hom {w₁}{w₂} w₁→w₂ end w₃ Aw₃ = B .F-hom (_⨂_ .F-hom (w₁→w₂ , W .id)) (end w₃ Aw₃)
        sep A B .F-id = funExt λ end → funExt λ w₃  → funExt λ Aw₃ → cong (λ x → (B .F-hom x) (end w₃ Aw₃) ) (_⨂_ .F-id) ∙ funExt⁻ (B .F-id) ((end w₃ Aw₃))
        sep A B .F-seq f g = funExt λ end → funExt λ w₃  → funExt λ Aw₃ → {! funExt⁻ (B .F-seq _ _) _ ∙ ?  !}
        -- cong (λ x → (B .F-hom x) (end w₃ Aw₃) ) {! _⨂_ .F-seq _ _  !} ∙ funExt⁻ (B .F-seq _ _ ) ((end w₃ Aw₃))
            -}
            
        module PlotkinPower where 
            Inj = FinSetMono {ℓS}

            𝒞 : Category (ℓ-suc ℓS) (ℓ-suc ℓS) 
            𝒞 = FUNCTOR Inj (SET ℓS)

            open Category
            open Functor
            open import Cubical.Foundations.Isomorphism
            open Iso

            open import Cubical.Data.Bool
            open import Cubical.Data.FinSet.Properties
            open import Cubical.Data.Unit 
            open import Cubical.Data.Sum
            open import Cubical.Data.FinSet.Constructors
            open import Cubical.Data.Sigma

            Unit*Fin : FinSet ℓS
            Unit*Fin = Unit* , EquivPresIsFinSet 
                                (isoToEquiv (iso 
                                                (λ{tt  → tt*}) 
                                                (λ{tt* → tt}) 
                                                (λ{ tt*  → refl}) 
                                                (λ{ tt → refl }))) isFinSetUnit

            inc : FinSet ℓS → FinSet ℓS
            inc X = ((X .fst ⊎ Unit*) , isFinSet⊎ X Unit*Fin)

            S : Functor (Inj ^op) (SET ℓS)
            S .F-ob x = ((SET ℓS) [ ((fst ( x)) , isFinSet→isSet (snd ( x))) , (Lift Bool , {!   !}) ]) , (SET ℓS) .isSetHom
            S .F-hom (f , _) m y = m (f y)
            S .F-id = refl 
            S .F-seq f g = refl

            Ref : ob 𝒞 
            Ref .F-ob X = (fst X) , (isFinSet→isSet (snd X))
            Ref .F-hom (f , _) X = f X 
            Ref .F-id = refl
            Ref .F-seq f g = refl

            T : Functor 𝒞 𝒞 
            T .F-ob A .F-ob X = ((SET ℓS)[ S .F-ob X , (Σ (ob Inj) (λ Y → fst (S .F-ob Y) × fst (A .F-ob Y) × (Inj [ X , Y ])) , {!   !}) ]) , ((SET ℓS) .isSetHom)
            T .F-ob A .F-hom {X} {Y} f Fx s = Y , (s , ({!   !} , (Inj .id))) where -- have A(Z) but need A(Y)
                --Z , (Sz , (Az , {!   !})) where -- have X → Y and X → Z but need Y → Z
                s×a = Fx (S .F-hom f s)
                Z : ob Inj 
                Z = fst s×a

                Sz : fst(S .F-ob Z)
                Sz = s×a .snd .fst

                Az : fst (A .F-ob Z)
                Az = s×a .snd .snd .fst

                X→Z : Inj [ X , Z ]
                X→Z = s×a .snd .snd .snd


            T .F-ob A .F-id = {!   !}
            T .F-ob A .F-seq = {!   !}
            T .F-hom = {!   !}
            T .F-id = {!   !} 
            T .F-seq = {!   !}