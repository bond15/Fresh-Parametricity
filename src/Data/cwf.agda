{-#OPTIONS --type-in-type #-}
module src.Data.cwf where
    open import Cubical.Categories.Category
    open import Cubical.Categories.Functor
    open import Cubical.Categories.Functors.Constant
    open import Cubical.Categories.Instances.Sets 
    open import Cubical.Categories.Displayed.Base
    open import Cubical.Categories.Displayed.Instances.Sets.Base
    open Categoryᴰ
    open import Cubical.Categories.Displayed.Constructions.TotalCategory
    open import Cubical.Categories.Constructions.TotalCategory
    open import Agda.Primitive
    open import Cubical.Data.Sigma
    open import Cubical.Categories.Limits.Terminal
    
    module _{ℓS} where
        --ℓS = ℓ-zero
        
        Fam : Category (lsuc ℓS ) ℓS
        Fam = ∫C (SETᴰ ℓS ℓS )

        open import Cubical.Data.Unit
        open import Cubical.Data.Bool

        open Category
        open Functor
        _ : ob Fam 
        _ = (Unit* , isSetUnit*) , λ{tt* → Bool* , {!   !}} 

        record CwF' : Set (ℓ-suc (ℓ-suc  ℓS)) where 
            field 
                C : Category (ℓ-suc ℓS) ℓS 
                T : Functor (C ^op) Fam 
                One : Terminal C

        open CwF'
        module _ (cwf : CwF')(Γ : ob (cwf .C)) where 


            Typ_ : ob (cwf .C) → Set _ 
            Typ Γ = cwf . T .F-ob Γ .fst .fst

            Trm_,_ : (Γ : ob (cwf .C)) → (c : Typ Γ) → Set _ 
            Trm_,_ Γ c = cwf .T .F-ob Γ .snd c .fst
            
            TySub : {Γ Δ : ob (cwf .C)} → (A : Typ Δ) → (δ : (cwf .C)[ Γ , Δ ] ) → Typ Γ
            TySub {Γ} {Δ} A δ = cwf .T .F-hom δ .fst A

            TrmSub : {Γ Δ : ob (cwf .C)}{A : Typ Δ} → (x : Trm Δ , A) → (δ : (cwf .C)[ Γ , Δ ] ) → Trm Γ , (TySub A δ)
            TrmSub {Γ} {Δ}{A} x δ = cwf .T .F-hom δ .snd A x

            record comprehension : Set (ℓ-suc ℓS) where 
                field 
                    A : Typ Γ
                    Γ+A : ob (cwf .C)
                    p : (cwf .C)[ Γ+A , Γ ]
                    q : Trm Γ+A , TySub A p

        open comprehension
        
        UP' : (cwf : CwF') → (Γ : ob (cwf .C)) → (comprehension cwf Γ) → Set
        UP' cwf Γ Γcomp = ∀ (Δ : ob (cwf .C))(γ : (cwf .C)[ Δ , Γ ])(a : Trm' Δ , TySub' A' γ) 
            → ∃! ((cwf .C)[ Δ , Γ+A' ]) λ θ → Σ[ prf ∈ (θ ⋆⟨ cwf .C ⟩ p' ≡ γ) ] PathP (λ i → {!   !}) (TrmSub' q' θ) a where
            -- (θ ⋆⟨ cwf .C ⟩ p' ≡ γ) × (TrmSub' q' θ ≡ {! a !}) where 
            p' = Γcomp .p
            q' = Γcomp .q
            A' = Γcomp .A
            Γ+A' = Γcomp .Γ+A
            Trm'_,_ = Trm_,_ cwf Γ
            TySub' = TySub cwf Γ 
            TrmSub' = TrmSub cwf Γ


        record CwF : Set where 
            field 
                cwf : CwF' 
                ctxcomp : ∀ (Γ : ob (cwf .C)) → comprehension cwf Γ
                UP : ∀ (Γ : ob (cwf .C)) → UP' cwf Γ (ctxcomp Γ)

        open import Cubical.Foundations.Prelude
        open import Cubical.Categories.Instances.Terminal
        open CwF
        ex : CwF
        ex .cwf .C = SET ℓS
        ex .cwf .T .F-ob (Γ , ΓisSet) = ((Γ → Set _) , {!   !}) , λ F → (∀ (x : Γ )→ F x) , {!   !}
        ex .cwf .T .F-hom f .fst g = λ z → g (f z)
        ex .cwf .T .F-hom f .snd x = λ z x → z (f x)
        ex .cwf .T .F-id = refl
        ex .cwf .T .F-seq f g = refl
        ex .cwf .One = {!   !}
        ex .ctxcomp Γ = record { A = λ x → Set ; Γ+A = (Σ[ γ ∈ Γ .fst ] {!   !}) , {!   !} ; p = {!   !} ; q = {!   !} }
        ex .UP = {!   !}
        
       -- foo : (Γ : ob (ex .C)) → comprehension ex Γ 
       -- foo Γ = record { A = λ x → Γ .fst ; Γ+A = (Σ (Γ .fst) λ γ → {!   !}) , {!   !} ; p = {!   !} ; q = {!   !} }
 

