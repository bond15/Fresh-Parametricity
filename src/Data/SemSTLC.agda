{-# OPTIONS --allow-unsolved-metas #-}
module src.Data.SemSTLC where 
    open import Cubical.Categories.Instances.Sets
    open import Cubical.Categories.Category hiding (isUnivalent)
    open Category
    open import Cubical.Categories.Functor
    open Functor
    open import Cubical.Foundations.Prelude
    open import Cubical.Foundations.Structure 
    open import Cubical.Data.Unit 
    open import Cubical.Data.Bool hiding (_≤_)
    open import Cubical.Data.Sigma
    open import Cubical.Foundations.HLevels

   -- open import Cubical.Data.List 
   -- open import Cubical.Data.Fin renaming (elim to felim)
    open import Cubical.Data.Nat
    open import Cubical.Data.Fin.Recursive.Base
    open import src.Data.STLC

    module toSet where 
        set : Category _ _ 
        set = SET ℓ-zero

        {-
            possible refinement 
            Category 
                ob := Σ[ u : U ] El u
                mor (u1 , T1) (u2 , T2) := El (arr u1 u2) 
        -}
        set' : Category _ _ 
        set' .ob = Σ[ u ∈ U ] El u
        set' .Hom[_,_] (u1 , T1) (u2 , T2) = El (arr u1 u2) -- T1 → T2 
        set' .id x = x
        set' ._⋆_ f g x = g (f x)
        set' .⋆IdL f = refl
        set' .⋆IdR f = refl
        set' .⋆Assoc f g h = refl
        set' .isSetHom = isSet→ (isSetEl _)

        open import Cubical.Categories.Displayed.Base
        syn : Category _ _  
        syn .ob = Ctx
        syn .Hom[_,_] = CtxMap
        syn .id  = idCtxMap 
        syn ._⋆_  = seqCtxMap
        syn .⋆IdL f = ≡CtxMap (funExt λ x → subId)
        syn .⋆IdR f = ≡CtxMap refl
        syn .⋆Assoc f g h = ≡CtxMap (funExt λ x → subSeq {f = f}{g} (CtxMap.terms h x))
        syn .isSetHom = isSetCtxMap


        cl : Functor syn set 
        -- closed terms
        cl .F-ob Γ = (syn [ ⊘ , Γ ]) , (syn .isSetHom)
        cl .F-hom {Γ}{Δ} Γ→Δ ∅→Γ = seqCtxMap ∅→Γ Γ→Δ
        cl .F-id = funExt λ x → ≡CtxMap refl
        cl .F-seq f g = funExt λ h → sym (syn .⋆Assoc h f g)

        ⟪_⟫ty : U → ob set
        ⟪ unit ⟫ty = (El unit) , isSetEl unit
        ⟪ bool ⟫ty = (El bool) , isSetEl bool
        ⟪ prod t1 t2 ⟫ty = El (prod t1 t2) , isSetEl (prod t1 t2)
        ⟪ arr t1 t2 ⟫ty = (El (arr t1 t2)) , isSetEl (arr t1 t2)

        lemma : (u : U) → ⟪ u ⟫ty .fst ≡ El u
        lemma unit = refl
        lemma bool = refl
        lemma (prod x x₁) = refl
        lemma (arr x x₁) = refl

        ⟪_⟫ctx : Ctx → ob set
        ⟪_⟫ctx c = ⟪ ctxToU c ⟫ty


        ⟪_⟫tm : {Γ : Ctx}{A : U} → Γ ⊢ A → set [ ⟪ Γ ⟫ctx , ⟪ A ⟫ty ]
        ⟪_⟫tm {Γ} {.unit} (u x) = λ _ → x
        ⟪_⟫tm {Γ} {.bool} (b x) = λ _ → x
        ⟪_⟫tm {Γ} {(prod A1 A2)} (pair M1 M2) γ = g1 , g2  where 
            M1' : set [ ⟪ Γ ⟫ctx , ⟪ A1 ⟫ty ]
            M1' = ⟪ M1 ⟫tm
            
            M2' : set [ ⟪ Γ ⟫ctx , ⟪ A2 ⟫ty ]
            M2' = ⟪ M2 ⟫tm

            -- really dumb.. these are all transport over refl
            g1 : El A1 
            g1 = transport (lemma A1) (M1' γ)

            g2 : El A2 
            g2 = transport (lemma A2) (M2' γ)
            
        ⟪_⟫tm {Γ} {(arr A1 A2)} (fun x) γ a1 = g where
            M : set [ ⟪ Γ ⟫ctx , ⟪ A2 ⟫ty ] 
            M = ⟪ x a1 ⟫tm

            g : El A2 
            g = transport (lemma A2) (M γ)

        ⟪_⟫tm {Γ} {A} (app f x) γ = g where 
            fx : El A
            fx = {! ⟪ f ⟫tm γ (⟪ x ⟫tm γ) !}
            g : fst ⟪ A ⟫ty 
            g = {! f  !}
            
        ⟪_⟫tm {Γ} {.(snd Γ i)} (var i) γ = g where 
            -- tricky, but doable
            g : fst ⟪ snd Γ i ⟫ty 
            g = {!  !}



        open testing
        test : set [ ⟪ c4 ⟫ctx , (((Bool → (Bool → Bool) × (Unit → Bool))) , _ )] 
        test = ⟪ term1 ⟫tm





    
