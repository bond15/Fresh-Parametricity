{-# OPTIONS --allow-unsolved-metas #-}
module src.Data.SemSTLC where 
    open import Cubical.Categories.Instances.Sets
    open import Cubical.Categories.Category hiding (isUnivalent)
    open Category
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
            
        ⟪_⟫tm {Γ} {.(snd Γ i)} (var i) γ = g where 
            -- tricky, but doable
            g : fst ⟪ snd Γ i ⟫ty 
            g = {!  !}



        open testing
        test : set [ ⟪ c4 ⟫ctx , (((Bool → (Bool → Bool) × (Unit → Bool))) , _ )] 
        test = ⟪ term1 ⟫tm





    
