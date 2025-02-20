{-# OPTIONS --type-in-type #-}
module src.Data.LogicalRelation where 

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
    open import Cubical.Categories.Displayed.Base
    open import Cubical.Data.Nat
    open import Cubical.Data.Fin.Recursive.Base
    open import Cubical.Categories.Instances.Posets.Base
    open import Cubical.Categories.Instances.Preorders.Monotone
    open import Cubical.Categories.Displayed.Constructions.StructureOver
    open Categoryᴰ
    open StructureOver
    open import Cubical.Relation.Binary.Preorder
    open PreorderStr 
    open MonFun renaming (f to mon)

    open import src.Data.STLC
    open import src.Data.SemSTLC
    open import src.Data.HyperDoctrine
    open import src.Data.SetHyperDoc

    open toSet hiding (set)

    
    𝓟⟨_⟩ : set .ob → Set 
    𝓟⟨ X ⟩ = 𝓟 .F-ob X .fst .fst

    𝓟₁⟨_⟩⟨_⟩ : {X Y : ob set} → set [ X , Y ] → 𝓟⟨ Y ⟩ → 𝓟⟨ X ⟩ 
    𝓟₁⟨ f ⟩⟨ py ⟩ = MonFun.f (𝓟 .F-hom f ) py

    _≤Px_ : {X : ob set} → 𝓟⟨ X ⟩ → 𝓟⟨ X ⟩ → Set
    _≤Px_ {X} = 𝓟 .F-ob X .fst .snd ._≤_

-- module Cubical.Categories.Instances.Posets.Base where

    open import Cubical.Categories.Displayed.Constructions.Reindex
    S' : StructureOver set _ _ 
    S' .ob[_] = 𝓟⟨_⟩
    S' .Hom[_][_,_] {X}{Y} X→Y 𝓟X 𝓟Y = _≤Px_{X} 𝓟X (𝓟₁⟨ X→Y ⟩⟨ 𝓟Y ⟩)
    S' .idᴰ x z = z
    S' . _⋆ᴰ_  {X}{Y}{Z}{X→Y}{Y→Z}{Px}{Py}{Pz} f* g* = λ x z → g* (X→Y x) (f* x z)
    S' .isPropHomᴰ {X} = 𝓟 .F-ob X .fst .snd .is-prop-valued  _ _

    S : Categoryᴰ set _ _ 
    S = StructureOver→Catᴰ S'

    open import Cubical.Categories.Displayed.Properties 

    Pred' : Categoryᴰ syn _ _ 
    Pred' = reindex S cl

    open import Cubical.Categories.Constructions.TotalCategory

    Pred : Category _ _ 
    Pred = ∫C Pred'

    open import  Cubical.Functions.Logic renaming (inl to inL)
    open import Cubical.Data.Fin.Recursive.Properties
    open import src.Data.STLC
    open examplemap
    open import Cubical.HITs.PropositionalTruncation.Base

    Γ' : ob Pred 
    Γ' = examplemap.Γ , g where 

        g : ob[ Pred' ] examplemap.Γ
        g record { terms = terms } = t1 ≡ₚ pure (true) where 

            t1 : ⊘ ⊢ bool 
            t1 = terms (iS (iS (toFin 0)))

            t2 : ⊘ ⊢ arr unit bool 
            t2 = terms (iS (toFin 1))

            t3 : ⊘ ⊢ unit 
            t3 = terms (toFin 2)

    Δ' : ob Pred 
    Δ' = examplemap.Δ , g where 
        g : ob[ Pred' ] Δ 
        g record { terms = terms } = t1' ≡ₚ pure (true) where 

            t1' : ⊘ ⊢ bool 
            t1' = terms (iS (iS (iS (toFin 0))))

    _ : Pred [ Γ' , Δ' ]
    _ = Γ→Δ , g where 
        g : Hom[ Pred' ][ Γ→Δ , snd Γ' ] (snd Δ') 
        g record { terms = terms } PΓterm = assm where 
            t1 : ⊘ ⊢ bool 
            t1 = terms (iS (iS (toFin 0)))


            assm  : ∥ t1 ≡ pure true ∥₁
            assm  = PΓterm

           -- assm : PΓterm t1 ≡ (t1 ≡ₚ pure bool)
           -- assm = ?


    open HDsyntax set term bp exp setHyperDoc


    _ : ⟪_⟫F {{!   !}} (⋀ {!   !}) {!   !} .fst
    _ = {!   !}
   -- exf : Formula {!   !}
 --   exf = ⋀_ {(Bool , isSetBool)} {!   !}

{-


        

    delta' : ob Pred 
    delta' = delta , λ x → ⊤

    map : CtxMap (fst gamma') (fst delta') 
    map = record { terms = λ {zero → {!   !}
                            ; (suc zero) → {!   !}
                            ; (suc (suc zero)) → {!   !}
                            ; (suc (suc (suc zero))) → {!   !}} }

    _ : Pred [ gamma' , delta' ]
    _ = {!   !} , {!   !} 

    
    -}

