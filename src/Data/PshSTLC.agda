{-# OPTIONS --type-in-type --allow-unsolved-metas #-}
module src.Data.PshSTLC where     
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

    open import src.Data.SemSTLC
    
    module experiment (𝓒 : Category _ _ )where 
        open import Cubical.Categories.Presheaf.Base
        open import Cubical.Categories.Presheaf.Constructions
        open import Cubical.Categories.Displayed.Constructions.Comma
        open import Cubical.Categories.NaturalTransformation renaming (_⇒_ to _⇒nat_ )
        open import Cubical.Categories.Functor.Properties
        open import Cubical.Categories.Functors.Constant
        open import src.Data.PresheafCCC
        open import Cubical.Categories.Limits.Terminal
        open import Cubical.Categories.Limits.BinProduct
        open BinProduct

        -- covarient presheaves category

        Psh : Category _ _ 
        Psh = PresheafCategory 𝓒 _

        termPsh : Terminal Psh
        termPsh = ⊤𝓟 {C = 𝓒} {_}

        bp : BinProducts Psh
        bp = ×𝓟 {C = 𝓒 } {_}
        
        𝟙 : ob Psh
        𝟙 = termPsh .fst

        _⇛_ : ob Psh → ob Psh → ob Psh
        _⇛_ = ExpOb

        _×𝓒_ : ob Psh → ob Psh → ob Psh
        _×𝓒_ X Y = bp X Y .binProdOb

        π₁𝓒 : {X Y : ob Psh} → Psh [ X ×𝓒 Y , X ]
        π₁𝓒  {X} {Y} = bp X Y .binProdPr₁

        π₂𝓒 : {X Y : ob Psh} → Psh [ X ×𝓒 Y , Y ]
        π₂𝓒  {X} {Y} = bp X Y .binProdPr₂

        Δ : (X : ob Psh) → Psh [ X , bp X X .binProdOb ]
        Δ X = bp X X .univProp (Psh .id{X}) (Psh .id{X}) .fst .fst

        bimap : {X Y Z W : ob Psh} → Psh [ X , Z ] → Psh [ Y , W ] → Psh [ bp X Y .binProdOb , bp Z W .binProdOb ]
        bimap {X}{Y}{Z}{W} f g = bp Z W .univProp (π₁𝓒 {X} {Y} ⋆⟨ Psh ⟩ f) (π₂𝓒 {X} {Y} ⋆⟨ Psh ⟩ g) .fst .fst

        binop : {H : ob Psh} → Psh [ H ×𝓒 H , H ] → (x y : Psh [ 𝟙 , H ]) → Psh [ 𝟙 , H ]
        binop op x y =  Δ 𝟙 ⋆⟨ Psh ⟩ bimap x y ⋆⟨ Psh ⟩ op


        open toSet renaming (⟪_⟫ty to ⟪_⟫ty-set ; ⟪_⟫ctx to ⟪_⟫ctx-set ; ⟪_⟫tm to ⟪_⟫tm-set)

        ⟪_⟫ty : U → ob Psh 
        ⟪ unit ⟫ty = Constant _ _ ⟪ unit ⟫ty-set
        ⟪ bool ⟫ty = Constant _ _ ⟪ bool ⟫ty-set
        ⟪ prod t1 t2 ⟫ty = ⟪ t1 ⟫ty ×𝓒 ⟪ t2 ⟫ty
        ⟪ arr t1 t2 ⟫ty = ⟪ t1 ⟫ty ⇛ ⟪ t2 ⟫ty


        ⟪_⟫ctx : Ctx → ob Psh
        ⟪_⟫ctx c = ⟪ ctxToU c ⟫ty

        open import Cubical.Categories.Functor
        open Functor
        ⟪_⟫tm : {Γ : Ctx}{A : U} → Γ ⊢ A → Psh [ ⟪ Γ ⟫ctx , ⟪ A ⟫ty ]
        ⟪_⟫tm {Γ} {.unit} (u x) = natTrans (λ c Γc → x) λ f → refl
        ⟪_⟫tm {Γ} {.bool} (b x) = natTrans (λ c Γc → x) λ f → refl
        ⟪_⟫tm {Γ} {.(prod _ _)} (pair M1 M2) = Δ ⟪ Γ ⟫ctx ⋆⟨ Psh ⟩ bimap ⟪ M1 ⟫tm ⟪ M2 ⟫tm
        ⟪_⟫tm {Γ} {(arr A1 A2)} (fun x) = natTrans (λ c Γx → natTrans (λ{c' ((lift f) , A1c) → {! x A1c  !}}) {!   !}) {!   !}
        ⟪_⟫tm {Γ} {.(snd Γ i)} (var i) = {!   !}
 
        


        