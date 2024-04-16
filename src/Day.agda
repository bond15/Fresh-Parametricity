{-# OPTIONS --cubical --type-in-type --allow-unsolved-metas #-}
module Day where 

    postulate synTy : Set

    open import world synTy
    open import LearnPresheaf
    open import CatLib
    open Psh WCat
    open Category
    open ProductCat
    open SetCat hiding (Sets)
    -- no
    open import Data.Product

    Psh-𝒲 : Category _ _ 
    Psh-𝒲 = Psh-𝒞

    open BiFunctor (Product WCat WCat) ℓSets ((Product WCat WCat)^op)  -- 2nd 3rd 1st
    open BiFunctorT 

    open Monoidal WCat 
    open MonoidalT MonWCat

    module DayC (X Y : Ob Psh-𝒲) where 
        Day-diagram : Ob WCat → BiFunctorT 
        Day-diagram x .F₀ (w1⁻ , w2⁻ ) (w1⁺ , w2⁺) = (_⇒_ WCat x (w1⁺ ⊗₀ w2⁺)) × X₀ w1⁻ × Y₀ w2⁻
            where 
                open Functor (WCat ^op) ℓSets
                open FunctorT X renaming (F₀ to X₀ ; F₁ to X₁ ; Fid to Xid ; Fcomp to Xcomp)
                open FunctorT Y renaming (F₀ to Y₀ ; F₁ to Y₁ ; Fid to Yid ; Fcomp to Ycomp)
        Day-diagram x .F₁ (f1 , f2) g o = {!  X₁ f1 !} , ({! X₁   !} , {!   !})
            where 
                open Functor (WCat ^op) ℓSets
                open FunctorT X renaming (F₀ to X₀ ; F₁ to X₁ ; Fid to Xid ; Fcomp to Xcomp)
                open FunctorT Y renaming (F₀ to Y₀ ; F₁ to Y₁ ; Fid to Yid ; Fcomp to Ycomp)
        Day-diagram x .Fid = {!   !}
        Day-diagram x .Fcomp = {!   !}
