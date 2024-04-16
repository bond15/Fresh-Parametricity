{-# OPTIONS --cubical #-}
module circular where

    postulate
        sorryTm : {A : Set₀} → A
        sorryTy : Set₀
    --variable 
    data CaseSym : Set₀ where 
        σ_bool : CaseSym

    data Type^Syn : Set₀ where 
        tyvar bool osum : Type^Syn
        case_ : Type^Syn → Type^Syn
        _×_ _*_ _⇒_ _-*_ : Type^Syn → Type^Syn → Type^Syn

    open import Cubical.Data.Nat
    open import Cubical.Data.Sigma
    open import Cubical.Data.Fin
    open import Cubical.Data.Unit renaming (Unit to ⊤)


   -- Dom : ℕ → Set₀ 
    --Dom n = Fin n → CaseSym

    world : ℕ → Set₀ 
    world n = Fin n → Type^Syn

    data ⊥ : Set₀ where 

    _≤_ : ℕ → ℕ → Set₀ 
    zero ≤ m = ⊤
    suc n ≤ zero = ⊥
    suc n ≤ suc m = n ≤ m

    record _≤w_ {n m : ℕ}(ρ₁ : world n)(ρ₂ : world m) : Set₀ where 
        field 
            sz : n ≤ m
            agree : ∀(x : Fin n) → sorryTy -- they agree on the "first" n enetries
   
    