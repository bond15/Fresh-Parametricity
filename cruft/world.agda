{-# OPTIONS --cubical --allow-unsolved-metas #-}
module world {ℓ}(SynTy : Set ℓ) where 
    open import Cubical.Data.FinSet
    open import Cubical.Data.FinSet.Constructors
    open import Cubical.Data.Empty
    open import Cubical.HITs.PropositionalTruncation
    open import Agda.Primitive
    open import Cubical.Core.Everything
    open import Cubical.Foundations.Prelude
    open import CatLib
    open import Cubical.Data.Sum renaming (map to ⊎map ; elim to ⊎elim)

    record world : Set (lsuc ℓ) where 
        constructor _◃_ 
        field 
            X : FinSet ℓ
            wmap : fst X → SynTy

    _⊎w_ : world → world → world 
    (X ◃ f) ⊎w (Y ◃ g) = ((fst X ⊎ fst Y) , isFinSet⊎ X Y )◃ λ{(inl x) → f x
                                                             ; (inr y) → g y }

    record wmap (w1 w2 : world ): Set ℓ where
        constructor _◂_ 
        open world w1 renaming (wmap to wmap₁)
        open world w2 renaming (X to Y; wmap to wmap₂)
        field 
            mp : fst Y → fst X 
            agree : ∀ (y : fst Y) → wmap₁ (mp y) ≡ wmap₂ y

    open wmap

    inj₁ : {w1 w2 : world} → wmap (w1 ⊎w w2) w1
    inj₁ = inl ◂ λ _ → refl

    inj₂ : {w1 w2 : world} → wmap (w1 ⊎w w2) w2
    inj₂ = inr ◂ λ _ → refl

    ∅ : world 
    ∅  = (⊥* , 0 , ∣_∣₁ ((λ()) , record { equiv-proof = λ() })) ◃ λ()

    emp : {w : world} → wmap w ∅ 
    emp = (λ()) ◂ λ()

    hmm : {w : world} → wmap (∅ ⊎w w) w 
    hmm = inr ◂ λ _ → refl

    hmm' : {w : world} → wmap w (∅ ⊎w w) 
    hmm' = (λ{ (inr x) → x }) ◂ λ{ (inr x) → refl }

    ≡w : {w1 w2 : world}{f g : wmap w1 w2} → (mp f ≡ mp g) → f ≡ g
    ≡w {w1} {w2} {f} {g} hyp i = (hyp i) ◂ λ y → {!   !}

    
    _∘w_ : {w1 w2 w3 : world} → (wmap w2 w3) → wmap w1 w2 → wmap w1 w3 
    _∘w_ {w1} {w2} {w3} (mp ◂ agree) (mp₁ ◂ agree₁) = h ◂ hprf
        where 
            open world w1 renaming (wmap to wmap₁)
            open world w2 renaming (X to Y; wmap to wmap₂)
            open world w3 renaming (X to Z; wmap to wmap₃)

            h : fst Z → fst X 
            h = λ z → mp₁ (mp z)

            hprf : (z : fst Z) → wmap₁ (h z) ≡ wmap₃ z
            hprf z = agree₁ (mp z) ∙ agree z

    idw : {w1 : world} → wmap w1 w1 
    idw  = (λ x → x) ◂ (λ _ → refl)

    open Category

    WCat : Category (ℓ-suc ℓ) ℓ 
    WCat .Ob = world
    WCat ._⇒_ = wmap
    WCat .id = idw
    WCat ._∘_ = _∘w_
    WCat .idr  = ≡w refl
    WCat .idl = ≡w refl
    WCat .assoc = ≡w refl


    open Monoidal WCat 
    open MonoidalT 
    open BiFunctor WCat WCat WCat
    open BiFunctorT

    ten : BiFunctorT 
    ten .F₀ = _⊎w_
    ten .F₁ f g = ⊎map (mp f) (mp g) ◂ ⊎elim (agree f) (agree g) 
    ten .Fid {X ◃ wmap₁} {X₁ ◃ wmap₂} = ≡w (funExt prf)
        where 
            prf : (x : fst X ⊎ fst X₁) → ⊎map (λ x₁ → x₁) (λ x₁ → x₁) x ≡ x
            prf (inl x) = refl
            prf (inr x) = refl
    ten .Fcomp {X ◃ xmap} {Y ◃ ymap} {Z ◃ zmap} {f} {g} {X' ◃ xmap'} {Y' ◃ ymap'} {Z' ◃ zmap'} {f'} {g'} = ≡w (funExt {! f  !})
        where 
            prf : {!   !}
            prf (inl x) = refl 
            prf (inr x) = refl 
        

    -- whats a cleaner way to do this?
    MonWCat : MonoidalT 
    MonWCat = record
                { ⊗ = ten
                ; unit = ∅
                ; unitorˡ = record { 
                                from = inr ◂ λ _ → refl ; 
                                to = (λ{(inr x) → x}) ◂ λ{(inr x) → refl } ; 
                                isoˡ = ≡w (funExt λ{(inr x) → refl }) ; 
                                isoʳ = ≡w (funExt λ x → refl) }
                ; unitorʳ = record { 
                                from = inl ◂ (λ _ → refl) ; 
                                to = (λ{(inl x) → x }) ◂ λ{ (inl x) → refl } ; 
                                isoˡ = ≡w (funExt λ{(inl x) → refl }) ; 
                                isoʳ = ≡w(funExt λ{x → refl }) }
                ; associator = record { 
                                from = (⊎elim (λ x → inl (inl x)) (⊎elim (λ x → inl (inr x)) inr)) ◂ λ{ (inl x) → refl
                                                                                                      ; (inr (inl x)) → refl
                                                                                                      ; (inr (inr x)) → refl} ; 
                                to = (⊎elim (⊎elim inl λ x → inr(inl x)) λ x → inr (inr x)) ◂ λ{(inl (inl x)) → refl
                                                                                              ; (inl (inr x)) → refl
                                                                                              ; (inr x) → refl} ; 
                                isoˡ = ≡w (funExt λ{(inl (inl x)) → refl
                                                  ; (inl (inr x)) → refl
                                                  ; (inr x) → refl }) ; 
                                isoʳ = ≡w (funExt λ{(inl x) → refl
                                                  ; (inr (inl x)) → refl
                                                  ; (inr (inr x)) → refl}) }
                ; pentagon = ≡w (funExt λ{(inl x) → refl 
                                        ; (inr (inl x)) → refl 
                                        ; (inr (inr (inl x))) → refl 
                                        ; (inr (inr (inr x))) → refl}) }