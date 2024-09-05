{-# OPTIONS  --lossy-unification --allow-unsolved-metas #-}
-- Following 1Lab
-- https://1lab.dev/Cat.Monoidal.Instances.Day.html
module src.Data.DayConv where 
    open import Cubical.Foundations.Prelude
    open import Cubical.Foundations.HLevels
    open import Cubical.Data.Sigma

    open import Cubical.Categories.Presheaf
    open import Cubical.Categories.Category
    open import Cubical.Categories.Functor
    open import Cubical.Categories.Bifunctor.Redundant
    open import Cubical.Categories.Monoidal.Base 
    open import Cubical.Categories.Instances.Sets

    private
        variable
            ℓC ℓC' ℓS  : Level

    -- for SET
    -- strict or regular? StrictMonCategory
    module _ {MC : StrictMonCategory ℓC ℓC'}(F G : Presheaf (MC .StrictMonCategory.C) (ℓ-max ℓC ℓC')) where
        open StrictMonCategory MC 
        open Category C renaming (ob to obᶜ ; _⋆_ to _⋆ᶜ_ ; id to idᶜ ; ⋆IdL to ⋆IdLᶜ ; ⋆Assoc to ⋆Assocᶜ ; ⋆IdR to ⋆IdRᶜ ;  isSetHom to isSetHomC )
        
        open Category (SET (ℓ-max ℓC ℓC')) renaming (ob to obˢ ; _⋆_ to _⋆ˢ_ ; id to idˢ ; ⋆IdR to ⋆IdRˢ ; ⋆IdL to ⋆IdLˢ)
        open Functor
        open Bifunctor
        
        open import Cubical.Categories.Constructions.BinProduct

        open BifunctorPar
        diagram' : obᶜ → BifunctorPar ((C ×C C) ^op) (C ×C C) (SET (ℓ-max ℓC ℓC'))
        diagram' c . Bif-ob (c₁⁻ , c₂⁻) (c₁⁺ , c₂⁺) = 
            ((((C)[ c , c₁⁺ ⊗ c₂⁺ ]) × fst ( F ⟅ c₁⁻ ⟆ )) × fst ( G ⟅ c₂⁻ ⟆ )) , 
            isSet× (isSet× isSetHomC (snd ( F ⟅ c₁⁻ ⟆ ))) (snd ( G ⟅ c₂⁻ ⟆ )) 
        diagram' c . Bif-hom× (f₁ , f₂)(g₁ , g₂) = map-× (map-× ((λ m → m ⋆⟨ C ⟩ (g₁ ⊗ₕ g₂))) ((F ⟪ f₁ ⟫))) ((G ⟪ f₂ ⟫)) 
        diagram' c . Bif-×-id = funExt λ{ ((f , Fc) , Gc) → 
                ≡-× (
                    ≡-× ((cong (λ h → f ⋆ᶜ h) (─⊗─ .F-id )) ∙ ⋆IdRᶜ f) 
                        (funExt⁻  (F .F-id) Fc)) 
                ((funExt⁻ (G .F-id) Gc)) } 
        diagram' c . Bif-×-seq (f₁ , f₂) (g₁ , g₂)(h₁ , h₂)(i₁ , i₂) = 
                funExt λ ((f , Fc) , Gc) → 
                    ≡-× 
                        (≡-×  
                            ((cong (λ h → f ⋆ᶜ h) (─⊗─ .F-seq _ _ )) ∙ sym (⋆Assocᶜ _ _ _)) 
                            ((funExt⁻ (F .F-seq _ _) Fc))) 
                        (funExt⁻ (G .F-seq _ _) Gc)
        
        diagram : obᶜ → Bifunctor ((C ×C C) ^op) (C ×C C) (SET (ℓ-max ℓC ℓC')) 
        diagram c = mkBifunctorPar (diagram' c)

        open import src.Data.Coend

        Day : (c : obᶜ) → Coend (diagram c)
        Day c = Set-Coend (diagram c) 

        open import Cubical.HITs.SetCoequalizer.Base
        open Coend
        open Cowedge
        open Functor

        day : {z x y : obᶜ} → ((C)[ z , (x ⊗ y) ]) → ( fst ( F ⟅ x ⟆ ))→  ( fst ( G ⟅ y ⟆ )) → fst( Day z .cowedge .nadir) 
        day {x = x}{y} f Fx Gy = inc ((x , y) , (f , Fx) , Gy)

        day-ap : {i a b : obᶜ} {h h' : (C)[ i , (a ⊗ b) ]} {x x' : fst ( F ⟅ a ⟆) } {y y' :  fst (G ⟅ b ⟆) }
            → h ≡ h' → x ≡ x' → y ≡ y' → day h x y ≡ day h' x' y'
        day-ap {a = a} {b} p q r i =  inc ((a , b) , (p i , q i) , r i) 

        day-apₘ : ∀ {i a b} {h h' : (C)[ i , (a ⊗ b)]} {x y} → h ≡ h' → day h x y ≡ day h' x y
        day-apₘ p = day-ap p refl refl

        day-fact : {x y z y' z' : obᶜ}{f : C [ y' , y ]}{g : C [ z' , z ]}{h : C [ x , (y' ⊗ z') ]}{Fy : F .F-ob y .fst}{Gz : G .F-ob z .fst} → 
            {fgh : C [ x , (y ⊗ z) ]}(p : fgh ≡ (h ⋆⟨ C ⟩ (f ⊗ₕ g))) → 
            day fgh Fy Gz ≡ day h (F .F-hom f Fy) (G .F-hom g Gz)
        day-fact {x}{y}{z}{y'}{z'}{f}{g}{h}{Fy}{Gz}{fgh} p = 
            day-ap p (sym (funExt⁻ (F .F-id ) Fy)) ((sym (funExt⁻ (G .F-id ) Gz))) 
            ∙ coeq ((y , z) , ((y' , z') , (f , g) , (h , Fy) , Gz)) 
            ∙ day-ap (cong (λ hole → h ⋆ᶜ hole) (─⊗─ .F-id) ∙ ⋆IdRᶜ h) refl refl

        Day-cowedge : ∀ {x} {y} → (C)[ y ,  x ] → Cowedge (diagram x)
        Day-cowedge {_} {y} _ .nadir = Day y .cowedge .nadir
        Day-cowedge f .ψ (a , b) ((g , Fa) , Gb) = day (f ⋆ᶜ g) Fa Gb
        Day-cowedge f .extranatural {c}{c'} (f₁ , f₂) = 
            funExt λ { ((x→c'₁⊗c'₂ , Fc'1) , Gc'2) → {! day-fact {f = f₁}{f₂}{x→c'₁⊗c'₂}{Fc'1}{Gc'2} ? !} }
            -- {!  day-fact {f = f₁}{f₂}{x→c'₁⊗c'₂}{Fc'1}{Gc'2} ? !} }

        factor' : ∀ {i} (W : Cowedge (diagram i)) → fst(Day i . cowedge .nadir) → fst (W .nadir)
        factor' W = Day _ .factor W 
    
        open import Cubical.HITs.SetCoequalizer.Properties
        open UniversalProperty
        _⊗ᴰ_ : Presheaf (MC .StrictMonCategory.C) (ℓ-max ℓC ℓC')
        _⊗ᴰ_ .F-ob x = Day x .cowedge .nadir
        _⊗ᴰ_ .F-hom {y}{x} f = factor' (Day-cowedge f)
        _⊗ᴰ_ .F-id = sym (uniqueness  {!   !} {!   !} {!   !} {!   !} {!   !} {!   !} {!   !})
            --funExt λ{x → {! coeq  ?  !} }
        _⊗ᴰ_ .F-seq f g = funExt λ nad → {!   !} 

    module _ (MC : StrictMonCategory ℓC ℓC') where 
        open StrictMonCategory MC 
        --open Category C renaming (ob to obᶜ ; _⋆_ to _⋆ᶜ_ ; id to idᶜ ; ⋆IdL to ⋆IdLᶜ ; ⋆IdR to ⋆IdRᶜ ;  ⋆Assoc to ⋆Assocᶜ ; isSetHom to isSetHomC )
    
        open import Cubical.Categories.Constructions.BinProduct
        open Functor

        PshC = PresheafCategory C (ℓ-max ℓC ℓC')

       -- Dmap : PshC [ ]

        Day-Functor : Functor (PshC ×C PshC) PshC 
        Day-Functor .F-ob (F , G)= _⊗ᴰ_ {MC = MC} F G
        Day-Functor .F-hom {(x₁ , x₂)}{(y₁ , y₂)}(f₁ , f₂) = {!   !}
        Day-Functor .F-id = {!   !}
        Day-Functor .F-seq = {!   !}

        I⨂ : Category.ob PshC
        I⨂ = LiftF {_}{(ℓ-max ℓC ℓC')} ∘F (C [-, unit ])

        open import Cubical.Categories.Functors.HomFunctor
        open MonoidalStr
        open import Cubical.Categories.Yoneda.More
        PshMon : MonoidalStr PshC 
        PshMon .tenstr = record { ─⊗─ = Day-Functor ; unit = I⨂ } --{! C [-, unit MC ] !} }
        PshMon .α = {!   !}  
        PshMon .η = {!   !}
        PshMon .ρ = {!   !}
        PshMon .pentagon = {!   !}
        PshMon .triangle = {!   !}

        Day-Monoidal : MonoidalCategory (ℓ-suc (ℓ-max ℓC ℓC')) (ℓ-max ℓC ℓC')
        Day-Monoidal = record { C = PshC ; monstr = PshMon } 