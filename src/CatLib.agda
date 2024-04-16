{-# OPTIONS --cubical --allow-unsolved-metas  #-}
-- Based off of https://github.com/agda/agda-categories and https://1lab.dev/
module CatLib where 
    open import Cubical.Core.Everything using (_≡_)
    open import Cubical.Foundations.Prelude using (refl; ~_)

    open import Data.Nat using (ℕ;suc)
    open import Agda.Primitive using (Level; lsuc ; _⊔_)


    record is-contr {ℓ} (A : Set ℓ) : Set ℓ where
        constructor contr 
        field 
            centre : A 
            paths : (x : A) → centre ≡ x
    open is-contr public

    is-prop : ∀{ℓ} → Set ℓ → Set _ 
    is-prop A = (x y : A) → x ≡ y  

    is-hlevel : ∀{ℓ} → Set ℓ → ℕ → Set _ 
    is-hlevel A 0 = is-contr A
    is-hlevel A 1 = is-prop A
    is-hlevel A (suc n) = (x y : A) → is-hlevel (x ≡ y) n

    is-set : ∀{ℓ} → Set ℓ → Set ℓ 
    is-set A = is-hlevel A 2

    record n-Type ℓ : Set (lsuc ℓ) where
        no-eta-equality
        constructor el
        field
            ∣_∣   : Set ℓ
            --is-tr : is-hlevel ∣_∣ n
        infix 100 ∣_∣
    open n-Type using (∣_∣) public

    record Category (o h : Level) : Set (lsuc (o ⊔ h)) where 
        field 
            Ob : Set o
            _⇒_ : Ob → Ob → Set h
            id : ∀ {x} → x ⇒ x
            _∘_ : ∀{x y z} → y ⇒ z → x ⇒ y → x ⇒ z

            idr : ∀{x y}{f : x ⇒ y} → (f ∘ id) ≡ f 
            idl : ∀{x y}{f : x ⇒ y} → id ∘ f ≡ f
            assoc : ∀{w x y z} {f : y ⇒ z}{g : x ⇒ y}{h : w ⇒ x} → f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h


        infixr 40 _∘_

    

    infixl 60 _^op
    _^op : ∀ {o₁ h₁} → Category o₁ h₁ → Category o₁ h₁
    (C ^op) .Category.Ob = Category.Ob C
    (C ^op) .Category._⇒_ x y = Category._⇒_ C y x
    (C ^op) .Category.id = Category.id C
    (C ^op) .Category._∘_ f g = Category._∘_ C g f
    (C ^op) .Category.idr = Category.idl C
    (C ^op) .Category.idl = Category.idr C
    (C ^op) .Category.assoc {f = f} {g} {h} i = Category.assoc C {f = h} {g} {f} (~ i)

    module ObjectProduct{o ℓ : Level} (𝒞 : Category o ℓ) where
        open Category 𝒞

        private 
            variable
                A B C D : Ob 
                h i j : A ⇒ B

        record Product (A B : Ob) : Set (o ⊔ ℓ) where
            infix 10 ⟨_,_⟩

            field
                A×B   : Ob
                π₁    : A×B ⇒ A
                π₂    : A×B ⇒ B
                ⟨_,_⟩ : C ⇒ A → C ⇒ B → C ⇒ A×B

                project₁ : π₁ ∘ ⟨ h , i ⟩ ≡ h
                project₂ : π₂ ∘ ⟨ h , i ⟩ ≡ i
                unique   : π₁ ∘ h ≡ i → π₂ ∘ h ≡ j → ⟨ i , j ⟩ ≡ h 

        
        module Morphisms where 

            open Product
            infix 10 [_]⟨_,_⟩ [_⇒_]_×_
            infix 12 [[_]] [_]π₁ [_]π₂

            [[_]] : Product A B → Ob 
            [[ p ]] = p .A×B

            [_]⟨_,_⟩ : ∀(p : Product B C) → A ⇒ B → A ⇒ C → A ⇒ [[ p ]]
            [ p ]⟨ f , g ⟩ = ⟨_,_⟩ p f g

            [_]π₁ : ∀(p : Product A B) → [[ p ]] ⇒ A 
            [ p ]π₁ = π₁ p

            [_]π₂ : ∀(p : Product A B) → [[ p ]] ⇒ B
            [ p ]π₂ = π₂ p

            [_⇒_]_×_ : ∀(p₁ : Product A C)(p₂ : Product B D) → (A ⇒ B) → (C ⇒ D) → ([[ p₁ ]] ⇒ [[ p₂ ]])
            [ p₁ ⇒ p₂ ] f × g = [ p₂ ]⟨ f ∘ [ p₁ ]π₁ , g ∘ [ p₁ ]π₂ ⟩ 



    module ProductCat  where 
        open Category
        open import Data.Product
        open import Function hiding (id; _∘_)
        Product : {o o' h h' : Level} → Category o h → Category o' h' → Category (o ⊔ o') (h ⊔ h')
        Product C D .Ob = C .Ob × D .Ob
        (Product C D ⇒ (C₁ , D₁)) (C₂ , D₂) = (C ._⇒_) C₁ C₂ × (D ._⇒_) D₁ D₂
        Product C D .id = (C .id) , (D .id)
        Product C D ._∘_ = zip (C ._∘_) (D ._∘_)
        Product C D .idr {f = f , g} = λ i → ((C .idr {f = f}) i) , D .idr {f = g} i
        Product C D .idl {f = f , g} = λ i → C .idl {f = f} i , D .idl {f = g} i 
        Product C D .assoc {f = f₁ , f₂} {g₁ , g₂} {h₁ , h₂} = λ i → C .assoc {f = f₁}{g₁}{h₁} i , D .assoc {f = f₂}{g₂}{h₂} i
                

    module BinaryProducts {o h} (𝒞 : Category o h) where
        open ObjectProduct 𝒞
        open Category 𝒞
        open import Level using (levelOfTerm)
        private 
            variable
                A B C D : Ob 

        record BinaryProductsT : Set (levelOfTerm 𝒞) where
            infixr 7 _×_

            field
                product : ∀ {A B : Ob} → Product A B

            _×_ : Ob → Ob → Ob
            A × B = Product.A×B (product {A} {B})


            
            --_⁂_ : A ⇒ B → C ⇒ D → A × C ⇒ B × D
            --f ⁂ g = [ product ⇒ product ] f × g

    module ObjectExponential {o h} (𝒞 : Category o h) where 
        open Category 𝒞
        open ObjectProduct 𝒞

        record ExponentialOb (A B : Ob) : Set (o ⊔ h) where 
            field
                B^A : Ob 
                product : Product B^A A 

            open Product
            B^A×A : Ob 
            B^A×A = product .A×B

            field 
                eval : B^A×A ⇒ B
                λg : {X A : Ob}(X×A : Product X A) → ((X×A .A×B) ⇒ B) → (X ⇒ B^A)
                
    module Exponentials {o h} (𝒞 : Category o h) where 
        open Category 𝒞 
        open ObjectExponential 𝒞
        open import Level using (levelOfTerm)

        record ExponentialsT : Set (levelOfTerm 𝒞) where
            field 
                exponential : {A B : Ob} → ExponentialOb A B

    module Terminal {o h} (𝒞 : Category o h) where
        open Category 𝒞
        
        record IsTerminal(⊤ : Ob) : Set (o ⊔ h) where
            field
                ! : {A : Ob} → (A ⇒ ⊤)
                !-unique : ∀{A : Ob} → (f : A ⇒ ⊤) → ! ≡ f

        record TerminalT : Set (o ⊔ h) where 
            field 
                ⊤ : Ob 
                ⊤-is-terminal : IsTerminal ⊤

    module Cartesian {o h} (𝒞 : Category o h) where 
        open import Level using (levelOfTerm)
        open Terminal 𝒞 using (TerminalT)
        open BinaryProducts 𝒞 using (BinaryProductsT)

        record CartesianT : Set (levelOfTerm 𝒞) where 
            field 
                terminal : TerminalT
                products : BinaryProductsT
                
    -- https://github.com/agda/agda-categories/blob/master/src/Categories/Category/CartesianClosed/Canonical.agda
    module CartesianClosed {o h} (𝒞 : Category o h) where 
        open import Level using (levelOfTerm)
        open Terminal 𝒞 using (TerminalT)
        open BinaryProducts 𝒞 using (BinaryProductsT)
        open Exponentials 𝒞 using (ExponentialsT)

        record CartesianClosedT : Set (levelOfTerm 𝒞) where 
            field 
                terminal : TerminalT
                products : BinaryProductsT
                exponentials : ExponentialsT

    module Equalizer {o ℓ} (𝒞 : Category o ℓ) where 
        open Category 𝒞

        private 
            variable
                A B X : Ob 
                h i l : A ⇒ B

        record IsEqualizer {E : Ob} (arr : E ⇒ A) (f g : A ⇒ B) : Set (o ⊔ ℓ) where  
            field 
                equality : f ∘ arr ≡ g ∘ arr 
                equalize : ∀{h : X ⇒ A} → f ∘ h ≡ g ∘ h → X ⇒ E
                universal : ∀{eq : f ∘ h ≡ g ∘ h} → h ≡ arr ∘ equalize eq
                unique : ∀{eq : f ∘ h ≡ g ∘ h} → h ≡ arr ∘ i → i ≡ equalize eq

        record EqualizerT (f g : A ⇒ B) : Set (o ⊔ ℓ) where 
            field 
                {obj} : Ob 
                arr : obj ⇒ A 
                isEqualizer : IsEqualizer arr f g

    module Pullback {o ℓ}(𝒞 : Category o ℓ) where
        open Category 𝒞 
        private
            variable
                A B X Y Z  : Ob
                h₁ h₂ i f g : A ⇒ B 

        record IsPullback {P : Ob} (p₁ : P ⇒ X) (p₂ : P ⇒ Y)(f : X ⇒ Z)(g : Y ⇒ Z) : Set (o ⊔ ℓ) where 
            field
                commute : f ∘ p₁ ≡ g ∘ p₂
                universal : ∀{h₁ : A ⇒ X}{h₂ : A ⇒ Y} → f ∘ h₁ ≡ g ∘ h₂ → A ⇒ P 
                unique : ∀{eq : f ∘ h₁ ≡ g ∘ h₂} → 
                            p₁ ∘ i ≡ h₁ → p₂ ∘ i ≡ h₂ → 
                            i ≡ universal eq
                p₁∘universal≈h₁  : ∀ {eq : f ∘ h₁ ≡ g ∘ h₂} →
                         p₁ ∘ universal eq ≡ h₁
                p₂∘universal≈h₂  : ∀ {eq : f ∘ h₁ ≡ g ∘ h₂} →
                         p₂ ∘ universal eq ≡ h₂

        record PullbackT (f : X ⇒ Z) (g : Y ⇒ Z) : Set (o ⊔ ℓ) where 
            field 
                {P} : Ob 
                p₁ : P ⇒ X 
                p₂ : P ⇒ Y 
                isPullback : IsPullback p₁ p₂ f g 



        open ObjectProduct 𝒞 
        open Equalizer 𝒞 
        -- do this proof later
        Product×Equalizer⇒Pullback : (p : Product A B) → EqualizerT (f ∘ Product.π₁ p) (g ∘ Product.π₂ p) → PullbackT f g
        Product×Equalizer⇒Pullback = {!   !}

    module Finitely {o ℓ} (𝒞 : Category o ℓ) where 
        open import Level using (levelOfTerm)

        open Category 𝒞 
        open BinaryProducts 𝒞 using (BinaryProductsT)
        open Cartesian 𝒞 using (CartesianT)
        open Equalizer 𝒞 using (EqualizerT)
        open Pullback 𝒞 using (PullbackT; Product×Equalizer⇒Pullback)

        record FinitelyComplete : Set (levelOfTerm 𝒞) where 
            field 
                cartesian : CartesianT
                equalizer : ∀ {A B : Ob} → (f g : A ⇒ B) → EqualizerT f g

            pullback : ∀{X Y Z : Ob} → (f : X ⇒ Z) → (g : Y ⇒ Z) → PullbackT f g  
            pullback f g = Product×Equalizer⇒Pullback (BinaryProductsT.product (CartesianT.products cartesian)) (equalizer _ _)

    module Functor {o ℓ o' ℓ'}(𝒞 : Category o ℓ)(𝒟 : Category o' ℓ') where
        open import Level using (levelOfTerm)

        open Category 𝒞 renaming (Ob to Obᶜ; _⇒_ to _⇒ᶜ_; id to idᶜ; _∘_ to _∘ᶜ_)
        open Category 𝒟 renaming (Ob to Obᵈ; _⇒_ to _⇒ᵈ_; id to idᵈ; _∘_ to _∘ᵈ_)

        record FunctorT : Set (o ⊔ o' ⊔ ℓ ⊔ ℓ') where 
            field
                F₀ : Obᶜ → Obᵈ
                F₁ : {A B : Obᶜ} → (f : A ⇒ᶜ B) → F₀ A ⇒ᵈ F₀ B

                Fid : {A : Obᶜ} → F₁ (idᶜ {A}) ≡ idᵈ { F₀ A }
                Fcomp : {A B C : Obᶜ}{f : A ⇒ᶜ B}{g : B ⇒ᶜ C} → F₁ (g ∘ᶜ f) ≡ (F₁ g ∘ᵈ F₁ f)

    module ContraFunctor {o ℓ o' ℓ'}(𝒞 : Category o ℓ)(𝒟 : Category o' ℓ') where
        open import Level using (levelOfTerm)

        open Category 𝒞 renaming (Ob to Obᶜ; _⇒_ to _⇒ᶜ_; id to idᶜ; _∘_ to _∘ᶜ_)
        open Category 𝒟 renaming (Ob to Obᵈ; _⇒_ to _⇒ᵈ_; id to idᵈ; _∘_ to _∘ᵈ_)

        record ContraFunctorT : Set (o ⊔ o' ⊔ ℓ ⊔ ℓ') where 
            field
                F₀ : Obᶜ → Obᵈ
                F₁ : {A B : Obᶜ} → (f : A ⇒ᶜ B) → F₀ B ⇒ᵈ F₀ A

                Fid : {A : Obᶜ} → F₁ (idᶜ {A}) ≡ idᵈ { F₀ A }
                Fcomp : {A B C : Obᶜ}{f : A ⇒ᶜ B}{g : B ⇒ᶜ C} → F₁ (g ∘ᶜ f) ≡ (F₁ f ∘ᵈ F₁ g)

    module Functors {o ℓ}{𝒞 : Category o ℓ} where 

        open Functor 𝒞 𝒞
        open import Cubical.Foundations.Prelude using (refl)
        Id : {o₁ h₁ : Level} → {Cat : Category o₁ h₁} → FunctorT
        Id = record { F₀ = λ x → x ; F₁ = λ x → x ; Fid = refl ; Fcomp = refl }


    -- covariant in both args

    module BiFunctor {o ℓ}(𝒞 𝒟 ℬ : Category o ℓ) where
        open import Level using (levelOfTerm)

        open Category ℬ renaming (Ob to Obᵇ; _⇒_ to _⇒ᵇ_; id to idᵇ; _∘_ to _∘ᵇ_)
        open Category 𝒞 renaming (Ob to Obᶜ; _⇒_ to _⇒ᶜ_; id to idᶜ; _∘_ to _∘ᶜ_)
        open Category 𝒟 renaming (Ob to Obᵈ; _⇒_ to _⇒ᵈ_; id to idᵈ; _∘_ to _∘ᵈ_)

        record BiFunctorT : Set (levelOfTerm 𝒞) where 
            field
                F₀ : Obᵇ → Obᶜ → Obᵈ
                F₁ : {A B : Obᵇ}{C D : Obᶜ} → (f : A ⇒ᵇ B)(g : C ⇒ᶜ D) → F₀ A C ⇒ᵈ F₀ B D

                Fid : {A : Obᵇ}{C : Obᶜ} → F₁ (idᵇ {A}) (idᶜ {C}) ≡ idᵈ { F₀ A C }
                Fcomp : {A B C : Obᵇ}{f  : A ⇒ᵇ B}{g  : B ⇒ᵇ C}
                        {X Y Z : Obᶜ}{f' : X ⇒ᶜ Y}{g' : Y ⇒ᶜ Z}
                    → F₁ (g ∘ᵇ f) (g' ∘ᶜ f') ≡ (F₁ g  g' ∘ᵈ F₁ f f')


    module Cowedge {o ℓ}(𝒞 𝒟 : Category o ℓ) where 
        open import Cubical.Core.Everything
        open BiFunctor  𝒞  𝒟 (𝒞 ^op)
        open Category 𝒞 renaming (Ob to Obᶜ; _⇒_ to _⇒ᶜ_; id to idᶜ; _∘_ to _∘ᶜ_)
        open Category 𝒟 renaming (Ob to Obᵈ; _⇒_ to _⇒ᵈ_; id to idᵈ; _∘_ to _∘ᵈ_)

        record CowedgeT (F : BiFunctorT): Set (ℓ-max o ℓ) where 
            open BiFunctorT F
            field 
                nadir : Obᵈ
                --\psi
                ψ : ∀ (c : Obᶜ) → F₀ c c ⇒ᵈ nadir 
                {- 
                    for all morphisms f : c ⇒ c' in category C,

                    F₀(c',c)---F₁(id(c'),f)---> F₀(c',c')
                     |                          |
                     F₁(f,id(c))               ψ(c')
                     |                          |
                    F₀(c,c)---ψ(c)-----------> nadir
                -}
                extranatural : ∀{c c' : Obᶜ}→ (f : c ⇒ᶜ c') → (ψ c ∘ᵈ (F₁ f (idᶜ {c}))) ≡ (ψ c' ∘ᵈ F₁ idᶜ f)
                 
    module Coend {o ℓ} (𝒞 𝒟 : Category o ℓ) where 
        -- a universal cowedge
        open import Cubical.Core.Everything
        open BiFunctor  𝒞  𝒟 (𝒞 ^op)
        open Category 𝒞 renaming (Ob to Obᶜ ; _⇒_ to _⇒ᶜ_; id to idᶜ; _∘_ to _∘ᶜ_)
        open Category 𝒟 renaming (Ob to Obᵈ ; _⇒_ to _⇒ᵈ_; id to idᵈ; _∘_ to _∘ᵈ_)
        open Cowedge 𝒞 𝒟


        {-
            How is a cowedge universal?
            Given some cowedge W := (nadir₁ , ψ),

            then for any other cowedge W' := (nadir₂ , ψ)  -- both are cowedges for the same bifunctor F
            we can factor through a map factor : nadir₁ → nadir₂ 
         -}
        open CowedgeT
        record CoendT (F : BiFunctorT) : Set (ℓ-max o ℓ) where 
            open BiFunctorT F
            field 
                cowedge : CowedgeT F -- (w₁ , ψ₁)
                factor : (W : CowedgeT F) → cowedge .nadir ⇒ᵈ W .nadir
                -- given any (w₂ , ψ₂),
                -- and factor : w₁ → w₂ 
                -- ∀ (c : Obᶜ),
                --    ψ₁(c) : F₀(c , c) → w₁
                --    ψ₂(c) : F₀(c , c) → w₂ 
                --
                -- then naturally we want
                -- F₀(c , c)--ψ₁(c)-->w₁--factor-->w₂ ≡ F₀(c , c)--ψ₂-->w₂
                commutes : (W : CowedgeT F)(c : Obᶜ) → (factor W ∘ᵈ cowedge .ψ c) ≡ W .ψ c
                -- uniqueness of factor map?
                -- any other factor' which also satisfies the commutes property
                unique : (W : CowedgeT F)(factor' : cowedge .nadir ⇒ᵈ W .nadir) → 
                            (∀(c : Obᶜ) → (factor' ∘ᵈ cowedge .ψ c) ≡ W .ψ c) → 
                            factor' ≡ factor W

    module Iso{o ℓ} (𝒞 : Category o ℓ) where 
        open Category 𝒞

        infix 4 _≅_
        record _≅_ (A B : Ob) : Set (ℓ ⊔ o) where
            field
                from : A ⇒ B
                to   : B ⇒ A
                isoˡ : to ∘ from ≡ id
                isoʳ : from ∘ to ≡ id


    module Commutation {o ℓ}(𝓒 : Category o ℓ) where
        open Category 𝓒

        infix 1 [_⇒_]⟨_≡_⟩
        [_⇒_]⟨_≡_⟩ : ∀ (A B : Ob) → A ⇒ B → A ⇒ B → Set _
        [ A ⇒ B ]⟨ f ≡ g ⟩ = f ≡ g

        infixl 2 connect
        connect : ∀ {A C : Ob} (B : Ob) → A ⇒ B → B ⇒ C → A ⇒ C
        connect B f g = g ∘ f

        syntax connect B f g = f ⇒⟨ B ⟩ g
        
    module Monoidal {o ℓ}(𝒞 : Category o ℓ) where
        open import Level using (levelOfTerm)
        open BiFunctor using (BiFunctorT)
        open Iso 𝒞 
        open _≅_

        open Category 𝒞
        open Commutation 𝒞
        
        record MonoidalT : Set (levelOfTerm 𝒞) where 
            field 
                ⊗ : BiFunctorT 𝒞 𝒞 𝒞
                unit : Ob
                

            open BiFunctorT ⊗ 
            infixr 10 _⊗₀_ _⊗₁_ 

            _⊗₀_ : Ob → Ob → Ob
            _⊗₀_ = F₀

            _⊗₁_ : {X Y Z W : Ob} → X ⇒ Y → Z ⇒ W → (X ⊗₀ Z) ⇒ (Y ⊗₀ W)
            _⊗₁_ = F₁          

            field 
                unitorˡ : {X : Ob} → unit ⊗₀ X ≅ X
                unitorʳ : {X : Ob} → X ⊗₀ unit ≅ X
                associator : {X Y Z : Ob} → (X ⊗₀ Y) ⊗₀ Z ≅ X ⊗₀ (Y ⊗₀ Z)

            private 
                λ⇒ : {X : Ob} → (unit ⊗₀ X) ⇒ X
                λ⇒ {X} = (unitorˡ {X}) .from  

                λ⇐ : {X : Ob} →  X ⇒ (unit ⊗₀ X)
                λ⇐ {X} = (unitorˡ {X}) .to

                ρ⇒ : {X : Ob} → (X ⊗₀ unit) ⇒ X
                ρ⇒ {X} = (unitorʳ {X}) .from  
                 
                ρ⇐ : {X : Ob} →  X ⇒ (X ⊗₀ unit)
                ρ⇐ {X} = (unitorʳ {X}) .to

                α⇒ : {X Y Z : Ob} → ((X ⊗₀ Y) ⊗₀ Z) ⇒ (X ⊗₀ (Y ⊗₀ Z))
                α⇒ {X}{Y}{Z} = associator {X} {Y} {Z} .from

                α⇐ : {X Y Z : Ob} → (X ⊗₀ (Y ⊗₀ Z)) ⇒ (((X ⊗₀ Y) ⊗₀ Z))
                α⇐ {X}{Y}{Z} = associator {X} {Y} {Z} .to
            field
                pentagon : { X Y Z W : Ob } → [ (((X ⊗₀ Y) ⊗₀ Z) ⊗₀ W) ⇒ (X ⊗₀ Y ⊗₀ Z ⊗₀ W) ]⟨
                                                    α⇒ ⊗₁ id ⇒⟨ ((X ⊗₀ Y ⊗₀ Z) ⊗₀ W) ⟩ 
                                                    α⇒       ⇒⟨ (X ⊗₀ (Y ⊗₀ Z) ⊗₀ W) ⟩ 
                                                    id ⊗₁ α⇒ 
                                                ≡ 
                                                    α⇒ ⇒⟨ ((X ⊗₀ Y) ⊗₀ Z ⊗₀ W) ⟩ 
                                                    α⇒ ⟩
    
    record _⇛_ {o₁ h₁ o₂ h₂} {C : Category o₁ h₁}{D : Category o₂ h₂}(F G : Functor.FunctorT C D) : Set (o₁ ⊔ h₁ ⊔ h₂) where 
        no-eta-equality
        constructor Mknt
  
        open Functor.FunctorT F 
        open Functor.FunctorT G renaming (F₀ to G₀ ; F₁ to G₁)
        open Category D renaming (_⇒_ to _⇒D_; _∘_ to _∘D_)
        open Category C renaming (Ob to C-Ob; _⇒_ to _⇒C_)
        field 
            η : (x : C-Ob) → (F₀ x) ⇒D (G₀ x)
            is-natural : (x y : C-Ob) (f : x ⇒C y) → (η y) ∘D (F₁ f) ≡ (G₁ f) ∘D (η x)

        
    module NP {o₁ h₁ o₂ h₂} {C : Category o₁ h₁}{D : Category o₂ h₂}(F G : Functor.FunctorT C D) where 
        -- according to 1Lab https://1lab.dev/Cat.Base.html#1850
        open Category C
        open Cubical.Core.Everything
        open _⇛_
        Nat-path : {a b : F ⇛ G} → 
            ((x : Ob) → _⇛_.η a x ≡ _⇛_.η b x  )→ 
            a ≡ b 
        Nat-path = {!   !}

        ap : ∀ {a b} {A : Set a} {B : A → Set b} (f : (x : A) → B x) {x y : A}
            → (p : x ≡ y) → PathP (λ i → B (p i)) (f x) (f y)
        ap f p i = f (p i)
        {-# NOINLINE ap #-}

        η≡ : {a b : F ⇛ G} → a ≡ b → ((x : Ob) → _⇛_.η a x ≡ _⇛_.η b x)
        η≡ p x = ap (λ e → e .η x) p


    _F∘_ : {o₁ h₁ o₂ h₂ o₃ h₃ : Level} → {B : Category o₁ h₁}{C : Category o₂ h₂}{D : Category o₃ h₃}
        → Functor.FunctorT C D → Functor.FunctorT  B C → Functor.FunctorT  B D 
    _F∘_ {B = B} {C} {D} F G = comps -- note usage of {B = B} here starts the implicit arguments at B 
                                    -- instead of o₁
        where 
            module B = Category B 
            module C = Category C 
            module D = Category D 

            open Functor.FunctorT  F 
            open Functor.FunctorT  G renaming (F₀ to G₀ ; F₁ to G₁ ; Fid to G-id ; Fcomp to G-∘ )

            comp₀ : B.Ob → D.Ob 
            comp₀ x = F₀ (G₀ x)

            comp₁ : {x y : B.Ob} → B._⇒_ x y → D._⇒_ (comp₀ x) (comp₀ y)
            comp₁ f = F₁ (G₁ f)
            open import Cubical.Foundations.Prelude
            
            abstract -- makes the definition like a postulate? doesn't unfold in type checking?
                comp-id : {x : B.Ob} → comp₁ (B.id {x}) ≡ D.id {comp₀ x}
                comp-id {x} = 
                    F₁ (G₁ B.id) ≡⟨ cong F₁ (G-id) ⟩ 
                    F₁ C.id ≡⟨ Fid ⟩ 
                    D.id ∎

                comp-∘ : {x y z : B.Ob} → (f : B._⇒_ y z) → (g : B._⇒_ x y) → 
                    comp₁ (f B.∘ g) ≡ (comp₁ f D.∘ comp₁ g)
                comp-∘ f g = 
                    F₁ (G₁ (f B.∘ g))  ≡⟨ cong F₁ (G-∘ ) ⟩ 
                    (F₁ ((G₁ f) C.∘ G₁ g ) ≡⟨ Fcomp ⟩ 
                    (F₁ (G₁ f) D.∘ F₁ (G₁ g) ∎))


            comps : Functor.FunctorT B D 
            comps .Functor.FunctorT.F₀ = comp₀
            comps .Functor.FunctorT.F₁ = comp₁
            comps .Functor.FunctorT.Fid = comp-id
            comps .Functor.FunctorT.Fcomp {f = f} {g} = comp-∘ g f 
        
    record _⊣_ {o₁ h₁ o₂ h₂}{C : Category o₁ h₁}{D : Category o₂ h₂}
                (L : Functor.FunctorT C D )(R : Functor.FunctorT D C) : Set (o₁ ⊔ o₂ ⊔ h₁ ⊔ h₂) where 
        private
            module C = Category C 
            module D = Category D
        open Functor.FunctorT L renaming (F₀ to L₀ ; F₁ to L₁)
        open Functor.FunctorT R renaming (F₀ to R₀ ; F₁ to R₁)
 
        field 
            unit : Functors.Id {Cat = C} ⇛ (R F∘ L)  
            counit : (L F∘ R) ⇛ Functors.Id {Cat = D} 
        {-
            unit : 
                note that  Id {C}   : Functor C C
                and 
                        (R F∘ L) : Functor C C    
                
                unit is a natural transformation from Id {C} to (R F∘ L)
                thus there is an η where 
                    η : (x : C.Ob) → (C.Hom (Id₀ x) ((R F∘ L) x))
                    or 
                        (x : C.Ob) → (C.Hom x ((R F∘ L) x))
            likewise
            counit :
                note that Id {D} : Functor D D 
                and 
                        (L F∘ R) : Functor D D 
        
                counit is a natrual transformation from (L F∘ R) to Id {D}
                thus ther is an η where 
                    ε : (x : D.Ob) → (D.Hom ((L F∘ R) x) x)
        
            unit and counit must obey these laws
        -}
        module unit = _⇛_ unit
        open unit  
        module counit = _⇛_ counit renaming (η to ε)
        open counit
        field 
            zig : ∀{A : C.Ob} → ε (L₀ A) D.∘ L₁ (η A) ≡ D.id
            zag : ∀{B : D.Ob} → R₁ (ε B) C.∘ η (R₀ B) ≡ C.id
    

    module SetCat  where 
        open Category  
        open import Agda.Primitive
        open import Cubical.Foundations.Prelude hiding(comp)     

        comp : {ℓ : Level}{A B C : Set ℓ} → (B → C) → (A → B) → A → C 
        comp g f x = g (f x)

        pre : {ℓ : Level}{A B C : Set ℓ}{g h : B → C}{f : A → B} → (p : g ≡ h) → 
            comp g f ≡ comp h f
        pre p = cong₂ comp p  refl
            
        post : {ℓ : Level}{A B C : Set ℓ}{h : B → C}{f g : A → B} → (p : f ≡ g) → 
            comp h f ≡ comp h g
        post p = {!   !}
            
        Sets : Category (lsuc lzero) (lzero)
        Sets .Ob = Set₀
        Sets ._⇒_ X Y = X → Y
        Sets .id x = x
        Sets ._∘_ = comp
        Sets .idr = refl
        Sets .idl = refl
        Sets .assoc = refl

        ℓSets : {ℓ : Level} → Category (lsuc ℓ) ℓ 
        ℓSets {ℓ} .Ob = Set ℓ
        ℓSets ._⇒_ X Y = X → Y  
        ℓSets .id x = x
        ℓSets ._∘_ = comp
        ℓSets .idr = refl
        ℓSets .idl = refl
        ℓSets .assoc = refl

        open Terminal Sets 
        open TerminalT

        data Unit : Set₀ where 
            tt : Unit


        unit-is-prop : is-prop Unit 
        unit-is-prop tt tt = refl

        set-term : TerminalT 
        set-term .⊤ =  Unit
        set-term .⊤-is-terminal = 
            record { 
                ! = λ _ → tt ; 
                !-unique = λ f → funExt λ x → unit-is-prop tt (f x)} 


 
    module HomFunctors 
        {o ℓ}
        {𝒞 : Category o ℓ} where
        open SetCat

        open Functor
        open Category
        open import Cubical.Foundations.Prelude


        Hom[_,-] : (Ob (𝒞 ^op)) →  FunctorT 𝒞 (ℓSets)
        Hom[_,-] X = 
            record { 
                F₀ = λ Y → X ⇒c Y ;
                F₁ = λ f g → f ∘c g ; 
                Fid = funExt λ g → idlc ; 
                Fcomp = funExt λ h → sym assocc 
            } where 
                open Category 𝒞 renaming 
                    (Ob to Cob ; _⇒_ to _⇒c_; _∘_ to _∘c_; idl to idlc ; assoc to assocc)

        Hom[-,_] : (Ob 𝒞 ) →  FunctorT (𝒞 ^op) (ℓSets)
        Hom[-,_] X = 
            record { 
                F₀ = λ Y → Y ⇒c X ; -- flipped
                F₁ = λ f → _∘c f ; 
                Fid = funExt λ g → idrc ; 
                Fcomp = funExt λ h → assocc
            } where 
                open Category 𝒞 renaming 
                    (Ob to Cob ; _⇒_ to _⇒c_; _∘_ to _∘c_; idr to idrc ; assoc to assocc)

        open ProductCat
        Hom[_,_] : FunctorT (Product (𝒞 ^op) 𝒞) (ℓSets {ℓ})
        Hom[_,_] = 
            record { 
                F₀ = λ {(X , Y) → X ⇒c Y} ; 
                F₁ = λ {(f , h) g → h ∘c g ∘c f} ; 
                Fid = λ { {X , Y} → funExt λ f → 
                    cId ∘c f ∘c cId ≡⟨ idlc ⟩ 
                    f ∘c cId ≡⟨ idrc ⟩ 
                    f  ∎ };
                Fcomp = λ { {f = f , h} {f' , h'} → funExt λ g → 
                    𝒞 ._∘_ h' h ∘c g ∘c f ∘c f'  ≡⟨ {!   !} ⟩ {!   !} } --𝒞 ._∘_ h' h ∘c g ∘c f ∘c f' ≡ h' ∘c (h ∘c g ∘c f) ∘c f'
            } where
                open Category 𝒞 renaming 
                    (Ob to Cob ; _⇒_ to _⇒c_; _∘_ to _∘c_; id to cId ; idr to idrc ; idl to idlc ; assoc to assocc)

        -- よ doesn't seem to have an agda input mode mapping
        


{- Cruft

from messing up the hom functor definition 


    {- 
       record Category (o h : Level) : Set (lsuc (o ⊔ h)) where 
        field 
            Ob : Set o
    -}
    module foobar where 
        open import Agda.Primitive 
        --open Category


        no : Set₀ 
        no = {!   !} -- Set₀ 
        
        dumb1 : {Obty : Set₀} → Obty → Set₀ 
        dumb1 X = {! X  !} → {!   !}

        dumb2 : {Obty : Set₁} → Obty → Set₀ 
        dumb2 X = {! X  !} → {!   !}
        
        -- duh.. because it is the morphisms of 𝒞
        -- here Obty has to be a datatype, since Set₀ ∉ Set₀
        -- then X is an element of the datatype
        -- in which case we can't use the function arrow construction because X and Y are not Sorts
        -- but we can use the definition of morphism in 𝒞 
        -- mor is a function type where the two arguments live at a lower universe level than the result type
        -- the type constructor 
        dumb3 : {Obty : Set₀} → (X : Obty) → (Y : Obty) → (mor : Obty → Obty → Set₀) → Set₀ 
        dumb3 X Y fun = fun X Y

        -- this does not work
        test : (X : Set₀) → (Y : Set₀) → Set₁
        test X Y = X → {!  Y !}



        open import Cubical.Foundations.Prelude using (Lift ; lift ; ℓ-suc)
        {-
        record Lift {i j} (A : Type i) : Type (ℓ-max i j) where
            constructor lift
            field
                lower : A

        open Lift public 
        -}

        -- Lift : {i j : Level} (A : Set i) → Set (i ⊔ j)
        -- lift : (lower : A : Set i) → Lift A : Set (i ⊔ j)
        -- have to lift it
        lifttype : (X : Set₀) → (Y : Set₀) → Set₁
        lifttype X Y = Lift {lzero} {ℓ-suc lzero} (X → Y)

        -- (X → Y) : Set₀
        -- this does not work
        liftterm : (X Y : Set₀) → (X → Y) → Set₁
        liftterm X Y f = {!lift  f  !}

        -- this does
        liftterm' : (X Y : Set₀) → (X → Y) → lifttype X Y
        liftterm' X Y f = lift f

        dumb5 : (T : Set₀) → (e : T) → Set₀ 
        dumb5 T e = T


        dumb4 : {𝒞 : Category lzero lzero} → (X : Category.Ob 𝒞) → (Y : Category.Ob 𝒞) → Set₀
        dumb4 {𝒞} X Y = Category._⇒_ SetCat.Sets {!   !} {!   !}

        -- Category.Ob (SetCat.ℓSets {ℓ'})) : Set (ℓ-suc ℓ')
        -- Category.Ob (SetCat.ℓSets {ℓ'})) = Set ℓ'

        -- Category.Ob 𝒞  : Set ℓ

        why : (ℓ : Level)→ (ℓ' : Level) → (𝒞 : Category ℓ ℓ') → 
            (X : Category.Ob 𝒞) → ( Y : Category.Ob 𝒞) → (Category.Ob (SetCat.ℓSets {ℓ'}))
        why ℓ ℓ' 𝒞 X Y = X ⇒ Y where 
                open Category 𝒞
            -- (Category._⇒_ (SetCat.ℓSets {ℓ'})) {!  X !} {! Category.Ob 𝒞  !}
            -- ... so it is not the hom in Set.. but the Hom in C.... which is a Set... wtf
       
        
            
        -- {-# NO_UNIVERSE_CHECK #-}
        {-record Cheat ℓ : Set ℓ where 
            constructor el
            field 
                ∣_∣ : Set ℓ
        open Cheat -}

        open import Cubical.Foundations.Prelude
        data wtf ℓ : Set (lsuc ℓ) where 
            inject : Set ℓ → wtf ℓ

        foo : {ℓ : Level} → Set ℓ → Set (lsuc ℓ)
        foo x = Lift x
        
        import Cubical.Categories.Functors.HomFunctor

        test : (Ob 𝒞) → (Ob 𝒞)→ (Ob ℓSets) --(Ob ℓSets)
        test X Y = (ℓSets ._⇒_) {! Ob Sets  !} (Lift (Ob 𝒞))

-}   