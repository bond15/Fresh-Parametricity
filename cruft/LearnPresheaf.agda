{-# OPTIONS --cubical --type-in-type  --allow-unsolved-metas #-} -- type-in-type for the exponent object in Psh-𝒞.. yeah yeah ... it will dissapear 
open import CatLib 
open import Agda.Primitive 
open import Cubical.Foundations.Prelude hiding(comp)

module cruft.LearnPresheaf  where 


    module Psh {o ℓ} (𝒞 : Category o ℓ)  where
        -- open Category
        open SetCat hiding (Sets)
        open Category

        Psh-𝒞 : Category (ℓ-max o (ℓ-suc ℓ)) (o ⊔ ℓ) 
        Psh-𝒞 .Ob = Functor.FunctorT (𝒞 ^op) (ℓSets {ℓ})
            -- Objects are functors from 𝒞 ^op to Set
        Psh-𝒞 ._⇒_ F G = F ⇛ G
            -- Morphisms are natural transformations 
        Psh-𝒞 .id {x = P} = 
            Mknt 
                (λ o → id ℓSets ) 
                -- The component of the natural transformation is the identity morphism in Set
                (λ X Y f → refl)
                -- The commuting diagram trivially becomes P(f) = P(f)
        (Psh-𝒞 ._∘_ {x = F} {y = G} {z = H} M N) = 
            (Mknt α commutes ) where 
                α₁ : (x : Ob (𝒞 ^op)) → (ℓSets ⇒ Functor.FunctorT.F₀ F x) (Functor.FunctorT.F₀ G x)
                α₁ = _⇛_.η N
                -- F₀(x) → G₀(x)

                α₂ : (x : Ob 𝒞) → (ℓSets ⇒ Functor.FunctorT.F₀ G x) (Functor.FunctorT.F₀ H x)
                α₂ = _⇛_.η M
                -- G₀(x) → H₀(x)

                -- simply compose
                α : (x : Ob 𝒞) → (ℓSets ⇒ Functor.FunctorT.F₀ F x) (Functor.FunctorT.F₀ H x)
                α o = comp (α₂ o) (α₁ o)

                sq₁ = _⇛_.is-natural N -- top square
                sq₂ = _⇛_.is-natural M -- bottom square

                -- this holds because the two squares hold
                open import Cubical.Foundations.Prelude hiding (comp)

                F₁ = Functor.FunctorT.F₁ F
                G₁ = Functor.FunctorT.F₁ G
                H₁ = Functor.FunctorT.F₁ H

                commutes : 
                    (x y : Ob (𝒞 ^op)) 
                    (f : ((𝒞 ^op) ⇒ x) y) →
                        comp (α y) (F₁ f) ≡ comp (H₁ f) (α x)
                commutes x y f =  
                        comp (α y) (F₁ f)                   ≡⟨ refl ⟩ 
                        comp (comp (α₂ y) (α₁ y)) (F₁ f)    ≡⟨ sym (ℓSets .assoc {f = (α₂ y)} {g = (α₁ y)} {h = (F₁ f)}) ⟩        
                        comp (α₂ y) (comp (α₁ y) (F₁ f))    ≡⟨ (post {h = α₂ y} (sq₁ x y f)) ⟩
                        comp (α₂ y) (comp (G₁ f) (α₁ x))    ≡⟨ ℓSets .assoc {f = (α₂ y)} {g = G₁ f} ⟩ 
                        comp (comp (α₂ y) (G₁ f) ) (α₁ x)   ≡⟨ pre (sq₂ x y f) ⟩ 
                        comp (comp (H₁ f) (α₂ x) ) (α₁ x)   ≡⟨ sym (ℓSets .assoc {f = H₁ f} {g = α₂ x})  ⟩ 
                        comp (H₁ f) (comp (α₂ x) ((α₁ x)))  ≡⟨ refl ⟩ 
                        comp (H₁ f) (α x) ∎


        Psh-𝒞 .idr {x = F} {y = G} = Nat-path (λ o → refl) where --the componets are trivially the same (idₓ ∘ αₓ ≡ αₓ)
            open NP F G
  
        Psh-𝒞 .idl {x = F} {y = G} = Nat-path (λ o → refl) where --the componets are trivially the same (αₓ ∘ idₓ ≡ αₓ)
            open NP F G
        Psh-𝒞 .assoc {w = F} {z = G}= Nat-path λ o → refl where  -- the components are trivially associative (just associatity of functions in Set)
            open NP F G



        -- See Notability 1-25-24
        module Yoneda where
            open Functor
            open FunctorT 
            open HomFunctors

            open Category 𝒞 renaming (Ob to Cob; _⇒_ to _⇒c_ ; _∘_ to _∘c_ ; id to cId ; assoc to Cassoc ; idl to  cidl)
            open Category Psh-𝒞 renaming (Ob to psh; _⇒_ to _⇒psh_)
            open Category (ℓSets {ℓ}) renaming (Ob to set; _⇒_ to _⇒s_ ; _∘_ to _∘s_)

            𝓨₀ : Ob 𝒞 → Ob Psh-𝒞
            𝓨₀ = Hom[-,_]

            𝓨₁ : {X Y : Ob 𝒞} → (f : X ⇒c Y) → 𝓨₀ X ⇒psh 𝓨₀ Y
            𝓨₁ {X} {Y} f = Mknt (λ Z → f ∘c_) (λ A B g → funExt λ h → Cassoc )

            -- MCY 
            -- Yonedda embedding
            𝓨 : FunctorT 𝒞 Psh-𝒞 
            𝓨 .F₀ = 𝓨₀ 
            𝓨 .F₁ = 𝓨₁
            𝓨 .Fid = Nat-path _ _ λ o → funExt λ g → cidl where open NP
            𝓨 .Fcomp = Nat-path _ _ λ o → funExt λ h → sym Cassoc where open NP

        module Psh-⊤ where 
            open Terminal (Psh-𝒞)
            open TerminalT

            open Functor
            open FunctorT

            term : Ob Psh-𝒞 
            term .F₀ Cob  = Terminal.TerminalT.⊤ set-term
            term .F₁ f = λ x → x
            term .Fid {F} = refl
            term .Fcomp = refl

            Psh-term : TerminalT
            Psh-term .⊤ = term
            Psh-term .⊤-is-terminal = record { ! = ! ; !-unique = uniq } where
                        ! : {A : FunctorT (𝒞 ^op) ℓSets} → A ⇛ term
                        ! = Mknt (λ X → λ _ → tt) λ X Y f → refl

                        uniq : {F : FunctorT (𝒞 ^op) ℓSets} (f : F ⇛ term) → ! ≡ f 
                        uniq {F} nt = Nat-path λ Cob → funExt λ x → unit-is-prop tt (_⇛_.η nt Cob x)  
                                        where open NP F term
    
            

        module Psh× where 
            open BinaryProducts Psh-𝒞 
            open BinaryProductsT hiding (_×_)
            open ObjectProduct Psh-𝒞
            open Product
            open import Cubical.Data.Prod
            open Functor 

            psh×₀ : {A B : Ob (𝒞 ^op)}{F G : FunctorT (𝒞 ^op) ℓSets} → 
                ((𝒞 ^op) ⇒ A) B → ((FunctorT.F₀ F A) × (FunctorT.F₀ G A)) → ((FunctorT.F₀ F B) × (FunctorT.F₀ G B))
            psh×₀ {F = F} {G} f (FA , GA) = F₁ f FA , G₁ f GA where     -- implicitly using things like ⟨_,_⟩ 
                open Functor.FunctorT G renaming (F₀ to G₀ ; F₁ to G₁)
                open Functor.FunctorT F 

            module _ (F G : Functor.FunctorT (𝒞 ^op) ℓSets) where 
                open Functor.FunctorT G renaming (F₀ to G₀ ; F₁ to G₁)
                open Functor.FunctorT F 
                open Category 𝒞 renaming (Ob to Cob ; id to cId ; _⇒_ to _⇒c_ ; _∘_ to _∘c_)

                psh× : Functor.FunctorT (𝒞 ^op) ℓSets
                psh× .FunctorT.F₀ c = (F₀ c) × (G₀ c)
                psh× .FunctorT.F₁ f pair = psh×₀ {F = F} {G = G} f pair 
                psh× .FunctorT.Fid = funExt λ {(Fa , Ga) →  
                    (F₁ cId Fa , G₁ cId Ga) ≡⟨ cong₂ _,_ (funExt⁻ (F .Fid) Fa) (funExt⁻ (G .Fid) Ga) ⟩ 
                    (Fa , Ga) ∎ }  
                psh× .FunctorT.Fcomp {f = f} {g = g} = funExt λ {(Fa , Ga) → --(F₁ (f ∘ g) Fa , G₁ (f ∘ g) Ga) ≡ (F₁ g (F₁ f Fa) , G₁ g (G₁ f Ga))
                    ((F₁ (f ∘c g) Fa , G₁ (f ∘c g) Ga)) ≡⟨ cong₂ _,_ (funExt⁻ (F .Fcomp {f = f} {g = g}) Fa) ((funExt⁻ (G .Fcomp {f = f} {g = g}) Ga)) ⟩ 
                    (F₁ g (F₁ f Fa) , G₁ g (G₁ f Ga)) ∎   }

               
            _×p_ : (F G : Functor.FunctorT (𝒞 ^op) ℓSets) → Functor.FunctorT (𝒞 ^op) ℓSets 
            F ×p G = psh× F G

            infixr 5 _×p_ 

            eq-× : {ℓ : Level}{A B : Set ℓ}{x y : A}{w z : B} → (p : x ≡ y) → (q : w ≡ z) → Path {ℓ} (A × B) (x , w) (y , z) 
            eq-× p q i = (p i) , (q i)

            π₁-psh : {F G : Ob Psh-𝒞} →  psh× F G  ⇛ F
            π₁-psh = Mknt ((λ o → λ {(x , _ ) → x})) (λ x y f → funExt λ {(x , _) → refl})

            π₂-psh : {F G : Ob Psh-𝒞} →  psh× F G  ⇛ G
            π₂-psh = Mknt ((λ o → λ {( _ , y ) → y})) (λ x y f → funExt λ {( _ , y ) → refl})

            -- this name is bad
            Psh-Product : (X Y : Ob Psh-𝒞) → Product X Y 
            Psh-Product X Y .A×B = psh× X Y
            Psh-Product X Y .π₁ = π₁-psh
            Psh-Product X Y .π₂ = π₂-psh
            Psh-Product X Y .⟨_,_⟩ {C} nt1 nt2 = Mknt η {!   !} where 
                open FunctorT X renaming(F₀ to X₀ ; F₁ to X₁)
                open FunctorT Y renaming(F₀ to Y₀ ; F₁ to Y₁)
                open FunctorT C renaming(F₀ to C₀ ; F₁ to C₁)
                open _⇛_ nt1 renaming (η to η₁ ; is-natural to is-natural₁) 
                open _⇛_ nt2 renaming (η to η₂ ; is-natural to is-natural₂) 

                η : (x : Ob 𝒞) → C₀ x → X₀ x × Y₀ x
                η x Cx = η₁ x Cx , η₂ x Cx

            Psh-Product X Y .project₁ = Nat-path _ _ λ ob → refl where open NP
            Psh-Product X Y .project₂ = Nat-path _ _ λ ob → refl where open NP
            --  unique   : π₁ ∘ h ≡ i → π₂ ∘ h ≡ j → ⟨ i , j ⟩ ≡ h 
            Psh-Product F G .unique {C} {h} {i} {j} p q = 
                Nat-path _ _ prf where 
                    open NP
                    open Category Psh-𝒞 renaming (_∘_ to _∘psh_)
                    open Category 𝒞 renaming (Ob to Cob)
                    open FunctorT F
                    open FunctorT G renaming(F₀ to G₀ ; F₁ to G₁)
                    open FunctorT C renaming(F₀ to C₀ ; F₁ to C₁)
                    open _⇛_ h renaming (η to ηₕ ; is-natural to is-naturalₕ) 
                    open _⇛_ i renaming (η to ηᵢ ; is-natural to is-naturalᵢ) 
                    open _⇛_ j renaming (η to ηⱼ ; is-natural to is-naturalⱼ) 

                    prf : (ob : Cob) → (λ Cx → ηᵢ ob Cx , ηⱼ ob Cx) ≡ ηₕ ob 
                    prf ob = funExt goal where

                        -- now this is a proof in Set using the components of the natural transformations

                        ηiob : C₀ ob → F₀ ob
                        ηiob = ηᵢ ob

                        ηjob : C₀ ob → G₀ ob
                        ηjob = ηⱼ ob

                        ηhob : C₀ ob → F₀ ob × G₀ ob
                        ηhob = ηₕ ob
                        
                        open _⇛_
                        eq₁ : (π₁-psh ∘psh h) .η ob  ≡  ηiob 
                        eq₁  = (η≡ _ _ p) ob 

                        eq₂ : (π₂-psh ∘psh h) .η ob ≡  ηjob 
                        eq₂ = (η≡ _ _ q) ob 

                        goal : (c : C₀ ob) → (ηiob c , ηjob c) ≡ ηhob c 
                        goal c = 
                            (ηiob c , ηjob c) ≡⟨ sym (eq-× {A = F₀ ob} {B = G₀ ob} foo bar ) ⟩ 
                            (((π₁-psh ∘psh h) .η ob c) , ((π₂-psh ∘psh h) .η ob c)) 
                            ≡⟨ {!   !} ⟩ {! π₁-psh .η ob  !} where 

                            foo : (π₁-psh ∘psh h) .η ob c ≡ ηiob c
                            foo = funExt⁻ eq₁ c

                            bar : (π₂-psh ∘psh h) .η ob c ≡ ηjob c
                            bar = funExt⁻ eq₂ c

                   -- funExt λ G → {!   !} where open NP

            Psh-prod : BinaryProductsT
            Psh-prod .product {F} {G}  = Psh-Product F G



        module Psh^ where 
            open Functor
            open FunctorT
            open HomFunctors
            open Yoneda

            open Psh× 
            open BinaryProducts
            open BinaryProductsT Psh-prod renaming (_×_ to _×psh_) 
            open import Cubical.Data.Prod  using (_×_ ) renaming (_,_ to _,_)
            open Category 𝒞 renaming (Ob to Cob ; _⇒_ to _⇒c_ ; _∘_ to _∘c_ ; id to cId ; assoc to Cassoc ; idl to cidl ; idr to cidr)
            open Category Psh-𝒞 renaming (Ob to psh ; _⇒_ to _⇒p_ ; _∘_ to _∘p_)
            open Category ℓSets renaming (Ob to set ; _⇒_ to _⇒s_ ; _∘_ to _∘s_)
            
            Psh-𝒞^ : (A B : Ob Psh-𝒞) → Ob Psh-𝒞
            Psh-𝒞^ A B .F₀ c = (𝓨₀ c ×psh A) ⇛ B -- TODO: type-in-type violation here (should this be Hom instead of ⇛?)
            Psh-𝒞^ A B .F₁ {X} {Y} = fmap where 
                fmap : (f : Y ⇒c X) → ((𝓨₀ X ×psh A) ⇛ B) → ((𝓨₀ Y ×psh A) ⇛ B)
                fmap y→x nt = Mknt η₃ is-natural₃ where 

                    open FunctorT A renaming (F₀ to A₀ ; F₁ to A₁)
                    open FunctorT B renaming (F₀ to B₀ ; F₁ to B₁)
                    open _⇛_ nt renaming (η to η₁ ; is-natural to is-natural₁) 
                    open _⇛_ (𝓨₁ y→x) renaming (η to η₂ ; is-natural to is-natural₂)

                    _ : (Z : Cob) → ((Z ⇒c X) × A₀ Z) ⇒s (B₀ Z)
                    _ = η₁

                    _ : (V : Cob) → (V ⇒c Y) → (V ⇒c X)
                    _ = η₂ 

                    η₃ : (Z : Cob) → ((Z ⇒c Y) × A₀ Z) ⇒s (B₀ Z)
                    η₃ Z (z→y , Az) = η₁ Z (η₂ Z z→y , Az) 

                    -- square
                    open NP
                    -- x₁ : (V ⇒c Y) × A₀ V
                    is-natural₃ : (V W : Cob) → (g : W ⇒c V) →  
                        (λ x₁ → η₃ W (psh×₀ g x₁)) ≡ (λ x₁ → B₁ g (η₃ V x₁))
                    is-natural₃ V W w→v = funExt prf where 
                            prf : (x : (V ⇒c Y) × A₀ V) → η₃ W (psh×₀ w→v x) ≡ B₁ w→v (η₃ V x)
                            prf (v→y , Av) = 
                                η₁ W ((y→x ∘c v→y ∘c w→v) , A₁ w→v Av) ≡⟨ cong₂ η₁ refl (eq-× sq₂' refl) ⟩ 
                                η₁ W (((y→x ∘c v→y) ∘c w→v) , A₁ w→v Av) ≡⟨ sq₁' ⟩ 
                                B₁ w→v (η₁ V ((y→x ∘c v→y) , Av)) ∎ where 

                                sq₁ : (λ x → η₁ W (psh×₀ w→v x)) ≡ (λ x → B₁ w→v (η₁ V x))
                                sq₁ = is-natural₁ V W  w→v

                                sq₁' : η₁ W (((y→x ∘c v→y) ∘c w→v) , A₁ w→v Av) ≡ B₁ w→v (η₁ V ((y→x ∘c v→y) , Av))
                                sq₁' = funExt⁻ sq₁ ((y→x ∘c v→y) , Av)

                                sq₂' : (y→x ∘c v→y ∘c w→v) ≡ ((y→x ∘c v→y) ∘c w→v)
                                sq₂' = funExt⁻ (is-natural₂ V W w→v) v→y
                                
            Psh-𝒞^ A B .Fid {ob} = -- fmap (id (𝒞 ^op)) nt ≡ nt
                funExt λ { nt → 
                    Nat-path ((𝓨₀ ob ×psh A)) B λ ob' → 
                        funExt λ { (ob→ob' , Aob') → 
                            cong₂ (_⇛_.η nt) refl (eq-× cidl refl) }}  where open NP 

            Psh-𝒞^ A B .Fcomp {x} {y} {z} {y→x} {z→y} =  
                funExt λ { nt → 
                    Nat-path _ _ λ ob → 
                        funExt λ { (ob→z , Aob) → 
                            cong₂ (_⇛_.η nt) refl (eq-× (sym Cassoc) refl)}} where open NP

            open Exponentials Psh-𝒞
            open ExponentialsT
            open ObjectExponential Psh-𝒞
            open ExponentialOb renaming (product to expprod)
            open Psh× 
            open BinaryProducts Psh-𝒞
            open ObjectProduct Psh-𝒞

            -- https://ncatlab.org/nlab/show/closed+monoidal+structure+on+presheaves
            Psh-exp : ExponentialsT
            Psh-exp .exponential {A} {B} .B^A = Psh-𝒞^ A B
            Psh-exp .exponential {A} {B} .expprod = Psh-Product ((Psh-𝒞^ A B)) A 
            Psh-exp .exponential {A} {B} .eval = Mknt η is-natural where 
                open Functor.FunctorT A renaming (F₀ to A₀ ; F₁ to A₁)
                open Functor.FunctorT B renaming (F₀ to B₀ ; F₁ to B₁)

                η : (X : Cob) → ((Hom[-, X ] ×p A) ⇛ B) × A₀ X → B₀ X
                η X (nt , AX) = η₁ X  (cId , AX)  where 
                
                    open _⇛_ nt renaming (η to η₁ ; is-natural to is-natural₁)

                is-natural : (x y : Cob) (f : y ⇒c x) → (λ x₁ → η y (psh×₀ f x₁)) ≡ (λ x₁ → B₁ f (η x x₁))
                is-natural x y f = funExt prf where 

                    prf : (p : ((Hom[-, x ] ×p A )⇛ B) × A₀ x) → η y (psh×₀ f p) ≡ B₁ f (η x p)
                    prf (nt , Ax) = goal where 
                    
                        open _⇛_ nt renaming (η to η₁ ; is-natural to is-natural₁)

                        sq : η₁ y ((cId ∘c f) , A₁ f Ax) ≡ B₁ f (η₁ x (cId , Ax))
                        sq = funExt⁻ (is-natural₁ x y f) (cId , Ax)

                        goal : η₁ y ((f ∘c cId) , A₁ f Ax) ≡ B₁ f (η₁ x (cId , Ax))
                        goal = η₁ y ((f ∘c cId) , A₁ f Ax) ≡⟨ cong₂ η₁ refl (eq-× cidr refl) ⟩ 
                               η₁ y ( f         , A₁ f Ax) ≡⟨ cong₂ η₁ refl (eq-× (sym cidl) refl) ⟩ 
                               η₁ y ((cId ∘c f) , A₁ f Ax) ≡⟨ sq ⟩ 
                               B₁ f (η₁ x (cId , Ax)) ∎

            Psh-exp .exponential {A} {B} .λg {G} {H} p nt = Mknt η {! G  !} where 
                open _⇛_ nt renaming (η to η₁ ; is-natural to is-natural₁)

                open Functor.FunctorT A renaming (F₀ to A₀ ; F₁ to A₁)
                open Functor.FunctorT B renaming (F₀ to B₀ ; F₁ to B₁)
                open Functor.FunctorT G renaming (F₀ to G₀ ; F₁ to G₁)
                open Functor.FunctorT H renaming (F₀ to H₀ ; F₁ to H₁)
                open Product p 
                open Functor.FunctorT A×B renaming (F₀ to P₀ ; F₁ to P₁)


                η : (x : Cob) → G₀ x → (Hom[-, x ] ×p A) ⇛ B 
                η x Gx = Mknt η' {!   !} where 

                    η' : (y : Cob) → (y ⇒c x) × A₀ y → B₀ y 
                    η' y (x→y , Ay) = η₁ y {!  nt !} where 

                        huh : P₀ y → B₀ y
                        huh = η₁ y
                        
        -- the category of presheaves on 𝒞 is cartesian closed
        module Psh-CCC where 
            open CartesianClosed Psh-𝒞
            open CartesianClosedT

            open Psh-⊤
            open Psh×
            open Psh^
            
            -- See also the Bachelor's thesis of Mario Garcia
            -- https://mroman42.github.io/ctlc/ctlc.pdf
            
            Psh-ccc : CartesianClosedT 
            Psh-ccc .terminal = Psh-term
            Psh-ccc .products = Psh-prod
            Psh-ccc .exponentials = Psh-exp


    -- simple F algebras for endofunctors on Set
    module comptypes where
        open Functor 
        open SetCat
        module setalgebras {ℓ : Level}(T : FunctorT (ℓSets {ℓ}) (ℓSets {ℓ})) where
            open FunctorT T renaming (F₀ to T₀ ; F₁ to fmap)
            open import Cubical.Data.Prod

            open Category ℓSets
            record T-algebra : Set ℓ where 
                constructor ⟪_,_⟫
                field 
                    carrier : Ob 
                    θ : T₀ carrier ⇒ carrier
                    -- laws
            open T-algebra

            postulate -- T is also a monad
                join : ∀ {X : Ob} → T₀ (T₀ X) → T₀ X

            -- singleton 'Set'
            -- {x}
            singleton : {ℓ : Level}{X : Set ℓ} → (x : X) → Set ℓ 
            singleton {X = X} x = Σ X (Path X x)
            
            free-T-Alg : (X : Ob) → T-algebra 
            free-T-Alg X .carrier = T₀ X
            free-T-Alg X .θ = join
            
            -- x : X allowed b/c this is Set (we can peek in object)
            singleton-T-alg : (X : Ob)(x : X) → T-algebra
            singleton-T-alg X x .carrier = singleton x
            singleton-T-alg X x .θ Tc = x , refl

            product-T-alg : (F G : T-algebra) → T-algebra 
            product-T-alg ⟪ c₁ , θ₁ ⟫ ⟪ c₂ , θ₂ ⟫ .carrier =  c₁ × c₂ 
            product-T-alg ⟪ c₁ , θ₁ ⟫ ⟪ c₂ , θ₂ ⟫ .θ Tx×y = (θ₁ (fmap proj₁ Tx×y)) , (θ₂ (fmap proj₂ Tx×y))

            exponent-T-alg : (C : T-algebra)(A : Ob) → T-algebra 
            exponent-T-alg C A . carrier = A → (C .carrier) 
            exponent-T-alg ⟪ c₁ , θ₁ ⟫ A .θ Ta→c₁ a = θ₁ (fmap (λ f → f a) Ta→c₁)


    module Syntax where 

        data VType : Set₀ 
        data CType : Set₀

        data VType where 
            One : VType 
            _×ty_ _*_ : VType → VType → VType
            U : CType → VType
        
        data CType where 
            -- \-->
            _⟶_ _-*_ : VType → CType → CType
            F : VType → CType


        data Trm : Set₀ where 
            
    module dumb where 
        open Category

        data Unit : Set₀ where 
            tt : Unit

        data ⊥ : Set₀ where 

        
        data Two : Set₀ where 
            L R : Two

        TwoCat : Category lzero lzero
        TwoCat .Ob = Two
        TwoCat ._⇒_ = λ{ L L → Unit
                         ; L R → ⊥
                         ; R L → ⊥
                         ; R R → Unit}
        TwoCat .id {L} = tt
        TwoCat .id {R} = tt
        _∘_ TwoCat {L} {L} {L} tt tt = tt
        _∘_ TwoCat {L} {L} {R} = λ()
        _∘_ TwoCat {L} {R} {L} = λ()
        _∘_ TwoCat {L} {R} {R} tt = λ()
        _∘_ TwoCat {R} {L} {L} tt = λ()
        _∘_ TwoCat {R} {R} {L} = λ()
        _∘_ TwoCat {R} {L} {R} = λ()
        _∘_ TwoCat {R} {R} {R} tt tt = tt
        TwoCat .idr {L} {L} {tt} = refl
        TwoCat .idr {R} {R} {tt} = refl
        TwoCat .idl {L} {L} {tt} = refl
        TwoCat .idl {R} {R} {tt} = refl
        TwoCat .assoc = {!   !}

        open Psh TwoCat

        Psh-Two = Psh-𝒞
        open Psh-CCC
        open CartesianClosed Psh-Two
        open CartesianClosedT Psh-ccc
        open Exponentials Psh-Two
        open ExponentialsT exponentials
        open Terminal.TerminalT
        open ObjectExponential Psh-Two
        open ExponentialOb 
        
        term : Ob Psh-Two
        term = terminal .⊤

        postulate X : Ob Psh-Two
        

        exp : ExponentialOb  term X
        exp  = exponential {term} {X}

        open import Cubical.Data.Prod
        expo : Ob Psh-Two 
        expo = exp .B^A
        foo = {!   !}
            where 
                open Functor.FunctorT
                postulate XL : F₀ X L
                thing : expo .F₀ L
                thing = Mknt (λ{L → λ{ (tt , SetCat.tt) → XL}
                              ; R → λ{(() , x₁)}}) 
                              
                              λ{L L tt → funExt λ{ (tt , SetCat.tt) → {!  !} }
                              ; L R → λ()
                              ; R L → λ()
                              ; R R tt → funExt λ{ (() , x₁) }}

            
    module Semantics (TySyn : Set) where
        open Category

        open import world TySyn
        open Psh WCat
        open Syntax

    
        Psh-World : Category _ _ 
        Psh-World = Psh-𝒞

        open Psh-CCC 
        open CartesianClosed Psh-World
        open CartesianClosedT Psh-ccc
        open Terminal.TerminalT
        open BinaryProducts.BinaryProductsT

        -- no its the monoidal structure from the day convolution
        --open Monoidal WCat

        ⦅_⦆val : VType → Psh-World .Ob
        ⦅_⦆cmp : CType → {!   !} 
        
        ⦅ One ⦆val = terminal .⊤ 
        ⦅ T₁ ×ty T₂ ⦆val =  _×_ products ⦅ T₁ ⦆val ⦅ T₂ ⦆val
        ⦅ T₁ * T₂ ⦆val = {!   !} -- Day convolution?
        ⦅ U T ⦆val = ⦅ T ⦆cmp

        postulate 
            T : Functor.FunctorT Psh-World Psh-World
            
       --  open comptypes.walgebras T
        ⦅ x ⟶ x₁ ⦆cmp = {! exponent-T-alg ? ?   !}
        ⦅ x -* x₁ ⦆cmp = {!   !}
        ⦅ F x ⦆cmp = {!   !}        
            


