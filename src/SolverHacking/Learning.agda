{-# OPTIONS --cubical #-}

open import Agda.Builtin.Reflection 
open import Agda.Builtin.Unit
open import Agda.Primitive
open import Cubical.Data.Maybe
open import Cubical.Foundations.Prelude 


module Learning where 


    postulate fail : {ℓ : Level}{A : Set ℓ} → A
    postulate success : {ℓ : Level}{A : Set ℓ} → A

    -- following https://1lab.dev/Cat.Solver.html
    module catsolve where 
        open import CatLib 
        
        module NbE {o ℓ}(𝒞 : Category o ℓ) where 
            open Category 𝒞 renaming (_⇒_ to Hom)

            post : {A B C : Ob}{g h : Hom B C}{f : Hom A B} → g ≡ h → g ∘ f ≡ h ∘ f
            post p = cong₂ _∘_ p refl

            pre : {A B C : Ob}{h : Hom B C}{f g : Hom A B} → f ≡ g → h ∘ f ≡ h ∘ g
            pre p = cong₂ _∘_ refl p

            private variable  -- this 
                A B C : Ob

            -- an expression tree for composition of morphisms in category 𝒞
            data Expr : Ob → Ob → Set (o ⊔ ℓ) where 
                `id : Expr A A
                _`∘_ : Expr B C → Expr A B → Expr A C
                _↑ : Hom A B → Expr A B

            infixr 40 _`∘_
            infix 50 _↑

            -- the "obvious" translation from expressions to (composition of) morphisms in 𝒞
            embed : {A B : Ob} → Expr A B → Hom A B
            embed `id = id
            embed (g `∘ f) = embed g ∘ embed f
            embed (f ↑) = f

            -- I don't understand the intuition behind this definition
            eval : {A B C : Ob} → Expr B C → Hom A B → Hom A C
            eval `id h = h
            eval (g `∘ f) h = eval g (eval f h)
            eval (f ↑) h = f ∘ h

            nf : {A B : Ob} → Expr A B → Hom A B
            nf e = eval e id

            eval-sound-k : {A B C : Ob} → (e : Expr B C) (f : Hom A B) → eval e f ≡ (embed e) ∘ f
            eval-sound-k `id h = 
                -- eval `id h ≡ embed `id ∘ h
                -- computes to
                -- h ≡ id ∘ h
                sym idl
                
            eval-sound-k (g `∘ f) h = 
                -- goal : eval (g `∘ f) h ≡ embed (g `∘ f) ∘ h
                eval (g `∘ f) h                 ≡⟨ refl ⟩                       -- by definition of eval
                eval g (eval f h)               ≡⟨ eval-sound-k g (eval f h) ⟩  -- induction hypothesis
                (embed g) ∘ (eval f h)          ≡⟨ pre (eval-sound-k f h) ⟩     -- induction hypothesis, again
                (embed g) ∘ ((embed f) ∘  h)    ≡⟨ assoc ⟩                      -- associativity in 𝒞
                ((embed g) ∘ (embed f)) ∘  h    ≡⟨ refl ⟩                       -- by definition of embed on _`∘_
                embed (g `∘ f) ∘ h ∎
            
            eval-sound-k (f ↑) h = 
                -- eval (f ↑) h ≡ embed (f ↑) ∘ h
                -- computes to 
                -- f ∘ h ≡ f ∘ h
                refl


            eval-sound : {A B : Ob} → (e : Expr A B) → nf e ≡ embed e 
            eval-sound e = 
                nf e            ≡⟨ refl ⟩               -- by definition of nf
                eval e id       ≡⟨ eval-sound-k e id ⟩  -- specific case of eval-sound-k
                (embed e) ∘ id  ≡⟨ idr ⟩ 
                embed e ∎


            -- so embed, nf : Expr A B → Hom A B 
            -- are extensionally equivalent..
            -- "embed is the intended semantics"
            -- "nf/eval is the optimized evaluator" .. how so?

            module example
                (A B C D E F : Ob)
                (f : Hom A B)
                (g : Hom B C)
                (h : Hom C D)
                (i : Hom D E)
                (j : Hom E F) where
                -- observe the computations on a complicated expressions
                ex₁ : Expr A F 
                ex₁ = (j ↑) `∘ (i ↑) `∘ (h ↑) `∘ (g ↑) `∘ (f ↑)

                -- nf ex₁    = j ∘ i ∘ h ∘ g ∘ f ∘ id
                -- embed ex₁ = j ∘ i ∘ h ∘ g ∘ f

                ex₂ : Expr A F 
                ex₂ = ((j ↑) `∘ (i ↑)) `∘ ((h ↑) `∘ (g ↑)) `∘ (f ↑)

                -- nf ex₂    = j ∘ i ∘ h ∘ g ∘ f ∘ id
                -- embed ex₂ = (j ∘ i) ∘ (h ∘ g) ∘ f

                ex₃ : Expr A F 
                ex₃ = (((j ↑) `∘ ((i ↑) `∘ `id)) `∘ (`id `∘ ((h ↑) `∘ `id)) `∘ (g ↑)) `∘ (f ↑)

                -- nf ex₃    = j ∘ i ∘ h ∘ g ∘ f ∘ id
                -- embed ex₃ = ((j ∘ i ∘ id) ∘ (id ∘ h ∘ id) ∘ g) ∘ f

                -- in all cases, nf computes a "normal form"
                -- this makes definitional equality of morphisms easy to prove!

                prf-hard : embed ex₁ ≡ embed ex₂ 
                prf-hard = fail -- j ∘ i ∘ h ∘ g ∘ f ≡ (j ∘ i) ∘ (h ∘ g) ∘ f
                    -- have to manually apply associativity rule multiple times...

                prf-easy' : nf ex₁ ≡ nf ex₂ 
                prf-easy' = refl
                -- holds by reflexity since both expressions compute to the same normal form

                -- with the eval-sound lemma, we can use this fact to prove the equivalence of embeddings
                prf-easy : embed ex₁ ≡ embed ex₂
                prf-easy = 
                    embed ex₁   ≡⟨ sym (eval-sound ex₁) ⟩ 
                    nf ex₁      ≡⟨ prf-easy' ⟩ 
                    nf ex₂      ≡⟨ eval-sound ex₂ ⟩ 
                    embed ex₂ ∎

            -- so make a lemma for this in general
            solve : {A B : Ob} → (x y : Expr A B) → nf x ≡ nf y → embed x ≡ embed y 
            solve x y p = 
                    embed x   ≡⟨ sym (eval-sound x) ⟩ 
                    nf x      ≡⟨ p ⟩ 
                    nf y      ≡⟨ eval-sound y ⟩ 
                    embed y ∎
                
            -- how is this related to normalization by evaluation

    -- now turn this into a tactic via reflection and metaprogramming
    module tactics where 


        module babyTactics where 
            open import Agda.Builtin.List
            open import Cubical.Reflection.Base 
            open import Agda.Builtin.String
                
            macro 
                yell! : Term → TC ⊤ 
                yell! hole = typeError ((strErr "FUCK!") ∷ [])

                echo! : Term → TC ⊤
                echo! hole = bindTC (inferType hole) λ hole' → typeError (strErr "got " ∷ termErr hole' ∷ [])

            _ : 1 ≡ 1 
            _ = {! echo!  !} 




        -- without specifying a category 
        {- 
        open import CatLib using (Category)
        open import Agda.Builtin.List
        open catsolve
        --open import Cubical.Tactics.Reflection

        --open Category

        module parse where
            asExpr' : Term → Term 
            asExpr' (def nm args)= unknown
            asExpr' _ = unknown


            -- use to see what the quoted Term is
            dumb : (quoteTerm Category.id) ≡ fail 
            dumb = {! Category.id !}

            ev : asExpr' (quoteTerm fail) ≡ unknown
            ev = refl
            -}

        -- fixing a category 𝒞
        open import CatLib using (Category)
        module reflect{o ℓ}(𝒞 : Category o ℓ) where
            open import Agda.Builtin.List
            open import Cubical.Reflection.Base 
            open import Agda.Builtin.String




            -- helper 

            quote-repr-macro : ∀ {ℓ} {A : Set ℓ} → A → Term →  TC ⊤
            quote-repr-macro a hole = 
                bindTC (quoteTC a) λ tm → 
                bindTC (quoteTC tm) λ repr → 
                typeError ( strErr "The term\n  "
                    ∷ termErr tm
                    ∷ strErr "\nHas quoted representation\n  "
                    ∷ termErr repr ∷ [])

            macro
                quote-repr! : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → A → Term → TC ⊤
                quote-repr! a = quote-repr-macro a

            open catsolve
            open NbE 𝒞


        
            -- while 1Lab generalizes this to not take an Explicit category,
            -- I'm going to parameterize one for now


            -- want to convert Agda Terms representing morphisms in category 𝒞 
            --      to         Agda Terms representing an Expression Expr

            -- While Term contains many constructors...
            _ : Term → Term 
            _ = λ {(var x args) → fail
                ; (con c args) → fail
                ; (def f args) → fail
                ; (lam v t) → fail
                ; (pat-lam cs args) → fail
                ; (pi a b) → fail
                ; (agda-sort s) → fail
                ; (lit l) → fail
                ; (meta x x₁) → fail
                ; unknown → fail}

            -- We only care about Terms id, f ∘ g and f
            -- id and _∘_ are definitions in the Category record of 𝒞
            open Category 𝒞


            -- to get a Term, we need to quote it
            quoted-id : Term 
            quoted-id = quoteTerm id

            -- observe the resulting quoted term
            -- it has two hidden arguments and one visible
            _ : quoted-id ≡ def 
                                    (quote Category.id)
                                    (unknown h∷
                                     unknown h∷ 
                                    var 0 [] v∷ [])
            _ = refl 

            -- we want to convert the Term representing id as a morphism in 𝒞 to a Term representing `id : Expr 
            quoted-id-expr : (a : Ob) → Term
            quoted-id-expr a = quoteTerm (`id {a})

            _ : ∀(a : Ob) → quoted-id-expr a ≡ con (quote `id) ((var 0 []) h∷ [])
            _ = λ a → refl

            -- This converts an 
            convert-id : Term → Term 
            convert-id (def (quote Category.id)(unknown h∷ unknown h∷ obj v∷ [])) = con (quote `id) (harg {quantity-ω} obj ∷ [])
            convert-id _ = fail

            foo = {! quote-repr! id !}





            asExpr' : Term → Term 
            -- id : {x : Ob} → x ⇒ x
            -- id takes one hidden arguement
            asExpr' (def (quote id) ( arg (arg-info hidden r) a ∷ []) ) = 
                -- then we need to construte the appropriate Expr term
                -- which is `id : {A : Ob} → Expr A A
                con (quote `id) (( arg (arg-info hidden r) a ∷ []))
            -- this parses correctly..
            asExpr' (def (quote Category.id)
                    (_ ∷
                    _ ∷
                    _ ∷
                    [])) = success
            asExpr' _ = fail

            -- this seems to be failing to parse

            {-  def (quote Category.id)
                    (arg (arg-info hidden (modality relevant quantity-ω)) unknown ∷
                    arg (arg-info hidden (modality relevant quantity-ω)) unknown ∷
                    arg (arg-info visible (modality relevant quantity-ω)) (var 0 []) ∷
                    []) 
            -}

            -- use to see what the quoted Term is
            dumb : (quoteTerm id) ≡ fail 
            dumb = {!   !}

            ev : asExpr' (quoteTerm id) ≡ success 
            ev = refl
    




























        module blarg where 

            data MyType : Set₀ where 
                myelem : MyType

                
            foo : Term → Maybe Name
            foo (var x args) = nothing
            foo (con c args) = just  c
            foo (def f args) = just f
            foo (lam v t) = nothing
            foo (pat-lam cs args) = nothing
            foo (pi a b) = nothing
            foo (agda-sort s) = nothing
            foo (lit l) = nothing
            foo (meta x x₁) = nothing
            foo unknown = nothing
            
            tyname : Name 
            tyname = quote MyType

            d : TC Definition 
            d = getDefinition tyname

            q : Set₀ → TC Term 
            q ty = quoteTC ty

   