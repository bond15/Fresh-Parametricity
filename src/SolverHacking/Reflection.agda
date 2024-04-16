{-# OPTIONS --safe #-}

module Cubical.Tactics.AltFunctorSolver.Reflection where

open import Cubical.Foundations.Prelude

open import Agda.Builtin.Reflection hiding (Type)
open import Agda.Builtin.String

open import Cubical.Data.Bool
open import Cubical.Data.Sum

open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Reflection.Base
open import Cubical.Tactics.AltFunctorSolver.Solver
open import Cubical.Tactics.Reflection

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Free.Category
open import Cubical.Categories.Constructions.Free.Functor.AltPresented
open import Cubical.Categories.Functor

private
  variable
    ℓ ℓ' : Level

-- | Parses a morphism in the codomain into a morphism in the free
-- | category on the codomain with a functor from the free category on
-- | the domain

-- | Inspired by https://1lab.dev/Cat.Diagram.Product.Solver.html#reflection
module ReflectionSolver where
  module _ (domain : Term) (codomain : Term) (functor : Term) where
    -- the two implicit levels and the category
    pattern category-args xs =
      _ h∷ _ h∷ _ v∷ xs

    -- the four implicit levels, the two implicit categories and the functor
    pattern functor-args functor xs =
      _ h∷ _ h∷ _ h∷ _ h∷ _ h∷ _ h∷ functor v∷ xs


    pattern “id” A =
      def (quote Category.id) (category-args (A h∷ []))
    -- pattern “id” A =
    --   def (quote Category.id) (category-args (A h∷ []))

    pattern “⋆” f g =
      def (quote Category._⋆_) (category-args (_ h∷ _ h∷ _ h∷ f v∷ g v∷ []))

    pattern “F⟪⟫” functor f =
      def (quote Functor.F-hom) (functor-args functor (_ h∷ _ h∷ f v∷ []))

    pattern “F⟅⟆” =
      def (quote Functor.F-ob)

    -- _ : (quote Functor.F-ob) ≡ {!!}
    -- _ = {!!}

    -- Parse a morphism in the domain to a morphism in the free category
    -- buildDomExpression : Term → Term
    -- buildDomExpression “id” = con (quote FreeCategory.idₑ) []
    -- buildDomExpression (“⋆” f g) =
    --   con (quote FreeCategory._⋆ₑ_)
    --       (buildDomExpression f v∷ buildDomExpression g v∷ [])
    -- buildDomExpression f = con (quote FreeCategory.↑_) (f v∷ [])

    -- -- Parse an *object* in the codomain to an object in the free category+functor
    -- buildCodObject : Term → TC Term
    -- buildCodObject (“F⟅⟆” args) = do
    --   -- unify functor functor'
    --   -- Ae ← buildCodObject A
    --   returnTC (con (quote inl) args)
    -- buildCodObject f = returnTC (con (quote inr) (f v∷ []))

    -- Parse a morphism in the codomain to a morphism in the free category+functor
    buildCodExpression : Term → TC Term
    buildCodExpression (“id” A) =
      returnTC (def (quote Category.id) (unknown hω∷ unknown hω∷ unknown v∷ A hω∷ []))
    --returnTC (def (quote Category.id) (def {!(quote )!} {!!} v∷ [])) -- returnTC (con (quote FreeFunctor.idₑ) [])      
    -- buildCodExpression (“⋆” f g) = {!!} 
      -- ((λ fe ge → (con (quote FreeFunctor._⋆ₑ_) (fe v∷ ge v∷ [])))
      --   <$> buildCodExpression f)
      --   <*> buildCodExpression g
    -- buildCodExpression (“F⟪⟫” functor' f) = {!!}
    --   -- do
    --   -- unify functor functor'
    --   -- returnTC (con (quote FreeFunctor.F⟪_⟫) (buildDomExpression f v∷ []))
    buildCodExpression f =
      unify (quoteTerm f) (quoteTerm Category._⋆_) >> returnTC f -- returnTC (con (quote FreeFunctor.↑_) (f v∷ []))

  solve-macro : Bool -- ^ whether to give the more detailed but messier error
                     --   message on failure
              → Term -- ^ The term denoting the domain category
              → Term -- ^ The term denoting the codomain category
              → Term -- ^ The term denoting the functor
              → Term -- ^ The hole whose goal should be an equality between
                     --   morphisms in the codomain category
              → TC Unit
  solve-macro b dom cod fctor =
    equation-solver
      (quote Category.id ∷ quote Category._⋆_ ∷ quote Functor.F-hom ∷ [])
      mk-call
      b
      where

      mk-call : Term → Term → TC Term
      mk-call lhs rhs = do
        l-e ← buildCodExpression dom cod fctor lhs
        r-e ← buildCodExpression dom cod fctor rhs
        -- unify l-e r-e
        returnTC (def (quote Eval.solve) (
          dom v∷ cod v∷ fctor v∷
          l-e v∷ r-e v∷ def (quote refl) [] v∷ []))
macro
  solveFunctor! : Term → Term → Term → Term → TC _
  solveFunctor! = ReflectionSolver.solve-macro false

  solveFunctorDebug! : Term → Term → Term → Term → TC _
  solveFunctorDebug! = ReflectionSolver.solve-macro true

macro
   -- for testing
  -- parseDOb! : Term → Term → Term → Term → Term → TC Unit
  -- parseDOb! d c f exp hole = (ReflectionSolver.buildCodObject d c f exp) >>= unify hole -- do
  --   -- exp' ← 
  --   -- unify hole exp'

  parseCodExp! : Term → Term → Term → Term → Term → TC Unit
  parseCodExp! d c f exp hole = withReduceDefs (false , (quote Category.id ∷ quote Category._⋆_ ∷ quote Functor.F-hom ∷ [])) (do
    exp' ← normalise exp
    exp'' ← ReflectionSolver.buildCodExpression d c f exp'
    unify hole exp'')

private
  module ParserTests ℓc ℓc' ℓd ℓd' (C : Category ℓc ℓc')  (D : Category ℓd ℓd') (F : Functor C D) where

    open import Cubical.Categories.Constructions.Free.Category.Quiver
    open Category
    open CoUnit F

    -- tst : ∀ (A : C .ob)(B : D .ob) → Path (C .ob ⊎ D .ob) (parseDOb! C D F (F ⟅ A ⟆)) (inr B)
    -- tst A B = {!!}

    -- p0 : ∀ (A : C .ob)(B : D .ob) → C .ob ⊎ D .ob
    -- p0 A B = parseDOb! C D F (F ⟅ A ⟆) -- parseCodExp! C C C C -- parseCodExp! C D F (D .id)

    -- pp : ∀ (A : C .ob)(B : D .ob) → p0 A B ≡ inr B
    -- pp A B = {!Functor.F-ob!}
