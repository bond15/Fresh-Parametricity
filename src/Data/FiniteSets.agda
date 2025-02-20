module src.Data.FiniteSets where 
open import Cubical.Data.Nat renaming (elim to Nelim)
open import Cubical.Data.Bool
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Data.List
open import Cubical.Foundations.Prelude
open import Agda.Builtin.Cubical.Equiv
open import Cubical.Data.Empty
open import Cubical.Foundations.HLevels


{-
data _∈_ {a} {A : Set a} : A → List A → Set a where
  eq : {x x' : A} {xs : List A} → x ≡ x' → x ∈ (x' ∷ xs)
  here  : ∀ {x}   {xs : List A} → x ∈ (x ∷ xs)
  there : ∀ {x y} {xs : List A} (x∈xs : x ∈ xs) → x ∈ (y ∷ xs)
-}

-- this is the definition of Discrete
record DecTC (A : Set) : Set where
    field 
        isDec : (x y : A) →  Dec (x ≡ y)
        --isDecProp (x ≡ y)
    _？_ : (x y : A) → Bool 
    x ？ y = Dec→Bool (isDec x y)
open DecTC{{...}}

_∈'_ : {A : Set }{{_ : DecTC A}} → A → List A → Bool
a ∈' [] = false
a ∈' (x ∷ xs) with (a ？ x )
(a ∈' (x ∷ xs)) | false = a ∈' xs
(a ∈' (x ∷ xs)) | true = true
    
_∈_ : {A : Set }{{_ : DecTC A}} → A → List A → Set
a ∈ xs = Bool→Type (a ∈' xs) 

isProp∈ : {A : Set }{{_ : DecTC A}}{x : A}{xs : List A} → isProp (x ∈ xs)
isProp∈ = isPropBool→Type {_}

_∈P_ : {A : Set }{{_ : DecTC A}} → A → List A → hProp _
_∈P_ {X}x xs = (x ∈ xs) , isProp∈ {X}{x}{xs}

All : (X : Set){{_ : DecTC X}} → List X → Set 
All X xs = (x : X) → x ∈ xs

Listable : (X : Set){{_ : DecTC X}} → Set 
Listable X = Σ[ xs ∈ (List X)] All X xs
open import Cubical.Data.Sigma 
open import Cubical.Functions.Logic

sub : (X : Set){{_ : DecTC X}}→ (X → hProp _ ) → Set 
sub X P = Σ[ xs ∈ List X ] ((x : X) → (P x .fst → x ∈ xs) × (x ∈ xs → P x .fst))
open import Cubical.Data.Fin.Recursive renaming (rec to Frec)
open import Cubical.Data.Nat.Order.Recursive
-- you should be able to define the equality of finite functions where the codomain is decidable
module _ (n : ℕ)(A : Set)⦃ _ : DecTC A ⦄(f g : Fin n → A) where

{-
_≤_ : ℕ → ℕ → Type₀
zero ≤ _ = Unit
suc m ≤ zero = ⊥
suc m ≤ suc n = m ≤ n

_<_ : ℕ → ℕ → Type₀
m < n = suc m ≤ n

    
-}
    _ : Fin 5 
    _ = toFin< 0 tt

    _ : Fin 5 
    _ = toFin< 1 tt
-- See example of tabulating and untabulatin a finite function in 
-- Tabulate  ()

-- See Prover
{-
for-all :  {X : Set} {P : X → Set}{Q : X → Set}
             → (kf : ListableSubset X P)
             → (∀ x → {p : P x} → Dec (Q x))
             →  Dec (∀ x → {p : P x} → Q x)
for-all lsbl pr1 with for-all-const {Z = λ _  → ⊤} lsbl 
  (λ x → yes tt) (λ x px _ → pr1 x {px}) 
for-all lsbl pr1 | yes p = yes (λ x {px} → p x px tt)
for-all lsbl pr1 | no ¬p = no (λ pr → ¬p (λ x px _ → pr x {px}))
-}
    tabulate' : ℕ → List ℕ 
    tabulate' zero = []
    tabulate' (suc n) = n ∷ tabulate' n

    _ : tabulate' 5 ≡ 4 ∷ 3 ∷ 2 ∷ 1 ∷ 0 ∷ []
    _ = refl

    _ = toFin 2
    tabulate : (n : ℕ) → List (Fin n)
    tabulate zero = []
    tabulate n = go n where 
        go : ℕ → List (Fin n)
        go zero = []
        go (suc m) = toFin< m {! tt  !} ∷ go m
        


instance 
    ListDec : {A : Set}{{DecA : DecTC A}} → DecTC (List A)
    ListDec {A}= record { isDec = discreteList (isDec) }

subdec : (X : Set){{_ : DecTC X}}→ (P : X → hProp _ ) → DecTC (sub X P)
subdec X P .isDec x y = discreteΣ isDec {!  isDecProp→isProp !} x y where 

    pr : (a : List X) → isProp ((x₁ : X) → (P x₁ .fst → x₁ ∈ a) × (x₁ ∈ a → P x₁ .fst))
    pr = {!   !}
    huh : (a : List X) → Discrete ((x₁ : X) → (P x₁ .fst → x₁ ∈ a) × (x₁ ∈ a → P x₁ .fst))
    huh a f g = {!pr a !}


open import Cubical.Foundations.Isomorphism
open Iso
open import Cubical.Data.Fin.Recursive

module _ (X : Set){{_ : DecTC X}} where

    to : {n : ℕ} → Iso X (Fin n) → Listable X 
    to {zero} x = {! x .inv  !}
    to {suc n} x = {!   !} , {!   !}

instance 
    booldec : DecTC Bool 
    booldec = record { isDec = λ {false false → yes refl
                                ; false true → no false≢true
                                ; true false → no true≢false
                                ; true true → yes refl }}


listablebool : Listable Bool 
listablebool = true ∷ false ∷ [] , λ { false → tt
                             ; true → tt}                      


{-

module _ (A : Set) {{DecA : DecTC A}}where
    open ListPath

    decL : (xs ys : List A) → Dec (xs ≡ ys)
    decL = discreteList (isDec)
    
    decL [] [] = yes refl
    decL [] (y ∷ ys) = no λ p → encode [] (y ∷ ys) p .lower
    decL (x ∷ xs) [] = no λ p → encode (x ∷ xs) [] p .lower
    decL (x ∷ xs) (y ∷ ys) with (decL xs ys , isDec x y)
    decL (x ∷ xs) (y ∷ ys) | yes p , yes p₁ = yes (cong₂ _∷_ p₁ p)
    decL (x ∷ xs) (y ∷ ys) | yes p , no ¬p = no λ np → ¬p (encode (x ∷ xs) (y ∷ ys) np .fst)
    decL (x ∷ xs) (y ∷ ys) | no ¬p , yes p = no λ np → ¬p (cons-inj₂ np)
    decL (x ∷ xs) (y ∷ ys) | no ¬p , no ¬p₁ = no λ np → ¬p (cons-inj₂ np)

    dec∈ : (x : A)(xs : List A) → Dec (x ∈ xs)
    dec∈ x [] = no λ ()
    dec∈ x (x' ∷ xs) with (isDec x x')
    dec∈ x (x' ∷ xs) | yes p = yes (subst (λ h → x ∈ (h ∷ xs)) p (here{x = x}{xs}))
    dec∈ x (x' ∷ xs) | no ¬p with (dec∈ x xs)
    dec∈ x (x' ∷ xs) | no ¬p | yes p = yes (there p)
    dec∈ x (x' ∷ xs) | no ¬p | no ¬p₁ = no λ np → ¬p₁ {! eq ?   !}
    --(lemma np ¬p )
-}



