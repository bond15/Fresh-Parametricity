{-# OPTIONS --type-in-type #-}
module src.PolyEncodings where
    open import Cubical.Foundations.Prelude

    -- From Plotkin Abadi A Logic for Parametric Polymorphism

    -- encodings
    -- should be impredicative ?
    one : Set
    one = ∀(X : Set) → X → X

    ttt : one 
    ttt = λ X x → x

    lem : (X : Set)(x : X)(o : one) → o X x ≡ x 
    lem X x o = {! refl  !}

    -- cant prove this in Agda?
    -- internal parametricity?
    hm : isProp (one)
    hm x y = funExt λ X → funExt λ x' → {!   !} 

    _⨂_ : Set → Set → Set
    A ⨂ B = (X : Set) → (A → B → X) → X
    
    open import Cubical.Data.Unit
    open import Cubical.Data.Bool 
    
    pair : Unit ⨂ Bool 
    pair X f = f tt true

    fst' : Unit ⨂ Bool → Unit 
    fst' p = p Unit λ u b → u

    snd' : Unit ⨂ Bool → Bool
    snd' p = p Bool λ u b → b

    try : snd' pair ≡ true 
    try = refl

    _⨁_ : Set → Set → Set₁ 
    A ⨁ B = (X : Set) → (A → X) → (B → X) → X

    inl' : Unit ⨁ Bool 
    inl' X c1 c2 = c1 tt

    inr' : Unit ⨁ Bool 
    inr' X c1 c2 = c2 true 

    --functor 
    M : {X X' Y Y' : Set}{A : Set → Set → Set} → (X → X')→ (Y → Y') → (A X Y → A X' Y')
    M f g Axy = {!   !}

    -- initial alg 
    μ_ : (Set → Set) → Set
    μ  B = (X : Set) → ((B X → X) → X)

    fold : {B : Set → Set} → (X : Set) → ((B X → X) → μ B → X)
    fold {B} X f = λ z → z X f

    postulate
        functor : {B : Set → Set}{X Y : Set} → (X → Y) → B X → B Y 
        
    inn : {B : Set → Set}{X : Set} → B (μ B) → μ B 
    inn {B}{X} z = λ Z f → f (functor (fold {B} Z f) z)
        

