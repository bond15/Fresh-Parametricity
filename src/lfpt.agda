{-# OPTIONS --cubical #-}
module lfpt where

    open import Cubical.Data.Unit renaming (Unit to ⊤)
    open import Cubical.Data.Sigma
    open import Cubical.Foundations.Prelude 


    _∘_ : {A B C : Set₀} → (B → C) → (A → B) → A → C 
    g ∘ f = λ a → g (f a)

    record point-surj {X Y : Set₀} (φ : X → Y) : Set₀ where
        field 
            ps : ∀ (q : ⊤ → Y) → Σ (⊤ → X) λ p → φ ∘ p ≡ q
   

    record hasFP {X : Set₀} (f : X → X) : Set₀ where 
        field 
            s : ⊤ → X 
            fp : s ≡ f ∘ s 

    {-# NON_TERMINATING #-}   -- obviously not terminating 
    fix' : {A B : Set} → A → (A → B)
    fix' a = fix' a a

    {-# NON_TERMINATING #-}   -- obviously not terminating 
    fix : {A B : Set} → (f : B → B) → A → (A → B) 
    fix f a = f ∘ fix f a


    Lfpt : {A B : Set₀} → (φ : A → (A → B)) → point-surj φ → ∀(f : B → B) → hasFP f 
    Lfpt {A} {B} φ φps f = prf where 

        δ : A → A × A 
        δ a = a , a

        eval : A × (A → B) → B 
        eval (a , f) = f a

        id×φ : A × A → A × (A → B)
        id×φ (a1 , a2) = a1 , (φ a2)

     --   A→B : A → B 
     --   A→B = ((f ∘ eval) ∘ id×φ ) ∘ δ
        -- fixpoint combinator
        -- because we have φ a ≡ A→B' from the pointwise surjection
        A→B' : A → B 
        A→B' a = f (φ a a)

        -- how is this step justified?
        -- Hom[1 , B^A] ≅ Hom[1×A , B] ≅ Hom[A , B] ?
        ⊤AB : ⊤ → (A → B)
        ⊤AB tt = A→B'

        ps : Σ (⊤ → A) λ p → φ ∘ p ≡ ⊤AB
        ps = point-surj.ps φps ⊤AB

        ⊤A : ⊤ → A 
        ⊤A = ps .fst 

        -- the particular choice of A from the pointwise surjection
        a : A
        a = ⊤A tt

        pprf : φ ∘ ⊤A ≡ ⊤AB
        pprf = ps .snd

        pprf' : φ a ≡ A→B'
        pprf' = funExt⁻ pprf tt

        pprf'' : φ a a ≡ A→B' a
        pprf'' = funExt⁻ pprf' a

        pprf''' : φ a a ≡ f (φ a a)
        pprf''' = φ a a       ≡⟨ pprf'' ⟩ 
                  A→B' a      ≡⟨ refl ⟩ 
                  (f (φ a a)) ∎

        
        s : ⊤ → B 
        --s = A→B' ∘ ⊤A
        s tt = f(φ a a) 
        
        prf : hasFP f -- f(φ (⊤A tt) (⊤a tt)) = f (f φ (⊤A tt) (⊤A tt))
        prf = record { s = s ; fp = funExt λ{ tt → 
                    f(φ a a)          ≡⟨ cong f pprf''' ⟩ 
                    f(f (φ a a)) ∎ } }
            
            

        