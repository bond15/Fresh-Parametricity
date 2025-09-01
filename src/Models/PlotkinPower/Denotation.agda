{-# OPTIONS --allow-unsolved-metas  --type-in-type #-}
module src.Models.PlotkinPower.Denotation where 
    open import Cubical.Foundations.HLevels hiding (extend)
    open import Cubical.Foundations.Prelude  
    open import Cubical.Categories.Category
    open import Cubical.Categories.Functor
    open import Cubical.Categories.Instances.Functors
    open import Cubical.Categories.Instances.Sets
    open import Cubical.Categories.NaturalTransformation
    open import Cubical.Categories.Functors.Constant
    open import Cubical.Categories.Presheaf.Base
    open import Cubical.Categories.Presheaf.Constructions
    open import Cubical.Categories.Bifunctor.Redundant hiding (Fst)
    open import Cubical.Categories.Monoidal.Base
    open import src.Data.DayConv
    open import Cubical.Foundations.Isomorphism
    open import Cubical.Data.Sigma 
    open import Cubical.HITs.SetCoequalizer
    open import src.Data.Coend
    open import Cubical.Categories.Constructions.BinProduct renaming (_×C_ to _B×C_)
    open import src.Data.PresheafCCC
    open import Cubical.Categories.Yoneda.More
    open import Cubical.Foundations.Function
    open import Cubical.Data.Sigma 
    open import Cubical.Categories.Instances.Discrete
    
    open Category
    open Functor

    open import src.Data.FinSet
    open Monoidal

    open import src.Data.PlotkinPower
    open import src.Data.BiDCC
    open import src.Data.Semicartesian
    

    module _ {ℓ ℓ' : Level} where 
        ℓm = (ℓ-max ℓ ℓ')

       -- opmon : StrictMonCategory (ℓ-suc ℓ')  ℓ'
      --  opmon = SMC ^opMon

        open PP (SMC {ℓm})
        open Mod {ℓ-suc ℓm}{ℓm} opmon

        open import Cubical.Data.Sum

        _ : {x : ob FS} → 𝓥unit .F-ob x .fst 
        _ = lift {!   !} 
        
        hmm : {x : ob C} → C [ ⊗C .Functor.F-ob (x , Cunit) , x ]
        hmm = inl , isEmbedding-inl
        
        open NotStrict 
            (inl , isEmbedding-inl) 
            {!   !} 
            (inr , isEmbedding-inr) 
            {!   !} 
            {!   !} 
            {!   !} 
            {!   !} 

        open import Cubical.Data.FinSet.Base
        
        {- 
        newcase : 
            {Γ : ob 𝒱}{B : ob 𝒞}→ 
            (ty : SynTy') → 
            computation (Γ ⨂ᴰᵥ Case ty) B → 
            computation Γ B        
        -}
        Names : ob 𝓥 
        Names .F-ob x = x .fst , isFinSet→isSet (x .snd)
        Names .F-hom f x = f .fst  x
        Names .F-id = refl
        Names .F-seq _ _ = refl 

        open NatTrans





        open NatTrans

        open import Cubical.Data.Unit
        open import Cubical.Data.FinSet.Properties
        Unit*Fin : FinSet _
        Unit*Fin = Unit* , EquivPresIsFinSet 
                            (isoToEquiv (iso 
                                            (λ{tt  → tt*}) 
                                            (λ{tt* → tt}) 
                                            (λ{ tt*  → refl}) 
                                            (λ{ tt → refl }))) isFinSetUnit

        open import Cubical.Categories.Instances.FunctorAlgebras
        open Algebra

        open import Cubical.Data.Empty

        module Bad (alg : Algebra T' )
                 (x y : ob C)
                 (e : (alg .carrier) .F-ob (⊗C .F-ob (x , y)) .fst)
                 (fact : (alg .carrier) .F-ob x .fst ≡ ⊥) where

            yikes : ⊥ 
            yikes = transport fact (alg .str .N-ob x (y , e) )

        yikes : ⊥ 
        yikes = Bad.yikes 
                (algebra Names (natTrans (λ{x (y , Nxy) → {!   !}}) {!   !})) 
                {!   !} 
                {!   !}  
                {!   !} 
                {!   !}
        
        open import Cubical.Categories.Instances.EilenbergMoore
        open IsEMAlgebra
        -- where is the future world ..?
        -- this is exactly 𝓥 [ Γ ⨂ᴰ Names , B .carrier ] → 𝓥 [ Γ , B .carrier ]
        -- for a CBV languange, this would be 𝓥 [ Γ ⨂ᴰ Names , T(B .carrier) ] → 𝓥 [ Γ , T(B .carrier) ] ?
        new : {Γ : ob 𝓥}{B : ob 𝓒} → 
            𝓥 [ Γ ⨂ᴰ Names , U .F-ob B ] → 
            𝓥 [ Γ , U .F-ob B ]
        new {Γ} {B} f .N-ob x Γx = 
            (B .fst .str) .N-ob 
                x 
                (Unit*Fin , 
                f .N-ob (⊕ .F-ob (x , Unit*Fin)) (inc ((x , Unit*Fin) , ((FS .id , Γx) , tt*))))
            
            -- goal where 
            {-

            x' : ob FS
            x' = ⊕ .F-ob (x , Unit*Fin)

            hm : fst (carrier (fst B) .F-ob x') 
            hm = f .N-ob x' (inc ((x , Unit*Fin) , ((FS .id , Γx) , tt*)))


            -- use the algebra..

            al : 𝓥 [ T (B .fst .carrier) , B .fst .carrier ]
            al = B .fst .str


            goal : fst (carrier (fst B) .F-ob x)
            goal = al .N-ob x (Unit*Fin , hm)
                --carrier (fst B) .F-hom {!   !}  hm
            -}
        new {Γ} {B} f .N-hom g = {!  ⨂UP .fun f .N-hom (g , ?)   !} ∙ {!   !} where 
            open Iso
            open DayUP
       -- open Mod opmon using (𝓥× ; _⨂Ext_)
        open DayUP

        weak' : {Γ : ob 𝓥}{A : ob 𝓒} → 𝓥 [ Γ , U .F-ob A ] → 𝓥× [ Γ ⨂Ext Names , U .F-ob A ∘F (⊗C ^opF) ]
        weak' {Γ}{A} M .N-ob (x , _) (γx , _) = A .fst .carrier .F-hom Inl (M .N-ob x γx)
        weak' {Γ}{A} M .N-hom = {!   !}

        open Iso
        weak : {Γ : ob 𝓥}{A : ob 𝓒} → 𝓥 [ Γ , U .F-ob A ] → 𝓥 [ Γ ⨂ᴰ Names , U .F-ob A ] 
        weak M = ⨂UP .inv (weak' M) 
        

        drop : {Γ : ob 𝓥}{A : ob 𝓒} → (M : 𝓥 [ Γ , U .F-ob A ]) → M ≡ new {B = A} (weak {A = A}M) 
        drop {Γ}{A} M = makeNatTransPath (funExt λ x → funExt λ γx → {!   !})
            -- M x γx = alg_x (Unit* , A(inl)(M x γx)))



        -- given some world, Name selects a name in that world
        Name : ob 𝓥 
        Name = FS [ Unit*Fin ,-]

        open import Cubical.Functions.Embedding
        idea : {A : ob 𝓥}{x : ob FS} → Iso ((Name ⊸ A) .F-ob x .fst) (A .F-ob (⊗C .F-ob (x , Unit*Fin)) .fst) 
        idea {A} {x}= iso 
                foo 
                bar 
                (λ Ax1 → cong (λ h → A .F-hom h Ax1) (⊗C .F-id) ∙ funExt⁻ (A .F-id) Ax1) 
                λ b → makeNatTransPath (funExt λ y → funExt λ tt→y → sym (funExt⁻ (b .N-hom tt→y) (FS .id)) ∙ cong (λ h → b .N-ob y h) (FS .⋆IdL tt→y)) where 

                foo : (Name ⊸ A) .F-ob x .fst → A .F-ob (⊗C .F-ob (x , Unit*Fin)) .fst
                foo f = f .N-ob Unit*Fin (FS .id)

                bar : A .F-ob (⊗C .F-ob (x , Unit*Fin)) .fst → (Name ⊸ A) .F-ob x .fst
                bar Ax1 = natTrans 
                            (λ{ y tt→y  → A .F-hom (⊗C .F-hom ((FS .id) , tt→y)) Ax1}) 
                            λ f → funExt λ y → {! refl  !} -- on paper, yes


        _ = {! _⊸_   !}
        -- presheaf datatypes..
        -- use generalized polynomial functors?
        record isPresheaf (A : ob FS → Set _) : Set where 
            field 
                pmap : {x y : ob FS}→ (f : FS [ x , y ]) → A x → A y 
                pid : {x : ob FS}{a : A x} → pmap (FS .id) a ≡ a 
                pseq : {x y z : ob FS}(f : FS [ x , y ] )(g : FS [ y , z ] )(a : A x)
                     → pmap g (pmap f a) ≡ pmap (f ⋆⟨ FS ⟩ g) a

        open isPresheaf


        module _(A : ob 𝓥) where 
            mutual
               -- {-# NO_POSITIVITY_CHECK #-}
                data New : ob FS → Set _ where
                    return : ∀{w} → A .F-ob w .fst → New w
                   -- newalg : ∀{w} → (Name ⊸ NA) .F-ob w .fst → New w
                    newalg : ∀{w} → (Name .F-ob Unit*Fin .fst → New (⊗C .F-ob (w , Unit*Fin))) → New w
                        --∀{w v}→ (Name .F-ob v .fst → New (⊗C .F-ob (w , v))) → New w
                        --(Name ⊸ New  w) .F-ob w .fst → New  w
                   {-} eq1 : ∀{w}{m : New w}
                        --→ ()
                        → newalg (λ _ → Nps .pmap Inl m) ≡ m
                    eq2 : ∀{w}{m : New  w}{k : (n n' : Name .F-ob Unit*Fin .fst)→ New (⊗C .F-ob (⊗C .F-ob (w , Unit*Fin) , Unit*Fin))}
                        → newalg (λ n → newalg λ n' → k n n') ≡ newalg (λ n → newalg λ n' → k n' n) -}

                Nps : isPresheaf New
                Nps .pmap f (return a) = return (A .F-hom f a)
                Nps .pmap {x}{y} f (newalg al) = newalg goal where 

                    goal : Name .F-ob Unit*Fin .fst → New (⊗C .F-ob (y , Unit*Fin))
                    goal tt→x = {!   !} where 
                    
                    --newalg λ tt→x → Nps .pmap {!   !} (al tt→x)
                Nps .pid = {!   !}
                Nps .pseq = {!   !}

                {-}
                NA : ob 𝓥 
                NA .F-ob x = New x , {!   !}
                NA .F-hom f (return x) = return (A .F-hom f x)
                NA .F-hom {x}{y} f (newalg g) = newalg (natTrans (λ z tt→z → NA .F-hom (⊗C .F-hom (f , FS .id)) (g .N-ob z tt→z)) {!   !})
                    --newalg (natTrans (λ z Nz → {! g .N-ob x   !}) {!   !})
                NA .F-id = {!   !}
                NA .F-seq = {!   !}
                -}
            
 



 
  
        