module src.kavvos where
    open import Cubical.Data.Nat
    open import Cubical.Data.FinData
    open import Cubical.Data.Sum

{-
    -- compare this to gsoslambda
    data Term : ℕ → Set where
        var : ∀ {n} → Fin n → Term n
        lam : ∀ {n} → Term (suc n) → Term n
        app : ∀ {n} → Term n → Term n → Term n


    ex : Term 0 
    ex = lam (var zero)

-}

    mutual 
        
        data VTerm : ℕ → Set where 
            var : ∀ {n} → Fin n → VTerm n
            tt : ∀ {n} → VTerm n 
            pair : ∀ {n} → VTerm n → VTerm n → VTerm n 
            thunk : ∀ {n} → CTerm n → VTerm n

        data CTerm : ℕ → Set where 
            ret : ∀ {n} → VTerm n → CTerm n
            bind : ∀ {n} → CTerm n → CTerm (suc n) → CTerm n
            lam : ∀ {n} → CTerm (suc n) → CTerm n
            app : ∀ {n} → CTerm n → VTerm n → CTerm n 
            force : ∀ {n} → VTerm n → CTerm n
            recₓ : ∀ {n} → VTerm n → CTerm (suc n) → CTerm (suc n) → CTerm n

        
    mutual 
        wkv : ∀ {n} → VTerm n → VTerm (suc n)
        wkv (var x) = var (suc x) -- THE only interesting case
        wkv tt = tt
        wkv (pair x y) = pair (wkv x) (wkv y)
        wkv (thunk x) = thunk (wkc x)

        wkc : ∀ {n} → CTerm n → CTerm (suc n )
        wkc (ret x) = ret (wkv x)
        wkc (bind x y) = bind (wkc x) (wkc y)
        wkc (lam x) = lam (wkc x)
        wkc (app x y) = app (wkc x) (wkv y)
        wkc (force x) = force (wkv x)
        wkc (recₓ x y z) = recₓ (wkv x) (wkc y) (wkc z)

    mutual 
        -- replaces just var 0 with term t
        substv : ∀ {n} → VTerm (suc n) → VTerm n → VTerm n 
        substv (var zero) t = t
        substv (var (suc x)) t = var x
        -- ^^ the interesting cases
        substv tt t = tt
        substv (pair x y) t = pair (substv x t) (substv y t)
        substv (thunk x) t = thunk (substc x t)

        substc : ∀ {n} → CTerm (suc n) → VTerm n → CTerm n 
        substc (ret x) t = ret (substv x t)
        substc (bind x y) t = bind (substc x t) (substc y (wkv t)) 
        substc (lam x) t = lam (substc x (wkv t))
        substc (app x y) t = app (substc x t)  (substv y t)
        substc (force x) t = force (substv x t)
        substc (recₓ x y z) t = recₓ (substv x t) (substc y (wkv t)) (substc z (wkv t))


    data isTerminal : {n : ℕ} → CTerm n → Set where  
        ret-term : ∀ {n} → (V : VTerm n) → isTerminal (ret V)
        lam-term : ∀ {n} → (M : CTerm (suc n)) → isTerminal {n} (lam {n} M)

    stepc : ∀ {n} → (M : CTerm n) → isTerminal M ⊎ 
    stepc (ret x) = ret-term x
    stepc (bind x y) = {!   !}
    stepc (lam x) = lam-term x
    stepc (app x y) = {!   !}
    stepc (force x) = {!   !}
    stepc (recₓ x y z) = {!   !}
 