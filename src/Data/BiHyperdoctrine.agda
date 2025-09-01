
    record isBiAlg (X : Set) : Set where 
        field 
            isHA : isHeytingAlg X
            pre : PreorderStr _ X
            
        module p = PreorderStr pre
        _≤p_ = p._≤_

        field
            𝓘 : X 
            _*_ _-*_ : X → X → X 
            mono : {x x' y y' : X} → x ≤p x' → y ≤p y' → (x * y) ≤p (x' * y') 
            *cmon : IsCommMonoid 𝓘 _*_
            *adj-* : {x y z : X} → ((x * y) ≤p z → x ≤p (y -* z)) × (x ≤p (y -* z) → (x * y) ≤p z)
            
            

    -- PCM 
    open import Cubical.Data.Maybe
    --isPCM : Set → Set 
    --isPCM M = Σ[ _⊚_ ∈  (M → M → Maybe M) ]  Σ[ 𝟙 ∈ M ] {!   !}

    open import Cubical.Data.Empty renaming (⊥ to Empty)

    isDef : {X : Set} → Maybe X → hProp _ 
    isDef nothing = ⊥
    isDef (just _) = ⊤

    extract : {X : Set} → (m  : Maybe X) → {isDef m .fst} → X 
    extract {X} (just x) = x 
    
    -- kleene equality (not needed ... )
    {-
    Cover : Maybe A → Maybe A → Type ℓ
    Cover nothing  nothing   = Lift Unit
    Cover nothing  (just _)  = Lift ⊥
    Cover (just _) nothing   = Lift ⊥
    Cover (just a) (just a') = a ≡ a'
  Cover≡Path : ∀ c c' → Cover c c' ≡ (c ≡ c')
  Cover≡Path c c' = isoToPath
    (iso (decode c c') (encode c c') (decodeEncode c c') (encodeDecode c c'))
    -}
    --_≈_ : {A : Set} (x y : Maybe A) → {isDef x .fst}→ {isDef y .fst}  → Set 
    --_≈_ (just x) (just y) = x ≡ y
   -- record _≈_ {A : Set} (x y : Maybe A) : Set where 
   --     constructor ke 
   --     field 
    --        ≈ : {isDef x .fst} → {isDef y .fst} → x ≡ y
    --_≈_ : {A : hSet _} (x y : Maybe (A .fst)) →  Set
   -- _≈_ {A} x y = isDef x .fst × isDef y .fst × (x ≡ y)
        -- {isDef x .fst} → {isDef y .fst} → x ≡ y


   -- ≈isProp : {A : hSet _} (x y : Maybe (A .fst)) → isProp (_≈_{A} x y )
   -- ≈isProp {A} x y  = isProp× (isDef x .snd) (isProp× (isDef y .snd) (isOfHLevelMaybe 0 (A .snd) x y))
        --isPropImplicitΠ λ _ → isPropImplicitΠ λ _ → isOfHLevelMaybe 0 (A .snd) x y
    
    _>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B 
    nothing >>= f = nothing
    just x >>= f = f x


    record PCM : Set where 
        field 
            M : hSet _ 
            _⊚_ : fst M → fst M → Maybe (fst M) 
            𝟙 : fst M 
            lunit : (x : fst M) → (𝟙 ⊚ x) ≡ just x
            runit : (x : fst M) → (x ⊚ 𝟙) ≡ just x
            comm : (x y : fst M) → (x ⊚ y) ≡ (y ⊚ x)
            assoc : (x y z : fst M) → ((y ⊚ z) >>= (x ⊚_)) ≡ ((x ⊚ y) >>= (_⊚ z))

        _#_ : (a b : fst M) → hProp _ 
        a # b = isDef (a ⊚ b)
        

    module _ (pcm : PCM) where 
        open PCM pcm

        _≤ext_ : fst M → fst M → hProp _
        _≤ext_ x y = ∃[ z ∶ fst M ] (((x ⊚ z) ≡ just y) , isOfHLevelMaybe 0 (M .snd) (x ⊚ z) (just y) )
        -- ≈isProp {M}(x ⊚ _) (just y)

        PrePcm : Preorder _ _ 
        PrePcm = fst M , 
            (preorderstr 
                (λ x y → (x ≤ext y) .fst) 
            (ispreorder 
                (λ x y → ( x ≤ext y) .snd) 
                (λ x → ∣ 𝟙 , runit x ∣₁)
                --∣ ? , {!   !} , ({!   !} , {!   !}) ∣₁)  -- (λ{d1}{d2} → runit x {d1}{d2}) ∣₁) 
                -- it is k ⊚ j then use associativity and the fact that things are defined to finish the proof
                λ x y z x≤y y≤z → rec2 (snd (x ≤ext z)) (λ {(k , prfk)(j , prfj) → ∣ {! k ⊚ j  !} , {!   !} ∣₁}) x≤y y≤z))

        HaPcm : HeytingAlg
        HaPcm = upSetHA PrePcm
        open isBiAlg

        typeOf : {X : Set} → (x : X) → Set 
        typeOf {X} _ = X
        -- subset relation
        upPre : PreorderStr ℓ-zero (typ HaPcm) 
        upPre = 
            preorderstr 
                (λ x y → (fst x) ⊆ (fst y)) 
            (ispreorder 
                (λ x y → ⊆-isProp (fst x) (fst y))
                (λ x → ⊆-refl (fst x)) 
                λ x y z x⊆y y⊆z e p → y⊆z e (x⊆y e p))

        Day : typ HaPcm → typ HaPcm → typ HaPcm
        Day (A , prfA)(B , prfB) = day , prfDay where 
            day : ℙ (fst M)
            day r∶M = 
                ∃[ (n ,  m)  ∶ (fst M × fst M) ] 
                    just r∶M ≡ₚ (n ⊚ m) ⊓ 
                    (n ∈ A , ∈-isProp A n) ⊓ 
                    (m ∈ B , ∈-isProp B m)   

            prfDay : (x y : fst M) → x ∈ day → snd PrePcm ._≤_ x y → y ∈ day
            prfDay x y x∈Day x≤y = Hmap2 goal x∈Day  x≤y where 

                goal : Σ (Σ (fst M) (λ _ → fst M))
                    (λ x₁ →
                    Σ ∥ just x ≡ (fst x₁ ⊚ snd x₁) ∥₁
                    (λ _ → Σ (fst (A (fst x₁))) (λ _ → fst (B (snd x₁))))) →
                    Σ (fst M) (λ x₁ → (x ⊚ x₁) ≡ just y) →
                    Σ (Σ (fst M) (λ _ → fst M))
                    (λ x₁ →
                    Σ ∥ just y ≡ (fst x₁ ⊚ snd x₁) ∥₁
                    (λ _ → Σ (fst (A (fst x₁))) (λ _ → fst (B (snd x₁))))) 
                goal ((z , w) , x≡z⊚w , z∈A , w∈B) (q , x⊚q≡y ) = goal' where 

                    x≡z⊚w' : just x ≡ (z ⊚ w)
                    x≡z⊚w' = Hrec (isOfHLevelMaybe 0 (M .snd) (just x) (z ⊚ w))  (λ x → x) x≡z⊚w

                    _ = ((z ⊚ w) >>= (_⊚ q)) ≡ just y

                    goal' : Σ (Σ (fst M) (λ _ → fst M))
                            (λ x₁ →
                            Σ ∥ just y ≡ (fst x₁ ⊚ snd x₁) ∥₁
                            (λ _ → Σ (fst (A (fst x₁))) (λ _ → fst (B (snd x₁)))))
                    goal' = (x , q) , ({!   !} , ({!   !} , {!   !}))

        -- the components of the Day convolution stay the same exept we "upgrade" the sets the arguments live in
        dayMono : {X X' Y Y' : typ HaPcm} → (upPre ≤ X) X' → (upPre ≤ Y) Y' → (upPre ≤ Day X Y) (Day X' Y')
        dayMono X≤X' Y≤Y' m∶M m∈Dayxy = Hmap (λ { ((z , w) , m≡z⊚w , z∈X , w∈Y) → (z , w) , (m≡z⊚w , (X≤X' z z∈X , Y≤Y' w w∈Y))}) m∈Dayxy


        Sep : typ HaPcm → typ HaPcm → typ HaPcm
        Sep (A , prfA)(B , prfB) = {!   !} , {!   !} where 
            sep : ℙ (fst M)
            sep m = ∀[ a ∶ fst M ] {!  m ⊚ a !} ∈ B , ∈-isProp B {!   !}

        
        BiPcm : isBiAlg (typ HaPcm)
        BiPcm .isHA = str HaPcm
        BiPcm .pre = upPre
        -- the full set of M, represented as a map into prop
        BiPcm .𝓘 = (λ x → ⊤) , λ x y x∈M x≤y → tt*
        -- day conv
        BiPcm ._*_  = Day
        BiPcm ._-*_ = Sep
        BiPcm .mono {X}{X'}{Y}{Y'} = dayMono {X}{X'}{Y}{Y'}
        BiPcm .*cmon = {!   !}
        BiPcm .*adj-* = {!   !}          


    module examplePCM (X : Set) where 
        open import Cubical.Data.Nat 
        open import Cubical.Data.Bool
        open import Cubical.Data.Fin
        open PCM
        open import Cubical.Relation.Nullary
        open import Cubical.Relation.Nullary.DecidablePropositions
        open import Cubical.Data.List

        -- Dependently Typed Programming with Finite Sets
  

        -- finite map
        finmap : {n : ℕ} → Set 
        finmap {n} = Σ[ n ∈ ℕ ] Fin n → X

        pcm : PCM
        pcm .M = {!   !}
        pcm ._⊚_ f g = {!   !}
        pcm .𝟙 = {!   !}
        pcm .lunit = {!   !}
        pcm .runit = {!   !}
        pcm .comm = {!   !}
        pcm .assoc = {!   !}