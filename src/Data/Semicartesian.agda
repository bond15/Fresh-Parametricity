{-# OPTIONS --allow-unsolved-metas  --lossy-unification #-}

module src.Data.Semicartesian where
    open import Cubical.Foundations.Prelude

    open import Cubical.Categories.Category 
    open import Cubical.Categories.Functor
    open import Cubical.Categories.Monoidal.Base 
    open import Cubical.Categories.Limits.Terminal
    
    open Category 

    record SemicartesianStrictMonCat ℓ ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where 
        open StrictMonCategory hiding (C ; _⊗_ ; sms ; _⊗ₕ_ )
        open StrictMonStr hiding (_⊗_ ; _⊗ₕ_ )
        open TensorStr 
        field 
            C : Category ℓ ℓ' 
            sms : StrictMonStr C 
            term : Terminal C 
            semi : sms .unit ≡ fst term
        
        proj₁ : {X Y : ob C} → C [ _⊗_ (sms .tenstr) X Y  ,  X ]
        proj₁ {X}{Y} = pre ⋆⟨ C ⟩ post where 
            pre : C [ _⊗_ (sms .tenstr) X Y  , _⊗_ (sms .tenstr) X (fst term)  ]
            pre = _⊗ₕ_ (sms .tenstr) (C .id) (terminalArrow C term Y)

            lemma : C [ _⊗_ (sms .tenstr) X (fst term)  , X ] ≡ C [ X , X ] 
            lemma = C [ _⊗_ (sms .tenstr) X (fst term)  , X ]  ≡⟨ cong (λ x → C [ (_⊗_ (sms .tenstr)) X x , X ] ) (sym (semi)) ⟩ 
                    C [ _⊗_ (sms .tenstr) X (sms .unit) , X ]  ≡⟨ cong (λ x → C [ x , X ]) (sms .idr X) ⟩ 
                    C [ X , X ] ∎
            
            post : C [ _⊗_ (sms .tenstr) X (fst term)  , X ] 
            post = transport (sym lemma) (C .id )

        proj₂ : {X Y : ob C} → C [ _⊗_ (sms .tenstr) X Y  ,  Y ]
        proj₂ {X}{Y} = pre ⋆⟨ C ⟩ post where 
            pre : C [ _⊗_ (sms .tenstr) X Y  , _⊗_ (sms .tenstr) (fst term) Y  ]
            pre = _⊗ₕ_ (sms .tenstr) (terminalArrow C term X) (C .id)

            lemma : C [ _⊗_ (sms .tenstr) (fst term)  Y , Y ] ≡ C [ Y , Y ] 
            lemma = C [ _⊗_ (sms .tenstr) (fst term)  Y , Y ]  ≡⟨ cong (λ x → C [ (_⊗_ (sms .tenstr)) x Y , Y ] ) (sym (semi)) ⟩ 
                    C [ _⊗_ (sms .tenstr) (sms .unit) Y , Y ]  ≡⟨ cong (λ x → C [ x , Y ]) (sms .idl Y) ⟩ 
                    C [ Y , Y ] ∎
            
            post : C [ _⊗_ (sms .tenstr) (fst term) Y  , Y ] 
            post = transport (sym lemma) (C .id )

    -- get a monoidal structure on the opposite category
    _^opMon : {ℓ ℓ' : Level} → StrictMonCategory ℓ ℓ' → StrictMonCategory ℓ ℓ'
    _^opMon SMC = record { 
                    C = SMC .C ^op ; 
                    sms = record { 
                            tenstr = record { 
                                        ─⊗─ = SMC . tenstr .─⊗─ ^opF ; 
                                        unit = SMC .tenstr .unit 
                                    } ; 
                            assoc = SMC .assoc ; 
                            idl = SMC .idl ; 
                            idr = SMC .idr 
                        } 
                }
        where 
            open StrictMonCategory
            open StrictMonStr 
            open TensorStr

    -- you can get a monoidal structure on the opposite category
    -- but not a semicartesian monoidal structure
    module bar {ℓ ℓ'}(SSMC : SemicartesianStrictMonCat ℓ ℓ') where 
        open SemicartesianStrictMonCat
        open StrictMonCategory

        opp : SemicartesianStrictMonCat ℓ ℓ' 
        opp = record { 
            C = SSMC .C ^op ; 
            sms = ( (record { C = SSMC .C ; sms = SSMC .sms }) ^opMon ) .sms ; 
            term = fst (SSMC .term) , λ y → {!   !} , {!   !} ; 
            -- it is not initial
            semi = SSMC .semi }
        
        
