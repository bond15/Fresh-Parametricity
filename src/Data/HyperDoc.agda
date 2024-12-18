{-#OPTIONS --type-in-type #-}
module src.Data.HyperDoc where
    open import Cubical.Categories.Instances.Posets.Base
    open import Cubical.Categories.Instances.Sets
    open import Cubical.Categories.Category
    open Category
    open import Cubical.Data.Sigma
    open import Cubical.Relation.Binary.Preorder
    open import Cubical.Relation.Binary
    open BinaryRelation
    open import Cubical.Categories.Functor
    open Functor
    open import src.Data.FinSet
    open import Cubical.Categories.Presheaf.Base
    open import Cubical.Categories.Presheaf.Constructions


    -- refactor to use Cubical.Algebra.Lattice
    
    -- Heyting Algebra Object in Set

    set = SET _

    record HA (X : Set) : Set where 
        field 
            top bot : X
            and : X → X → X 
            or : X → X → X 
            
            and-assoc : (x y z : X) → and x (and y z) ≡ and (and x y) z
            and-comm : (x y : X) → and x y ≡ and y x
            and-idem : (x : X) → and x x ≡ x

            or-assoc : (x y z : X) → or x (or y z) ≡ or (or x y) z
            or-comm : (x y : X) → or x y ≡ or y x
            or-idem : (x : X) → or x x ≡ x

            abs₁ : (x y : X) → and x (or y x) ≡ x
            abs₂ : (x y : X) → x ≡ or (and x y) x

            and-unit : (x : X) → and x top ≡ x 
            or-unit : (x : X) → or x bot ≡ x

        -- ^^ lattice
            imp : X → X → X

            l1 : (x : X) → imp x x ≡ top
            l2 : (x y : X) → and x (imp x y) ≡ and x y
            l3 : (x y : X) → and y (imp x y) ≡ y 
            l4 : (x y z : X) → imp x (and y z) ≡ and (imp x y) (imp x z)

    open HA

    record  BIAlg (X : Set) : Set where 
        field 
            ha : HA X 
            𝕀 : X
            * -* : X → X → X 



    open import Cubical.Foundations.Powerset
    open import Cubical.Data.Maybe renaming (rec to mayberec)

    --_k≡_ : {A B : Set} → (f g : A → Maybe B) → Set 
    --_k≡_ f g = {! (x : A) → ?  !}


    mbind : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
    mbind nothing f = nothing
    mbind (just x) f = f x

    open import Cubical.Data.Unit
    open import Cubical.Data.Empty hiding(⊥)
    
    defined : {A : Set} → Maybe A → Set 
    defined nothing = ⊥*
    defined (just x) = Unit

    open PreorderStr
    
    -- orderd partial commutative monoid
    record isopcm (M : Set) : Set where
        field 
            E : ℙ M
            -- \o.
            ⊙ : M × M → Maybe M
            ordered : PreorderStr _ M

            opcm1 : (x y : M) → ⊙ (x , y) ≡ ⊙ (y , x) 
            opcm2 : (x y z : M) → mbind (⊙ (x , y)) (λ r → ⊙(r , z)) ≡ mbind (⊙ (y , z)) (λ r → ⊙(x , r))
            opcm3 : (x : M) → Σ M λ e → (e ∈ E) × (⊙ (x , e) ≡ just x) 
            opcm4 : (x : M) (e : Σ M (_∈ E))→ defined (⊙ (x , e .fst)) → ⊙ (x , e .fst) ≡ just x
            opcm5 : (x x' y y' : M) → ordered ._≤_ x x' → ordered ._≤_ y y' → defined (⊙ (x' , y')) → Σ (M × M) λ (r1 , r2) → (⊙ (x , y) ≡ just r1) × (⊙ (x' , y') ≡ just r2) × ordered ._≤_ r1 r2

  


    open isopcm     
    open import Cubical.Foundations.Prelude
    open import Cubical.HITs.PropositionalTruncation renaming (rec to prec)
    open import Cubical.Foundations.Structure
    open import Cubical.Data.Sum.Base renaming (rec to ⊎rec)
    open import Cubical.Functions.Logic
    open import Cubical.Foundations.HLevels


    -- easiest HA 
    propHA : HA (hProp _)
    propHA = record{ 
            top = ⊤
            ; bot = ⊥
            ; and = λ p q  → p ⊓ q 
            ; or = λ p q → p ⊔ q 
            ; and-assoc = λ p q r → ⊓-assoc p q r
            ; and-comm = λ p q → ⊓-comm p q
            ; and-idem = λ p →  ⊓-idem p
            ; or-assoc = λ p q r → ⊔-assoc p q r
            ; or-comm = λ p q → ⊔-comm p q
            ; or-idem = λ p → ⊔-idem p
            ; abs₁ = λ p q → ⇒∶ fst ⇐∶ λ m → m , ∣ _⊎_.inr m ∣₁
            ; abs₂ = λ p q → ⇒∶ (λ m → ∣ _⊎_.inr m ∣₁) ⇐∶ λ m → prec (p .snd) (⊎rec fst λ x → x) m
            ; and-unit = λ p → ⊓-identityʳ p
            ; or-unit = λ p → ⊔-identityʳ p
            ; imp = λ p q → p ⇒ q
            ; l1 = λ p → ⇒∶ (λ _ → tt*) ⇐∶ λ _ x → x
            ; l2 = λ p q → ⇒∶ (λ (m , f) → m , (f m)) ⇐∶ λ (m , n) → m , (λ _ → n)
            ; l3 = λ p q → ⇒∶ fst ⇐∶ λ m → m , (λ _ → m)
            ; l4 = λ p q r → ⇒-⊓-distrib p q r} 

    -- Any powerset is an HA
    PowerHA : {X : Set} → HA (ℙ X)
    PowerHA = record{ 
            top = λ x → ⊤
            ; bot = λ x → ⊥
            ; and = λ p q x → p x ⊓ q x
            ; or = λ p q x → p x ⊔ q x
            ; and-assoc = λ p q r → funExt λ x → ⊓-assoc (p x) (q x) (r x)
            ; and-comm = λ p q → funExt λ x → ⊓-comm (p x) (q x)
            ; and-idem = λ p → funExt λ x → ⊓-idem (p x)
            ; or-assoc = λ p q r → funExt λ x → ⊔-assoc (p x) (q x) (r x)
            ; or-comm = λ p q → funExt λ x → ⊔-comm (p x) (q x)
            ; or-idem = λ p → funExt λ x → ⊔-idem (p x)
            ; abs₁ = λ p q → funExt λ x → ⇒∶ fst ⇐∶ λ m → m , ∣ _⊎_.inr m ∣₁
            ; abs₂ = λ p q → funExt λ x → ⇒∶ (λ m → ∣ _⊎_.inr m ∣₁) ⇐∶ λ m → prec (p x .snd) (⊎rec fst λ x → x) m
            ; and-unit = λ p → funExt λ x → ⊓-identityʳ (p x)
            ; or-unit = λ p → funExt λ x → ⊔-identityʳ (p x)
            ; imp = λ p q x → p x ⇒ q x
            ; l1 = λ p → funExt λ x → ⇒∶ (λ _ → tt*) ⇐∶ λ _ x → x
            ; l2 = λ p q → funExt λ x → ⇒∶ (λ (m , f) → m , (f m)) ⇐∶ λ (m , n) → m , (λ _ → n)
            ; l3 = λ p q → funExt λ x → ⇒∶ fst ⇐∶ λ m → m , (λ _ → m)
            ; l4 = λ p q r → funExt λ x → ⇒-⊓-distrib (p x) (q x) (r x)} 

    defined' : {A : Set} → Maybe A → hProp _ 
    defined' nothing = ⊥
    defined' (just x) = ⊤

    OPCM : Set
    OPCM = Σ[ M ∈ Set ] isopcm M

    opcmToBiAlg : (O : OPCM) → BIAlg (ℙ (O .fst)) 
    opcmToBiAlg (M , opcm) = record { 
        ha = PowerHA {M} ; 
        𝕀 = opcm .E ; 
        * = λ p q → λ k → ∃[ (m , n) ∶ M × M ] just k ≡ₚ opcm .⊙ (m , n) ; -- no
        -* = λ p q → λ n → ∀[ m ∶ (Σ[ e ∈ M ] e ∈ p) ] mayberec ⊥ (λ r → (r ∈ q) , ∈-isProp q _) (opcm .⊙ (m .fst , n)) }
        -- defined' (opcm .⊙ (m .fst , n)) ⇒ mayberec ⊥ (λ x → (x ∈ q) , ∈-isProp q _) (opcm .⊙ (m .fst , n)) }


    record HAhom {X Y : Set} (f : X → Y)(hx : HA X)(hy : HA Y) : Set where  
    open import Cubical.Relation.Binary.Preorder renaming (isUnivalent to isUnivalentP)
    open import Agda.Builtin.Cubical.Equiv
    -- a poset on a heyting algebra
    -- page 199 Sheaves GL
    -- x ≤ y ⇔ and x y ≡ x
    open OrderEquivalent 
    haPoset : (X : ob set) → HA (X .fst) → ob (POSET _ _) 
    haPoset X h = P , uP where 
    
        ≤' : X .fst → X .fst → Set 
        ≤' x y = h .and x y ≡ x

        prf : IsPreorder ≤'
        prf = ispreorder g1 g2 g3 where 
        
            g1 : isPropValued ≤' 
            g1 x y p1 p2 = X .snd (h .and x y) x p1 p2

            g2 : isRefl ≤'
            g2 x = h .and-idem x

            g3 : isTrans ≤'
            g3 x y z p1 p2 = cong (λ d → h .and d z) (sym p1) ∙ sym (h .and-assoc x y z) ∙ cong (λ d → h .and x d) p2 ∙ p1
        
        P : Preorder _ _ 
        P = (X .fst) , (preorderstr ≤' prf)

        uP : isUnivalentP P
        uP = record { univ = λ x y → record { equiv-proof = λ oequiv-x-y → {!   !} } }
        
        --(X .fst , preorderstr (λ x y → h .and x y ≡ x) (ispreorder (λ a b x y  → X .snd (h .and a b) a x y) (λ a  → h .and-idem a) λ a b c x x₁  → {!   !})) , {!   !} 

    -- set based, first order
    record FOHyperDoc : Set where
        field 
            F : Functor (set ^op) (POSET _ _) 
            isHA : (X : ob (set ^op)) → HA (F .F-ob X .fst .fst)
            -- isHAhom : {X Y : ob ((SET _) ^op)} → (f : ((SET _) ^op) [ X , Y ]) → {! F .F-hom f   !}

    open import Cubical.Foundations.Isomorphism
    open FOHyperDoc
    record HyperDoc : Set where
        field 
            FO : FOHyperDoc
            H : ob set
            HisHA : HA (H .fst)
            Θ : (X : ob set) → Iso (FO .F .F-ob X .fst .fst) (set [ X , H ])


    open import Cubical.Data.Bool hiding (and-assoc ; and-comm ; and-idem ; or-assoc ; or-comm ; or-idem)

    poset : Set 
    poset = Σ[ P ∈  Preorder _ _ ] isUnivalentP P
    
    posetPower : (X : ob set) → poset 
    posetPower X = ((ℙ (X .fst)) , preorderstr _⊆_ (ispreorder ⊆-isProp ⊆-refl {!   !})) , record { univ = λ x y → record { equiv-proof = {! ⊆-extensionalityEquiv  !} } }
    -- {! ⊆-extensionalityEquiv  !}

    open BIAlg
    open IsPreorder 
    
    F' : (𝓑 : ob set) → BIAlg (𝓑 .fst) → Functor (set ^op)  (POSET _ _) 
    F' 𝓑 bi .F-ob X = P , uP where

        𝓑poset : poset 
        𝓑poset = haPoset 𝓑 (bi .ha)

        ≤𝓑 : 𝓑 .fst → 𝓑 .fst → Set 
        ≤𝓑 = 𝓑poset .fst .snd .PreorderStr._≤_ 

        -- pointwise
        -- f≤g ⇔ ∀x∈X, f(x)≤g(x) 
        ≤' : (X .fst → 𝓑 .fst) → (X .fst → 𝓑 .fst) → Type
        ≤' f g = (x : X .fst) → ≤𝓑 (f x) (g x)

        ispre : IsPreorder ≤' 
        ispre = ispreorder g1 g2 g3 where 
            g1 : isPropValued ≤'
            g1 = λ a b r1 r2  → funExt λ x → 𝓑poset .fst .snd .isPreorder .is-prop-valued (a x) (b x) (r1 x) (r2 x)

            g2 : isRefl ≤'
            g2 = λ a r → 𝓑poset .fst .snd .isPreorder .is-refl (a r)

            g3 : isTrans ≤' 
            g3 = λ f g h r1 r2 x → 𝓑poset .fst .snd .isPreorder .is-trans (f x) (g x) (h x) (r1 x) (r2 x)

        P : Preorder _ _ 
        P = (X .fst → 𝓑 .fst) , preorderstr ≤' ispre

        uP : isUnivalentP P 
        uP = record { univ = λ x y → record { equiv-proof = λ y₁ → {!   !} } }
        
        --((X .fst → 𝓑 .fst) , preorderstr (λ f g → (x : X .fst) → {! f x  !}) {!   !}) , {!   !}
    F' 𝓑 bi .F-hom = {!   !}
    F' 𝓑 bi .F-id = {!   !}
    F' 𝓑 bi .F-seq = {!   !}

    -- why is this very similar to how power set is a heyting alg?
    hrm : (𝓑 : ob set) → BIAlg (𝓑 .fst) → FOHyperDoc
    hrm 𝓑 bi = record { 
                F = F' 𝓑 bi ; 
                isHA = λ X → 
                    record{ 
                        top = λ x → bi .ha .top
                        ; bot = λ x → bi .ha .bot
                        ; and = λ f g x → bi .ha .and (f x) (g x)
                        ; or = λ f g x → bi .ha .or (f x) (g x)
                        ; and-assoc = λ f g h → funExt λ x → bi .ha .and-assoc (f x) (g x) (h x)
                        ; and-comm = λ f g → funExt λ x → bi .ha .and-comm (f x) (g x)
                        ; and-idem = λ f → funExt λ x → bi .ha .and-idem (f x)
                        ; or-assoc = λ f g h → funExt λ x → bi .ha .or-assoc (f x) (g x) (h x)
                        ; or-comm = λ f g → funExt λ x → bi .ha .or-comm (f x) (g x)
                        ; or-idem = λ f → funExt λ x → bi .ha .or-idem (f x)
                        ; abs₁ = λ f g → funExt λ x → bi .ha .abs₁ (f x) (g x)
                        ; abs₂ = λ f g → funExt λ x → bi .ha .abs₂ (f x) (g x)
                        ; and-unit = λ f → funExt λ x → bi .ha .and-unit (f x)
                        ; or-unit = λ f → funExt λ x → bi .ha .or-unit (f x)
                        ; imp = λ f g x → bi .ha .imp (f x) (g x)
                        ; l1 = λ f → funExt λ x → bi .ha .l1 (f x)
                        ; l2 = λ f g → funExt λ x → bi .ha .l2 (f x) (g x)
                        ; l3 = λ f g → funExt λ x → bi .ha .l3 (f x) (g x)
                        ; l4 = λ f g h → funExt λ x → bi .ha .l4 (f x) (g x) (h x)} }

    tada : OPCM → HyperDoc 
    tada O = record { 
        FO = hrm 𝓑 bi ; 
        H = 𝓑 ; 
        HisHA = bi .ha ; 
        Θ = λ X → idIso } where 
        
            𝓑 : ob set 
            𝓑 = ℙ (O .fst) , isSetℙ

            bi : BIAlg (𝓑 .fst) 
            bi = opcmToBiAlg O




   -- pre : Preorder _ _ 
   -- pre = {!   !} , preorderstr {!   !} (ispreorder {!   !} {!   !} {!   !})

   -- P : ob (POSET _ _)
   -- P = pre , record { univ = {!   !} }

   -- Poset : Set 
    --Poset = Σ[ P ∈ Preorder _ _ ] isUnivalent P
  --  Poset : Set
   -- Poset = Σ[ P ∈ Preorder ℓ ℓ' ] isUnivalent P

   --foo : Prop
   --foo = ?
    open Monoidal

   -- FS = FinSetMono
    𝓒 : Category _ _ 
    𝓒 = PresheafCategory (FS ^op) _

  

    open import src.Data.PresheafCCC
    open import Cubical.Categories.Limits.Terminal
    open import Cubical.Categories.Limits.BinProduct
    open BinProduct
    open import Cubical.Categories.NaturalTransformation
    open NatTrans
    open import Cubical.Foundations.Prelude
    
    term : ob 𝓒 
    term = ⊤𝓟 {C = FS ^op}{_} .fst

    _×𝓒_ : ob 𝓒 → ob 𝓒 → ob 𝓒  
    _×𝓒_ A B = ×𝓟 {C = FS ^op} {_} A B .binProdOb

    postulate Val : Set
    
    ph : ob 𝓒 
    ph .F-ob n = (Σ[ m ∈ ob FS ] Σ[ f ∈ FS [ m , n ] ] ((m .fst) → Val)) , {!   !}
    ph .F-hom {x}{y} f (x' , (x'x , xm)) =  x' , x'x ⋆⟨ FS  ⟩ f , xm
    ph .F-id = {!   !}
    ph .F-seq = {!   !}

    Δ : (X : ob 𝓒) → 𝓒 [ X , X ×𝓒 X ] 
    Δ X .N-ob n Xn = Xn , Xn
    Δ X .N-hom f = refl

    ×f : {A B C D : ob 𝓒} → 𝓒 [ A , C ] → 𝓒 [ B , D ] → 𝓒 [ A ×𝓒 B , C ×𝓒 D ]
    ×f f g .N-ob x (Ax , Bx)= (f .N-ob x  Ax) , (g .N-ob x Bx)
    ×f f g .N-hom = {!   !}

    -- Lemma 4.18 Prop𝕎 is a complete heyting algebra in S_ℓ
    Prop𝕎 : ob 𝓒 
    Prop𝕎 = {!   !}

    record InternalMonoid (M : ob 𝓒) : Set where 
        field 
            𝕀 : 𝓒 [ term , M ] -- \bI
            ⊗ : 𝓒 [ M ×𝓒 M , M ]
            idl : (e : 𝓒 [ term , M ]) → 𝕀 ≡ Δ term ⋆⟨ 𝓒 ⟩ ×f e 𝕀 ⋆⟨ 𝓒 ⟩ ⊗
            -- idr 
            --assoc 
            -- comm

    record InternalLattice (L : ob 𝓒) : Set where 
        field 
            top bot : 𝓒 [ term , L ]
            meet join : 𝓒 [ L ×𝓒 L , L ]
            -- laws
            -- assoc, commutative, idempotent, absorption, left right identity

    record InternalHeytingAlg (H : ob 𝓒) : Set where 
        field 
            hlattice : InternalLattice H
            implies : 𝓒 [ H ×𝓒 H , H ]
            -- laws 1.8.3 of Sheaves in Geometry and Logic

    record InternalBIAlg (B : ob 𝓒) : Set where 
        field 
            haB : InternalHeytingAlg B
            -- ? 
            sepB : InternalMonoid B 
            -- laws and interaction with other structure?
            
    -- page 199 Sheaves in Geo and Logic
    record InternalPoset (P : ob 𝓒) : Set where 
        field 
            plattice : InternalLattice P 
            -- ≤L equalizer of meet and π₁ 
            -- x ≤ y iff x meet y = x
            
    open InternalMonoid
    ! : { X : ob FS} → FS [ Ø , X ]
    ! = (λ()) , λ()

    {-
        -- set based, first order
    record FOHyperDoc : Set where
        field 
            F : Functor (set ^op) (POSET _ _) 
            isHA : (X : ob (set ^op)) → HA (F .F-ob X .fst .fst)
            -- isHAhom : {X Y : ob ((SET _) ^op)} → (f : ((SET _) ^op) [ X , Y ]) → {! F .F-hom f   !}

    open import Cubical.Foundations.Isomorphism
    open FOHyperDoc
    record HyperDoc : Set where
        field 
            FO : FOHyperDoc
            H : ob set
            HisHA : HA (H .fst)
            Θ : (X : ob set) → Iso (FO .F .F-ob X .fst .fst) (set [ X , H ]) 
    -}

    -- 𝓒 based
    record FOHyperDoc' : Set where
        field 
            F𝓒 : Functor (𝓒 ^op) (POSET _ _) 
            isHA : (X : ob (𝓒 ^op)) → HA (F𝓒 .F-ob X .fst .fst) 

    open FOHyperDoc'
    record HyperDoc' : Set where
        field 
            FO : FOHyperDoc'
            H : ob 𝓒
            HisHA : InternalHeytingAlg H
            Θ : (X : ob 𝓒) → Iso (FO .F𝓒 .F-ob X .fst .fst) (𝓒 [ X , H ]) 


    phMon : InternalMonoid ph 
    phMon .𝕀 = natTrans (λ{x tt* → Ø , !{_} , λ()}) λ f → funExt λ{ tt* → {!  !}}
    phMon .⊗ = natTrans (λ{x (f , g) → {!   !}}) {!   !}
    phMon .idl = {!   !}



 
    
    open import Cubical.Categories.Instances.Functors
    

    asPoset : Category _ _ → Set 
    asPoset = {!   !}

    {- 
        A power object of an object A in a topos E is 
        the exponential object Ω^A
        Power(A) = Ω^A

        Subobject classifier in a presheaf topos maps an object to its set of sieves

        -- Theorem 4.5 Mahany Note
           Elementary Topos Theory and Intuitionistic Logic
        For any object X in a topos E,
         Power(X) is an internal Heyting Algebra
         ∀(Y : ob E), E[Y , P(X)] is an external Heyting Algebra
    -}


    open import Cubical.Categories.Site.Sieve

    SetSieve : ob set → Set
    SetSieve = Sieve set _

    ex : SetSieve (Bool , isSetBool) 
    ex = record
        { passes = λ {X} f∷X→Bool → {!   !} ; 
        isPropPasses = {!   !} ; 
        closedUnderPrecomposition = {!   !} }

    open import Cubical.Data.FinSet
    
    FStoSet : ob FS → ob set
    FStoSet (X , xfin) = X , isFinSet→isSet xfin

    -- page 38 Sheaves in GL
    Ω : ob 𝓒 
    Ω . F-ob X = SetSieve (FStoSet X) , {!   !}
    Ω . F-hom = {!   !}
    Ω . F-id  = {!   !}
    Ω . F-seq = {!   !}

    Power𝓒 : ob 𝓒 → ob 𝓒 
    Power𝓒 X = ExpOb X Ω

    PowerHA𝓒 : (X : ob 𝓒) → InternalHeytingAlg (Power𝓒 X)
    PowerHA𝓒 X = 
        record { 
            hlattice = 
                record { 
                    top = t ;
                        --natTrans (λ{x tt* → natTrans (λ{ y (f∷X→Y , Xy) → {! f∷X→Y .lower .fst  !}}) {!   !}}) {!   !} ; 
                    bot = {!   !} ; 
                    meet = {!   !} ; 
                    join = {!   !} } ; 
            implies = {!   !} } where 
            
            t : 𝓒 [ term , Power𝓒 X ] 
            t = natTrans nob {!   !} where

                nob : N-ob-Type term (Power𝓒 X) 
                nob y tt* = natTrans (λ z (f∷z→y , Xz) → 
                    -- setSieve (FStoSet z)
                    record{ 
                        passes = {!   !} ; 
                        isPropPasses = {!   !} ; 
                        closedUnderPrecomposition = {!   !} }) {!   !}


    -- ?
    InternalPS→PS : (X : ob 𝓒) → InternalPoset X → poset
    InternalPS→PS X Xips = ({!   !} , {!   !}) , {!   !}
    -- ph is an internal OPCM
    𝓒HyperDoc : (ph : ob 𝓒) → HyperDoc' 
    𝓒HyperDoc ph = record { 
        FO = 𝓒FO ; 
        H = H' ; 
        HisHA = PowerHA𝓒 ph ; 
        Θ = {!   !} } where 

            H' : ob 𝓒
            H' = Power𝓒 ph

            FF : Functor (𝓒 ^op) (POSET _ _)
            -- hmm?
            FF . F-ob X = InternalPS→PS (ExpOb X H') {!   !} 
            FF . F-hom = {!   !}
            FF . F-id = {!   !}
            FF . F-seq = {!   !}

            𝓒FO : FOHyperDoc' 
            𝓒FO = record { F𝓒 = FF ; isHA = {!   !} }


    {-
    Furthermore, in a topos, the power object 𝒫(A) 
    is an internal Heyting algebra that 
    corresponds to the external Heyting algebra Sub(A). 
    -}

    PropCat : Category _ _ 
    PropCat = record
        { ob = hProp _
        ; Hom[_,_] = λ φ ψ → Cubical.Functions.Logic._⇒_ φ ψ .fst
        ; id = λ x → x
        ; _⋆_ = λ f g x → g (f x)
        ; ⋆IdL = λ f  → refl
        ; ⋆IdR = λ f → refl
        ; ⋆Assoc = λ f g h → refl
        ; isSetHom = λ {φ} {ψ} → isProp→isSet (Cubical.Functions.Logic._⇒_ φ ψ .snd )}
    
    
    {-Prop𝕎 : ob 𝓒 
    Prop𝕎 .F-ob n = (asPoset (FUNCTOR  {!   !} {!   !})) , {!   !}
    Prop𝕎 .F-hom = {!   !}
    Prop𝕎 .F-id = {!   !}
    Prop𝕎 .F-seq = {!   !}

    Prop𝕎-isInternalPoset : InternalPoset Prop𝕎
    Prop𝕎-isInternalPoset = {!   !}

    𝓑 : ob 𝓒 
    𝓑 = {!   !}
  -}