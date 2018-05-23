module Int where
  open import Nat
  open import Data.Integer as ℤ public
  open import Data.Integer.Properties as ℤp public
  open import Equality
  open import Data.Empty
  open import Relation.Nullary
  open import Relation.Nullary.Decidable

  cong-≤ℤ-l :
    {a b c : ℤ} ->
    (a=b : a ≡ b) ->
    (a≤c : a ℤ.≤ c) ->
    b ℤ.≤ c
  cong-≤ℤ-l refl a≤c = a≤c

  cong-≤ℤ-r :
    {a b c : ℤ} ->
    (a=b : a ≡ b) ->
    (c≤a : c ℤ.≤ a) ->
    c ℤ.≤ b
  cong-≤ℤ-r refl a≤c = a≤c

  -+≤+ :
    (a b : ℕ) ->
    - (+ a) ℤ.≤ + b
  -+≤+ zero b =
    +≤+ z≤n
  -+≤+ (Nat.suc a) b =
    -≤+

  a≤b=>-b≤-a :
    {a b : ℤ} ->
    (a≤b : a ℤ.≤ b) ->
    - b ℤ.≤ - a
  a≤b=>-b≤-a { -[1+_] a} {+_ zero} -≤+ =
    +≤+ z≤n
  a≤b=>-b≤-a { -[1+_] a} {+_ (Nat.suc b)} -≤+ =
    -≤+
  a≤b=>-b≤-a {(-[1+ a ])} {(-[1+ b ])} (-≤- n≤m) =
    +≤+ (s≤s n≤m)
  a≤b=>-b≤-a {+_ zero} {+_ zero} (+≤+ m≤n) =
    +≤+ z≤n
  a≤b=>-b≤-a {+_ zero} {+_ (Nat.suc b)} (+≤+ m≤n) =
    -≤+
  a≤b=>-b≤-a {+_ (Nat.suc a)} {+_ zero} (+≤+ ())
  a≤b=>-b≤-a {+_ (Nat.suc a)} {+_ (Nat.suc b)} (+≤+ (s≤s m≤n)) =
    -≤- m≤n

  ≤-compa-+ :
    (a b c : ℤ) ->
    a ℤ.≤ b ->
    (a ℤ.+ c) ℤ.≤ (b ℤ.+ c)
  ≤-compa-+ (+_ n) (+_ n₁) (+_ n₂) (+≤+ m≤n) =
    +≤+ (a≤b=>c≤d=>a+c≤b+d m≤n Nat.≤-refl)
  ≤-compa-+ (+_ n) (+_ n₁) (-[1+_] n₂) a≤b with n Nat.≤? Nat.suc n₂
  ≤-compa-+ (+_ n) (+_ n₁) (-[1+_] n₂) a≤b | yes p with n₁ Nat.≤? Nat.suc n₂
  ≤-compa-+ (+_ n) (+_ n₁) (-[1+_] n₂) (+≤+ a≤b) | yes p | yes p₁ =
    cong-≤ℤ-l
      { - (+ (Nat.suc n₂ ∸ n))}
      (sym
        (begin
          n ⊖ Nat.suc n₂
            ≡⟨ ⊖-swap n (Nat.suc n₂) ⟩
          - (Nat.suc n₂ ⊖ n)
            ≡⟨ cong
                 (λ x -> - x)
                 (⊖-≥ p) ⟩
          - (+ (Nat.suc n₂ ∸ n)) ∎))
      (cong-≤ℤ-r
        { - (+ (Nat.suc n₂ ∸ n₁))}
        (sym
          (begin
            n₁ ⊖ Nat.suc n₂
              ≡⟨ ⊖-swap n₁ (Nat.suc n₂) ⟩
            - (Nat.suc n₂ ⊖ n₁)
              ≡⟨ cong
                   (λ x -> - x)
                   (⊖-≥ p₁) ⟩
            - (+ (Nat.suc n₂ ∸ n₁)) ∎))
        (a≤b=>-b≤-a
          { (+ (Nat.suc n₂ ∸ n₁))}
          { (+ (Nat.suc n₂ ∸ n))}
          (+≤+ (a≤b=>c-b≤c-a (Nat.suc n₂) a≤b))))
  ≤-compa-+ (+_ n) (+_ n₁) (-[1+_] n₂) a≤b | yes p | no ¬p =
    cong-≤ℤ-l
      { - (+ (Nat.suc n₂ ∸ n))}
      (sym
        (
        (begin
          n ⊖ Nat.suc n₂
            ≡⟨ ⊖-swap n (Nat.suc n₂) ⟩
          - (Nat.suc n₂ ⊖ n)
            ≡⟨ cong
                 (λ x -> - x)
                 (⊖-≥ p) ⟩
          - (+ (Nat.suc n₂ ∸ n)) ∎)))
      (cong-≤ℤ-r
        { + (n₁ ∸ Nat.suc n₂)}
        (sym
          (⊖-≥
            {n₁}
            {Nat.suc n₂}
            (a<b=>a≤b
              {Nat.suc n₂}
              {n₁}
              (¬a≤b=>b<a {n₁} {Nat.suc n₂} ¬p))))
        (-+≤+ (Nat.suc n₂ ∸ n) (n₁ ∸ Nat.suc n₂)))
  ≤-compa-+ (+_ n) (+_ n₁) (-[1+_] n₂) a≤b | no ¬p with n₁ Nat.≤? Nat.suc n₂
  ≤-compa-+ (+_ n) (+_ n₁) (-[1+_] n₂) (+≤+ m≤n) | no ¬p | yes p =
    ⊥-elim
      (¬p
        (Nat.≤-trans m≤n p))
  ≤-compa-+ (+_ n) (+_ n₁) (-[1+_] n₂) (+≤+ a≤b) | no ¬p | no ¬p₁ =
    cong-≤ℤ-l
      {+ (n ∸ Nat.suc n₂)}
      (sym
        (⊖-≥
          {n}
          {Nat.suc n₂}
          (a<b=>a≤b
            {Nat.suc n₂}
            {n}
            (¬a≤b=>b<a {n} {Nat.suc n₂} ¬p))))
      (cong-≤ℤ-r
        {+ (n₁ ∸ Nat.suc n₂)}
        (sym
          (⊖-≥
            {n₁}
            {Nat.suc n₂}
            (a<b=>a≤b
              {Nat.suc n₂}
              {n₁}
              (¬a≤b=>b<a {n₁} {Nat.suc n₂} ¬p₁))))
        (+≤+ (a≤b=>a-c≤b-c (Nat.suc n₂) a≤b )))
  ≤-compa-+ (+_ n) (-[1+_] n₁) c ()
  ≤-compa-+ (-[1+_] n) (+_ n₁) (+_ n₂) a≤b with Nat.suc n Nat.≤? n₂
  ≤-compa-+ (-[1+_] n) (+_ n₁) (+_ n₂) a≤b | yes p =
    cong-≤ℤ-l
      {+ (n₂ ∸ Nat.suc n)}
      (sym
        (⊖-≥
          {n₂}
          {Nat.suc n}
          p))
      (+≤+
        (Nat.≤-trans
          {j = n₂}
          (a-b≤a n₂ (Nat.suc n))
          (cong-≤-r
            {n₂ Nat.+ n₁}
            (Nat.+-comm n₂ n₁)
            (a≤a+b {n₂} {n₁}))))
  ≤-compa-+ (-[1+_] n) (+_ n₁) (+_ n₂) a≤b | no ¬p =
    cong-≤ℤ-l
      { - (+ (Nat.suc n ∸ n₂))}
      (sym
        (begin
          n₂ ⊖ Nat.suc n
            ≡⟨ ⊖-swap n₂ (Nat.suc n) ⟩
          - (Nat.suc n ⊖ n₂)
            ≡⟨ cong
                 (λ x -> - x)
                 (⊖-≥
                   {Nat.suc n}
                   {n₂}
                   (a<b=>a≤b
                     {n₂}
                     {Nat.suc n}
                     (¬a≤b=>b<a
                       ¬p))) ⟩
          - (+ (Nat.suc n ∸ n₂)) ∎))
      (-+≤+ (Nat.suc n ∸ n₂) (n₁ Nat.+ n₂))
  ≤-compa-+ (-[1+_] n) (+_ n₁) (-[1+_] n₂) a≤b with n₁ Nat.≤? Nat.suc n₂
  ≤-compa-+ (-[1+_] n) (+_ n₁) (-[1+_] n₂) a≤b | yes p =
    cong-≤ℤ-r
      { - (+ (Nat.suc n₂ ∸ n₁))}
      (sym
        (begin
          n₁ ⊖ Nat.suc n₂
            ≡⟨ ⊖-swap n₁ (Nat.suc n₂) ⟩
          - (Nat.suc n₂ ⊖ n₁)
            ≡⟨ cong
                 (λ x -> - x)
                 (⊖-≥ p) ⟩
          - ( + (Nat.suc n₂ ∸ n₁)) ∎))
      (ℤp.≤-trans
        {j = -[1+ n Nat.+ n₂ ] }
        (-≤- k≤sk)
        (a≤b=>-b≤-a
          {+ (Nat.suc n₂ ∸ n₁)}
          {+ (Nat.suc n Nat.+ n₂)}
          (+≤+
            (Nat.≤-trans
              {j = (Nat.suc n₂) }
              (a-b≤a (Nat.suc n₂) n₁)
              (cong-≤-r
                {Nat.suc n₂ Nat.+ n}
                (cong Nat.suc (Nat.+-comm n₂ n))
                (s≤s (a≤a+b {n₂} {n})))))))
  ≤-compa-+ (-[1+_] n) (+_ n₁) (-[1+_] n₂) a≤b | no ¬p =
    cong-≤ℤ-r
      { (+ (n₁ ∸ Nat.suc n₂))}
      (sym
        (⊖-≥
          {n₁}
          {Nat.suc n₂}
          (a<b=>a≤b
            {Nat.suc n₂}
            {n₁}
            (¬a≤b=>b<a
              ¬p))))
      -≤+
  ≤-compa-+ (-[1+_] n) (-[1+_] n₁) (+_ n₂) a≤b with Nat.suc n Nat.≤? n₂
  ≤-compa-+ (-[1+_] n) (-[1+_] n₁) (+_ n₂) a≤b | yes p with Nat.suc n₁ Nat.≤? n₂
  ≤-compa-+ (-[1+_] n) (-[1+_] n₁) (+_ n₂) (-≤- n≤m) | yes p | yes p₁ =
    cong-≤ℤ-l
      {+ (n₂ ∸ (Nat.suc n))}
      (sym
        (⊖-≥ p))
      (cong-≤ℤ-r
        {+ (n₂ ∸ (Nat.suc n₁))}
        (sym
          (⊖-≥ p₁))
        (+≤+ (a≤b=>c-b≤c-a n₂ (s≤s n≤m))))
  ≤-compa-+ (-[1+_] n) (-[1+_] n₁) (+_ n₂) (-≤- n≤m) | yes p | no ¬p =
    ⊥-elim
      (¬p
        (Nat.≤-trans
          (s≤s n≤m)
          p))
  ≤-compa-+ (-[1+_] n) (-[1+_] n₁) (+_ n₂) a≤b | no ¬p with Nat.suc n₁ Nat.≤? n₂
  ≤-compa-+ (-[1+_] n) (-[1+_] n₁) (+_ n₂) (-≤- n≤m) | no ¬p | yes p =
    cong-≤ℤ-l
      { - (+ (Nat.suc n ∸ n₂))}
      (sym
        (begin
          n₂ ⊖ (Nat.suc n)
            ≡⟨ ⊖-swap n₂ (Nat.suc n) ⟩
          - (Nat.suc n ⊖ n₂)
            ≡⟨ cong
                 (λ x -> - x)
                 (⊖-≥
                   {Nat.suc n}
                   {n₂}
                   (a<b=>a≤b
                     (¬a≤b=>b<a ¬p))) ⟩
          - (+ (Nat.suc n ∸ n₂)) ∎))
      (cong-≤ℤ-r
        {+ (n₂ ∸ (Nat.suc n₁))}
        (sym
          (⊖-≥ p))
        (-+≤+ (Nat.suc n ∸ n₂) (n₂ ∸ (Nat.suc n₁))))
  ≤-compa-+ (-[1+_] n) (-[1+_] n₁) (+_ n₂) (-≤- n≤m) | no ¬p | no ¬p₁ = 
    cong-≤ℤ-l
      { - (+ (Nat.suc n ∸ n₂))}
      (sym
        (begin
          n₂ ⊖ (Nat.suc n)
            ≡⟨ ⊖-swap n₂ (Nat.suc n) ⟩
          - (Nat.suc n ⊖ n₂)
            ≡⟨ cong
                 (λ x -> - x)
                 (⊖-≥
                   {Nat.suc n}
                   {n₂}
                   (a<b=>a≤b
                     (¬a≤b=>b<a ¬p))) ⟩
          - (+ (Nat.suc n ∸ n₂)) ∎))
      (cong-≤ℤ-r
        { - (+ (Nat.suc n₁ ∸ n₂))}
        (sym
          (begin
            n₂ ⊖ (Nat.suc n₁)
              ≡⟨ ⊖-swap n₂ (Nat.suc n₁) ⟩
            - (Nat.suc n₁ ⊖ n₂)
              ≡⟨ cong
                   (λ x -> - x)
                   (⊖-≥
                     {Nat.suc n₁}
                     {n₂}
                     (a<b=>a≤b
                       (¬a≤b=>b<a ¬p₁))) ⟩
            - (+ (Nat.suc n₁ ∸ n₂)) ∎))
        (a≤b=>-b≤-a
          { (+ (Nat.suc n₁ ∸ n₂))}
          { (+ (Nat.suc n ∸ n₂))}
          (+≤+ (a≤b=>a-c≤b-c n₂ (s≤s n≤m)))))
  ≤-compa-+ (-[1+_] n) (-[1+_] n₁) (-[1+_] n₂) (-≤- n≤m) =
    -≤-
      (s≤s
        (a≤b=>c≤d=>a+c≤b+d
          n≤m
          (Nat.≤-refl {n₂})))

  _⊔ℤ_ :
    ℤ ->
    ℤ ->
    ℤ
  k ⊔ℤ k' with k ℤ.≤? k'
  k ⊔ℤ k' | yes p =
    k'
  k ⊔ℤ k' | no ¬p =
    k

  asso-⊔ℤ :
    (a b c : ℤ) ->
    a ⊔ℤ (b ⊔ℤ c) ≡ (a ⊔ℤ b) ⊔ℤ c
  asso-⊔ℤ a b c with a ℤ.≤? b
  asso-⊔ℤ a b c | yes p with b ℤ.≤? c
  asso-⊔ℤ a b c | yes p | yes p₁ with a ℤ.≤? c
  asso-⊔ℤ a b c | yes p | yes p₁ | yes p₂ =
    refl
  asso-⊔ℤ a b c | yes p | yes p₁ | no ¬p =
    ⊥-elim
      (¬p
        (ℤp.≤-trans p p₁))
  asso-⊔ℤ a b c | yes p | no ¬p with a ℤ.≤? b
  asso-⊔ℤ a b c | yes p | no ¬p | yes p₁ =
    refl
  asso-⊔ℤ a b c | yes p | no ¬p | no ¬p₁ =
    ⊥-elim (¬p₁ p)
  asso-⊔ℤ a b c | no ¬p with b ℤ.≤? c
  asso-⊔ℤ a b c | no ¬p | yes p =
    refl
  asso-⊔ℤ a b c | no ¬p | no ¬p₁ with a ℤ.≤? b
  asso-⊔ℤ a b c | no ¬p | no ¬p₁ | yes p =
    ⊥-elim (¬p p)
  asso-⊔ℤ a b c | no ¬p | no ¬p₁ | no ¬p₂ with a ℤ.≤? c
  asso-⊔ℤ a b c | no ¬p | no ¬p₁ | no ¬p₂ | yes p =
    ⊥-elim
      (¬p₁
        (ℤp.≤-trans
          (ℤp.<⇒≤
            {b}
            {a}
            (≰→>
              {a}
              {b}
              ¬p))
          p))
  asso-⊔ℤ a b c | no ¬p | no ¬p₁ | no ¬p₂ | no ¬p₃ =
    refl

  commu-⊔ℤ :
    (a b : ℤ) ->
    a ⊔ℤ b ≡ b ⊔ℤ a
  commu-⊔ℤ a b with a ℤ.≤? b
  commu-⊔ℤ a b | yes p with b ℤ.≤? a
  commu-⊔ℤ a b | yes p | yes p₁ =
    ℤp.≤-antisym {b} {a} p₁ p
  commu-⊔ℤ a b | yes p | no ¬p =
    refl
  commu-⊔ℤ a b | no ¬p with b ℤ.≤? a
  commu-⊔ℤ a b | no ¬p | yes p =
    refl
  commu-⊔ℤ a b | no ¬p | no ¬p₁ =
    ⊥-elim
      (¬p₁
        (ℤp.<⇒≤
          (≰→>
            ¬p)))

  _⊓ℤ_ :
    ℤ ->
    ℤ ->
    ℤ
  k ⊓ℤ k' with k ℤ.≤? k'
  k ⊓ℤ k' | yes p =
    k
  k ⊓ℤ k' | no ¬p =
    k'

  asso-⊓ℤ :
    (a b c : ℤ) ->
    a ⊓ℤ (b ⊓ℤ c) ≡ (a ⊓ℤ b) ⊓ℤ c
  asso-⊓ℤ a b c with a ℤ.≤? b
  asso-⊓ℤ a b c | yes p with b ℤ.≤? c
  asso-⊓ℤ a b c | yes p | yes p₁ with a ℤ.≤? c
  asso-⊓ℤ a b c | yes p | yes p₁ | yes p₂ with a ℤ.≤? b
  asso-⊓ℤ a b c | yes p | yes p₁ | yes p₂ | yes p₃ =
    refl
  asso-⊓ℤ a b c | yes p | yes p₁ | yes p₂ | no ¬p =
    ⊥-elim (¬p p)
  asso-⊓ℤ a b c | yes p | yes p₁ | no ¬p =
    ⊥-elim
      (¬p
        (ℤp.≤-trans p p₁))
  asso-⊓ℤ a b c | yes p | no ¬p with a ℤ.≤? b
  asso-⊓ℤ a b c | yes p | no ¬p | yes p₁ =
    refl
  asso-⊓ℤ a b c | yes p | no ¬p | no ¬p₁ =
    ⊥-elim (¬p₁ p)
  asso-⊓ℤ a b c | no ¬p with b ℤ.≤? c
  asso-⊓ℤ a b c | no ¬p | yes p with a ℤ.≤? b
  asso-⊓ℤ a b c | no ¬p | yes p | yes p₁ =
    ⊥-elim (¬p p₁)
  asso-⊓ℤ a b c | no ¬p | yes p | no ¬p₁ =
    refl
  asso-⊓ℤ a b c | no ¬p | no ¬p₁ with a ℤ.≤? b
  asso-⊓ℤ a b c | no ¬p | no ¬p₁ | yes p =
    ⊥-elim (¬p p)
  asso-⊓ℤ a b c | no ¬p | no ¬p₁ | no ¬p₂ with a ℤ.≤? c
  asso-⊓ℤ a b c | no ¬p | no ¬p₁ | no ¬p₂ | yes p =
    ⊥-elim
      (¬p₁
        (ℤp.≤-trans
          (ℤp.<⇒≤
            {b}
            {a}
            (≰→>
              {a}
              {b}
              ¬p))
          p))
  asso-⊓ℤ a b c | no ¬p | no ¬p₁ | no ¬p₂ | no ¬p₃ =
    refl

  commu-⊓ℤ :
    (a b : ℤ) ->
    a ⊓ℤ b ≡ b ⊓ℤ a
  commu-⊓ℤ a b with a ℤ.≤? b
  commu-⊓ℤ a b | yes p with b ℤ.≤? a
  commu-⊓ℤ a b | yes p | yes p₁ =
    ℤp.≤-antisym {a} {b} p p₁
  commu-⊓ℤ a b | yes p | no ¬p =
    refl
  commu-⊓ℤ a b | no ¬p with b ℤ.≤? a
  commu-⊓ℤ a b | no ¬p | yes p =
    refl
  commu-⊓ℤ a b | no ¬p | no ¬p₁ =
    ⊥-elim
      (¬p₁
        (ℤp.<⇒≤
          (≰→>
            ¬p)))

  abso-⊔ℤ :
    (a b : ℤ) ->
    a ⊔ℤ (a ⊓ℤ b) ≡ a
  abso-⊔ℤ a b with a ℤ.≤? b
  abso-⊔ℤ a b | yes p with a ℤ.≤? a
  abso-⊔ℤ a b | yes p | yes p₁ =
    refl
  abso-⊔ℤ a b | yes p | no ¬p =
    ⊥-elim (¬p ℤp.≤-refl)
  abso-⊔ℤ a b | no ¬p with a ℤ.≤? b
  abso-⊔ℤ a b | no ¬p | yes p =
    ⊥-elim (¬p p)
  abso-⊔ℤ a b | no ¬p | no ¬p₁ = 
    refl

  abso-⊓ℤ :
    (a b : ℤ) ->
    a ⊓ℤ (a ⊔ℤ b) ≡ a
  abso-⊓ℤ a b with a ℤ.≤? b
  abso-⊓ℤ a b | yes p with a ℤ.≤? b
  abso-⊓ℤ a b | yes p | yes p₁ =
    refl
  abso-⊓ℤ a b | yes p | no ¬p =
    ⊥-elim (¬p p)
  abso-⊓ℤ a b | no ¬p with a ℤ.≤? a
  abso-⊓ℤ a b | no ¬p | yes p =
    refl
  abso-⊓ℤ a b | no ¬p | no ¬p₁ = 
    ⊥-elim (¬p₁ ℤp.≤-refl)

  compa-+ :
    (a b c : ℤ) ->
    ((a ⊓ℤ b) ℤ.+ c) ⊓ℤ (b ℤ.+ c) ≡ ((a ⊓ℤ b) ℤ.+ c)
  compa-+ a b c with a ℤ.≤? b
  compa-+ a b c | yes p with (a ℤ.+ c) ℤ.≤? (b ℤ.+ c)
  compa-+ a b c | yes p | yes p₁ =
    refl
  compa-+ a b c | yes p | no ¬p =
    ⊥-elim
      (¬p
        (≤-compa-+ a b c p))
  compa-+ a b c | no ¬p with (b ℤ.+ c) ℤ.≤? (b ℤ.+ c)
  compa-+ a b c | no ¬p | yes p =
    refl
  compa-+ a b c | no ¬p | no ¬p₁ =
    ⊥-elim (¬p₁ ℤp.≤-refl)

