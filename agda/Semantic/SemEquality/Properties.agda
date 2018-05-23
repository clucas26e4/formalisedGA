module Semantic.SemEquality.Properties where
  
  {- STDLIB -}
  open import Nat
  open import Equality

  {- Syntax -}
  open import Syntax.Term

  {- Semantic -}
  open import Semantic.SemEquality

  congₛ :
    {A B : Term} ->
    A ≡ B ->
    A ≡ₛ B
  congₛ refl =
    reflₛ

  ≤-compa-+S :
    {A B C : Term} ->
    ((A ⊓S B) +S C) ≤S (B +S C)
  ≤-compa-+S = compa-+S

  -S-distri :
    {A B : Term} ->
    -S (A +S B) ≡ₛ (-S A) +S (-S B)
  -S-distri {A} {B} =
    beginₛ
      (-S (A +S B))
        ≡ₛ⟨ symₛ neutral-+S ⟩
      (-S (A +S B)) +S botAG
        ≡ₛ⟨ symₛ neutral-+S ⟩
      ((-S (A +S B)) +S botAG) +S botAG
        ≡ₛ⟨ ctxtₛ
              (((-C ((CC A) +C (CC B))) +C ●) +C botC)
              (symₛ opp-+S) ⟩
      ((-S (A +S B)) +S (A +S (-S A))) +S botAG
        ≡ₛ⟨ ctxtₛ
              (● +C botC)
              asso-+S ⟩
      (((-S (A +S B)) +S A) +S (-S A)) +S botAG
        ≡ₛ⟨ symₛ asso-+S ⟩
      ((-S (A +S B)) +S A) +S ((-S A) +S botAG)
        ≡ₛ⟨ ctxtₛ
              (((-C ((CC A) +C (CC B))) +C (CC A)) +C ((-C (CC A)) +C ●))
              (symₛ opp-+S) ⟩
      ((-S (A +S B)) +S A) +S ((-S A) +S (B +S (-S B)))
        ≡ₛ⟨ ctxtₛ
              (((-C ((CC A) +C (CC B))) +C (CC A)) +C ●)
              asso-+S ⟩
      ((-S (A +S B)) +S A) +S (((-S A) +S B) +S (-S B))
        ≡ₛ⟨ ctxtₛ
              (((-C ((CC A) +C (CC B))) +C (CC A)) +C (● +C (-C (CC B))))
              commu-+S ⟩
      ((-S (A +S B)) +S A) +S ((B +S (-S A)) +S (-S B))
        ≡ₛ⟨ ctxtₛ
              (((-C ((CC A) +C (CC B))) +C (CC A)) +C ●)
              (symₛ asso-+S) ⟩
      ((-S (A +S B)) +S A) +S (B +S ((-S A) +S (-S B)))
        ≡ₛ⟨ asso-+S ⟩
      (((-S (A +S B)) +S A) +S B) +S ((-S A) +S (-S B))
        ≡ₛ⟨ ctxtₛ
              ((● +C ((-C (CC A)) +C (-C (CC B)))))
              (symₛ asso-+S) ⟩
      ((-S (A +S B)) +S (A +S B)) +S ((-S A) +S (-S B))
        ≡ₛ⟨  ctxtₛ
              ((● +C ((-C (CC A)) +C (-C (CC B)))))
              (transₛ commu-+S opp-+S) ⟩
      botAG +S ((-S A) +S (-S B))
        ≡ₛ⟨ commu-+S ⟩
      ((-S A) +S (-S B)) +S botAG
        ≡ₛ⟨ neutral-+S ⟩
      (-S A) +S (-S B) ∎ₛ

  *S-distri :
    {A B : Term} ->
    (k : ℕ) ->
    k *S (A +S B) ≡ₛ (k *S A) +S (k *S B) 
  *S-distri {A} {B} zero = 
    symₛ
      neutral-+S
  *S-distri {A} {B} (suc zero) = 
    reflₛ
  *S-distri {A} {B} (suc (suc k)) =
    beginₛ
      (A +S B) +S ((suc k) *S (A +S B))
        ≡ₛ⟨ ctxtₛ
              (((CC A) +C (CC B)) +C ●)
              (*S-distri  (suc k))  ⟩
      (A +S B) +S (((suc k) *S A) +S ((suc k) *S B))
        ≡ₛ⟨ symₛ asso-+S ⟩
      A +S (B +S (((suc k) *S A) +S ((suc k) *S B)))
        ≡ₛ⟨ ctxtₛ
              ((CC A) +C ●)
              commu-+S ⟩
      A +S ((((suc k) *S A) +S ((suc k) *S B)) +S B)
        ≡ₛ⟨ ctxtₛ
              ((CC A) +C ●)
              (symₛ asso-+S) ⟩
      A +S (((suc k) *S A) +S (((suc k) *S B) +S B))
        ≡ₛ⟨ asso-+S ⟩
      (A +S ((suc k) *S A)) +S (((suc k) *S B) +S B)
        ≡ₛ⟨ ctxtₛ
              ((CC (A +S ((suc k) *S A))) +C ●)
              commu-+S ⟩
      (A +S ((suc k) *S A)) +S (B +S ((suc k) *S B)) ∎ₛ

  -S-botAG :
    botAG ≡ₛ (-S botAG)
  -S-botAG = 
    beginₛ
      botAG
        ≡ₛ⟨ symₛ opp-+S ⟩
      botAG +S (-S botAG)
        ≡ₛ⟨ commu-+S ⟩
      (-S botAG) +S botAG
        ≡ₛ⟨ neutral-+S ⟩
      (-S botAG) ∎ₛ

  *S--S :
    {A : Term} ->
    (k : ℕ) ->
    k *S (-S A) ≡ₛ -S (k *S A)
  *S--S {A} zero = -S-botAG
  *S--S {A} (suc zero) = reflₛ
  *S--S {A} (suc (suc k)) = 
    beginₛ
      (-S A) +S (suc k *S (-S A))
        ≡ₛ⟨ ctxtₛ
              ((-C (CC A)) +C ●)
              (*S--S (suc k)) ⟩
      (-S A) +S (-S (suc k *S A))
        ≡ₛ⟨ symₛ -S-distri ⟩
      -S (A +S (suc k *S A)) ∎ₛ

  -S--S :
    {A : Term} ->
    -S (-S A) ≡ₛ A
  -S--S {A} = 
    beginₛ
      (-S (-S A))
        ≡ₛ⟨ symₛ neutral-+S ⟩
      (-S (-S A)) +S botAG
        ≡ₛ⟨ ctxtₛ
              ((-C (-C (CC A))) +C ●)
              (symₛ opp-+S) ⟩
      (-S (-S A)) +S (A +S (-S A))
        ≡ₛ⟨ ctxtₛ
              ((-C (-C (CC A))) +C ●)
              commu-+S ⟩
      (-S (-S A)) +S ((-S A) +S A)
        ≡ₛ⟨ asso-+S ⟩
      ((-S (-S A)) +S (-S A)) +S A
        ≡ₛ⟨ ctxtₛ
              (● +C (CC A))
              commu-+S ⟩
      ((-S A) +S (-S (-S A))) +S A
        ≡ₛ⟨ ctxtₛ
              (● +C (CC A))
              opp-+S ⟩
      botAG +S A
        ≡ₛ⟨ commu-+S ⟩
      A +S botAG
        ≡ₛ⟨ neutral-+S ⟩
      A ∎ₛ

  ≤S-antisym :
    {A B : Term} ->
    (A≤SB : A ≤S B) ->
    (B≤SA : B ≤S A) ->
    A ≡ₛ B
  ≤S-antisym {A} {B} A≤SB B≤SA = 
    beginₛ
      A
        ≡ₛ⟨ symₛ A≤SB ⟩
      A ⊓S B
        ≡ₛ⟨ commu-⊓S ⟩
      B ⊓S A
        ≡ₛ⟨ B≤SA ⟩
      B ∎ₛ

  ≤S-cong-l :
    {A A' B : Term} ->
    (A=A' : A ≡ₛ A') ->
    (A≤SB : A ≤S B) ->
    A' ≤S B
  ≤S-cong-l {A} {A'} {B} A=A' A≤SB = 
    beginₛ
      A' ⊓S B
        ≡ₛ⟨ ctxtₛ
              (● ⊓C (CC B))
              (symₛ A=A') ⟩
      A ⊓S B
        ≡ₛ⟨ A≤SB ⟩
      A
        ≡ₛ⟨ A=A' ⟩
      A' ∎ₛ

  ≤S-cong-r :
    {A B B' : Term} ->
    (B=B' : B ≡ₛ B') ->
    (A≤SB : A ≤S B) ->
    A ≤S B'
  ≤S-cong-r {A} {B} {B'} B=B' A≤SB = 
    beginₛ
      A ⊓S B'
        ≡ₛ⟨ ctxtₛ
              ((CC A) ⊓C ●)
              (symₛ B=B') ⟩
      A ⊓S B
        ≡ₛ⟨ A≤SB ⟩
      A ∎ₛ

  ≤S-trans :
    {A B C : Term} ->
    (A≤B : A ≤S B) ->
    (B≤C : B ≤S C) ->
    A ≤S C
  ≤S-trans {A} {B} {C} A≤B B≤C = 
    beginₛ
      A ⊓S C
        ≡ₛ⟨ ctxtₛ
              (● ⊓C (CC C))
              (symₛ A≤B) ⟩
      (A ⊓S B) ⊓S C
        ≡ₛ⟨ symₛ asso-⊓S ⟩
      A ⊓S (B ⊓S C)
        ≡ₛ⟨ ctxtₛ
              ((CC A) ⊓C ●)
              B≤C ⟩
      A ⊓S B
        ≡ₛ⟨ A≤B ⟩
      A ∎ₛ

  ≤S-+S :
    {A B C : Term} ->
    (A≤SB : A ≤S B) ->
    (A +S C) ≤S (B +S C)
  ≤S-+S {A} {B} {C} A≤SB = 
    ≤S-cong-l
      {A = (A ⊓S B) +S C}
      (ctxtₛ
        (● +C (CC C))
        A≤SB)
      ≤-compa-+S

  ⊓S-⊔S :
    {A B : Term} ->
    (A⊓B=A : A ⊓S B ≡ₛ A) ->
    A ⊔S B ≡ₛ B
  ⊓S-⊔S {A} {B} A⊓B=A =
    beginₛ
      A ⊔S B
        ≡ₛ⟨ ctxtₛ
              (● ⊔C (CC B))
              (symₛ A⊓B=A) ⟩
      (A ⊓S B) ⊔S B
        ≡ₛ⟨ commu-⊔S ⟩
      B ⊔S (A ⊓S B)
        ≡ₛ⟨ ctxtₛ
              ((CC B) ⊔C ●)
              commu-⊓S ⟩
      B ⊔S (B ⊓S A)
        ≡ₛ⟨ abso-⊔S ⟩
      B ∎ₛ

  ⊔S-⊓S :
    {A B : Term} ->
    (A⊔B=A : A ⊔S B ≡ₛ A) ->
    A ⊓S B ≡ₛ B
  ⊔S-⊓S {A} {B} A⊔B=A = 
      A ⊓S B
        ≡ₛ⟨ ctxtₛ
              (● ⊓C (CC B))
              (symₛ A⊔B=A) ⟩
      (A ⊔S B) ⊓S B
        ≡ₛ⟨ commu-⊓S ⟩
      B ⊓S (A ⊔S B)
        ≡ₛ⟨ ctxtₛ
              ((CC B) ⊓C ●)
              commu-⊔S ⟩
      B ⊓S (B ⊔S A)
        ≡ₛ⟨ abso-⊓S ⟩
      B ∎ₛ

  ≤S-refl-cong :
    {A B : Term} ->
    (A ⊓S A) ⊓S B ≡ₛ A ⊓S B
  ≤S-refl-cong {A} {B} = 
    beginₛ
      (A ⊓S A) ⊓S B
        ≡ₛ⟨ symₛ asso-⊓S ⟩
      A ⊓S (A ⊓S B)
        ≡ₛ⟨ commu-⊓S ⟩
      (A ⊓S B) ⊓S A
        ≡ₛ⟨ ctxtₛ
              (● ⊓C (CC A))
              (symₛ neutral-+S) ⟩
      ((A ⊓S B) +S botAG) ⊓S A
        ≡ₛ⟨ ctxtₛ
              ((((CC A) ⊓C (CC B)) +C botC) ⊓C ●)
              (symₛ neutral-+S) ⟩
      ((A ⊓S B) +S botAG) ⊓S (A +S botAG)
        ≡ₛ⟨ ctxtₛ
              ((● +C botC) ⊓C ((CC A) +C botC))
              commu-⊓S ⟩
      ((B ⊓S A) +S botAG) ⊓S (A +S botAG)
        ≡ₛ⟨ ≤-compa-+S ⟩
      (B ⊓S A) +S botAG
        ≡ₛ⟨ neutral-+S ⟩
      (B ⊓S A)
        ≡ₛ⟨ commu-⊓S ⟩
      A ⊓S B ∎ₛ

  ≤S-refl :
    {A : Term} ->
    A ≤S A
  ≤S-refl {A} = 
    beginₛ
      A ⊓S A
        ≡ₛ⟨ ctxtₛ
              ((CC A) ⊓C ●)
              (symₛ (abso-⊓S)) ⟩
      A ⊓S (A ⊓S (A ⊔S A))
        ≡ₛ⟨ asso-⊓S ⟩
      (A ⊓S A) ⊓S (A ⊔S A)
        ≡ₛ⟨ ≤S-refl-cong ⟩
      A ⊓S (A ⊔S A)
        ≡ₛ⟨ abso-⊓S ⟩
      A ∎ₛ

  ≤S-⊓S :
    {A B C : Term} ->
    (A≤B : A ≤S B) ->
    (A≤C : A ≤S C) ->
    A ≤S (B ⊓S C)
  ≤S-⊓S {A} {B} {C} A≤B A≤C = 
    beginₛ
      A ⊓S (B ⊓S C)
        ≡ₛ⟨ asso-⊓S ⟩
      (A ⊓S B) ⊓S C
        ≡ₛ⟨ ctxtₛ
              (● ⊓C (CC C))
              A≤B ⟩
      A ⊓S C
        ≡ₛ⟨ A≤C ⟩
      A ∎ₛ

  ≤S-⊔S :
    {A B : Term} ->
    A ≤S (A ⊔S B)
  ≤S-⊔S {A} {B} = 
    abso-⊓S

  ⊔S-≤S :
    {A B C : Term} ->
    (B≤A : B ≤S A) ->
    (C≤A : C ≤S A) ->
    (B ⊔S C) ≤S A
  ⊔S-≤S {A} {B} {C} B≤A C≤A = 
    beginₛ
      (B ⊔S C) ⊓S A
        ≡ₛ⟨ commu-⊓S ⟩
      A ⊓S (B ⊔S C)
        ≡ₛ⟨ ⊔S-⊓S
              {A}
              {B ⊔S C}
              (beginₛ
                A ⊔S (B ⊔S C)
                  ≡ₛ⟨ commu-⊔S ⟩
                (B ⊔S C) ⊔S A
                  ≡ₛ⟨ symₛ asso-⊔S ⟩
                B ⊔S (C ⊔S A)
                  ≡ₛ⟨ ctxtₛ
                        ((CC B) ⊔C ●)
                        (⊓S-⊔S C≤A) ⟩
                B ⊔S A
                  ≡ₛ⟨ ⊓S-⊔S B≤A ⟩
                A ∎ₛ) ⟩
      B ⊔S C ∎ₛ

  A≤B-C=>A+C≤B :
    {A B C : Term} ->
    (A≤B-C : A ≤S (B +S (-S C))) ->
    A +S C ≤S B
  A≤B-C=>A+C≤B {A} {B} {C} A≤B-C = 
    ≤S-cong-r
      {A +S C}
      {(B +S (-S C)) +S C}
      {B}
      (beginₛ
        (B +S (-S C)) +S C
          ≡ₛ⟨ symₛ asso-+S ⟩
        B +S ((-S C) +S C)
          ≡ₛ⟨ ctxtₛ
                ((CC B) +C ●)
                commu-+S ⟩
        B +S (C +S (-S C))
          ≡ₛ⟨ ctxtₛ
                ((CC B) +C ●)
                opp-+S ⟩
        B +S botAG
          ≡ₛ⟨ neutral-+S ⟩
        B ∎ₛ)
      (≤S-+S
        A≤B-C)

  A-C≤B=>A≤B+C :
    {A B C : Term} ->
    (A-C≤B : (A +S (-S C)) ≤S B) ->
    A ≤S B +S C
  A-C≤B=>A≤B+C {A} {B} {C} A-C≤B = 
    ≤S-cong-l
      {(A +S (-S C)) +S C}
      {A}
      {B +S C}
      (
      (beginₛ
        (A +S (-S C)) +S C
          ≡ₛ⟨ symₛ asso-+S ⟩
        A +S ((-S C) +S C)
          ≡ₛ⟨ ctxtₛ
                ((CC A) +C ●)
                commu-+S ⟩
        A +S (C +S (-S C))
          ≡ₛ⟨ ctxtₛ
                ((CC A) +C ●)
                opp-+S ⟩
        A +S botAG
          ≡ₛ⟨ neutral-+S ⟩
        A ∎ₛ))
      (≤S-+S
        A-C≤B)

  A+C≤B=>A≤B-C :
    {A B C : Term} ->
    (A+C≤B : (A +S C) ≤S B) ->
    A ≤S B +S (-S C)
  A+C≤B=>A≤B-C {A} {B} {C} A+C≤B = 
    A-C≤B=>A≤B+C
      {A}
      {B}
      { -S C}
      (≤S-cong-l
        {A +S C}
        {A +S (-S (-S C))}
        {B}
        (ctxtₛ
          ((CC A) +C ●)
          (symₛ -S--S))
        A+C≤B)

  A≤B+C=>A-C≤B :
    {A B C : Term} ->
    (A≤B+C : A ≤S (B +S C)) ->
    (A +S (-S C)) ≤S B
  A≤B+C=>A-C≤B {A} {B} {C} A≤B+C =  
    A≤B-C=>A+C≤B
      {A}
      {B}
      { -S C}
      (≤S-cong-r
        {A}
        {B +S C}
        {B +S (-S (-S C))}
        (ctxtₛ
          ((CC B) +C ●)
          (symₛ -S--S))
        A≤B+C)
                               
  ⊔S-+S :
    {A B C : Term} ->
    (A ⊔S B) +S C ≡ₛ (A +S C) ⊔S (B +S C)
  ⊔S-+S {A} {B} {C} = 
    ≤S-antisym
      (A≤B-C=>A+C≤B
        {A ⊔S B}
        {(A +S C) ⊔S (B +S C)}
        {C}
        (⊔S-≤S
          (A+C≤B=>A≤B-C
            ≤S-⊔S)
          (A+C≤B=>A≤B-C
            (≤S-cong-r
              {B = (B +S C) ⊔S (A +S C)}
              commu-⊔S
              ≤S-⊔S))))
      (⊔S-≤S
        (≤S-cong-l
          {A ⊓S (A ⊔S B) +S C}
          {A +S C}
          {A ⊔S B +S C}
          (ctxtₛ
            (● +C (CC C))
            abso-⊓S)
          ≤-compa-+S)
        (≤S-cong-l
          {B ⊓S (A ⊔S B) +S C}
          {B +S C}
          {A ⊔S B +S C}
          (beginₛ
            B ⊓S (A ⊔S B) +S C
              ≡ₛ⟨ ctxtₛ
                    (((CC B) ⊓C ●) +C (CC C))
                    commu-⊔S ⟩
            B ⊓S (B ⊔S A) +S C
              ≡ₛ⟨ ctxtₛ
                    (● +C (CC C))
                    abso-⊓S ⟩
            B +S C ∎ₛ)
          ≤-compa-+S))

  ⊓S-≤S :
    {A B : Term} ->
    A ⊓S B ≤S A
  ⊓S-≤S {A} {B} = 
    beginₛ
      (A ⊓S B) ⊓S A
        ≡ₛ⟨ commu-⊓S ⟩
      A ⊓S (A ⊓S B)
        ≡ₛ⟨ asso-⊓S ⟩
      (A ⊓S A) ⊓S B
        ≡ₛ⟨ ≤S-refl-cong ⟩
      A ⊓S B ∎ₛ

  ≤S--S :
    {A B : Term} ->
    (A≤B : A ≤S B) ->
    (-S B) ≤S (-S A)
  ≤S--S {A} {B} A≤B = 
    ≤S-cong-l
      {botAG +S (-S B)}
      {(-S B)}
      {(-S A)}
      (beginₛ
        botAG +S (-S B)
          ≡ₛ⟨ commu-+S ⟩
        (-S B) +S botAG
          ≡ₛ⟨ neutral-+S ⟩
        (-S B) ∎ₛ)
      (A≤B+C=>A-C≤B
        (≤S-cong-r
          {B = B +S (-S A)}
          commu-+S
          (A+C≤B=>A≤B-C
            (≤S-cong-l
              {A = A}
              (symₛ
                (transₛ
                  commu-+S
                  neutral-+S))
              A≤B))))

  -S-⊓S-⊔S :
    {A B : Term} ->
    -S (A ⊓S B) ≡ₛ (-S A) ⊔S (-S B)
  -S-⊓S-⊔S {A} {B} =
    ≤S-antisym
      (≤S-cong-r
        {B = -S (-S ((-S A) ⊔S (-S B)))}
        -S--S
        (≤S--S
          (≤S-⊓S
            (≤S-cong-r
              {B = (-S (-S A))}
              -S--S
              (≤S--S
                ≤S-⊔S))
            (≤S-cong-r
              {B = (-S (-S B))}
              -S--S
              (≤S--S
                (≤S-cong-r
                  {B = (-S B) ⊔S (-S A)}
                  commu-⊔S
                  ≤S-⊔S))))))
      (⊔S-≤S
        (≤S--S
          ⊓S-≤S)
        (≤S--S
          (≤S-cong-l
            {A = B ⊓S A}
            commu-⊓S
            ⊓S-≤S)))

  ⊓S-≤S-⊔S :
    {A B : Term} ->
    A ⊓S B ≤S A ⊔S B
  ⊓S-≤S-⊔S {A} {B} =
    ≤S-trans
      {B = A}
      ⊓S-≤S
      ≤S-⊔S
      
  -S-eq-> :
    {A B : Term} ->
    (A=B : A ≡ₛ B) ->
    (-S A) ≡ₛ (-S B)
  -S-eq-> {A} {B} A=B =
    ctxtₛ
      (-C ●)
      A=B

  -S-eq<- :
    {A B : Term} ->
    (-A=-B : (-S A) ≡ₛ (-S B)) ->
    A ≡ₛ B
  -S-eq<- {A} {B} -A=-B =
    beginₛ
      A
        ≡ₛ⟨ symₛ -S--S ⟩
      -S (-S A)
        ≡ₛ⟨ ctxtₛ
              (-C ●)
              -A=-B ⟩
      -S (-S B)
        ≡ₛ⟨ -S--S ⟩
      B ∎ₛ
      
  A≤B=>C≤D=>A+C≤B+D :
    {A B C D : Term} ->
    (A≤B : A ≤S B) ->
    (C≤D : C ≤S D) ->
    (A +S C) ≤S (B +S D)
  A≤B=>C≤D=>A+C≤B+D {A} {B} {C} {D} A≤B C≤D =
    ≤S-trans
      {B = B +S C}
      (≤S-+S
        A≤B)
      (≤S-cong-l
        {A = C +S B}
        commu-+S
        (≤S-cong-r
          {B = D +S B}
          commu-+S
          (≤S-+S
            C≤D)))

  *S-compa :
    {A : Term} ->
    (k : ℕ) ->
    botAG ≤S k *S (A ⊔S botAG)
  *S-compa {A} zero = 
    ≤S-refl
  *S-compa {A} (suc zero) = 
    ≤S-cong-r
      {B = botAG ⊔S A}
      commu-⊔S
      ≤S-⊔S
  *S-compa {A} (suc (suc k)) = 
    ≤S-cong-l
      {A = botAG +S botAG}
      (neutral-+S)
      (A≤B=>C≤D=>A+C≤B+D
        (≤S-cong-r
          {B = botAG ⊔S A}
          commu-⊔S
          ≤S-⊔S)
        (*S-compa (suc k)))

  ≤S-compa-*S : 
    {A B : Term} ->
    (k : ℕ) ->
    (A≤B : A ≤S B) ->
    k *S A ≤S k *S B
  ≤S-compa-*S zero A≤B = 
    ≤S-refl
  ≤S-compa-*S (suc zero) A≤B = 
    A≤B
  ≤S-compa-*S (suc (suc k)) A≤B = 
    A≤B=>C≤D=>A+C≤B+D
      A≤B
      (≤S-compa-*S (suc k) A≤B) 

  A=B=>A-B=0 :
    {A B : Term} ->
    (A=B : A ≡ₛ B) ->
    A -S B ≡ₛ botAG
  A=B=>A-B=0 {A} {B} A=B =
    beginₛ
      A -S B
        ≡ₛ⟨ ctxtₛ
          ((CC A) -C ●)
          (symₛ A=B) ⟩
      A -S A
        ≡ₛ⟨ opp-+S ⟩
      botAG ∎ₛ

  A-B=0=>A=B :
    {A B : Term} ->
    (A-B=0 : A -S B ≡ₛ botAG) ->
    A ≡ₛ B
  A-B=0=>A=B {A} {B} A-B=0 =
    beginₛ
      A
        ≡ₛ⟨ symₛ neutral-+S ⟩
      A +S botAG
        ≡ₛ⟨ ctxtₛ
              ((CC A) +C ●)
              (symₛ opp-+S) ⟩
      A +S (B -S B)
        ≡ₛ⟨ commu-+S ⟩
      (B -S B) +S A
        ≡ₛ⟨ symₛ asso-+S ⟩
      B +S ((-S B) +S A)
        ≡ₛ⟨ ctxtₛ
              ((CC B) +C ●)
              commu-+S ⟩
      B +S (A -S B)
        ≡ₛ⟨ ctxtₛ
              ((CC B) +C ●)
              A-B=0 ⟩
      B +S botAG
        ≡ₛ⟨ neutral-+S ⟩
      B ∎ₛ

  -S-⊔S-⊓S :
    {A B : Term} ->
    -S (A ⊔S B) ≡ₛ (-S A) ⊓S (-S B)
  -S-⊔S-⊓S {A} {B} =
    beginₛ
      (-S (A ⊔S B))
        ≡ₛ⟨ ctxtₛ
              (-C ((CC A) ⊔C ●))
              (symₛ -S--S) ⟩
      (-S (A ⊔S (-S (-S B))))
        ≡ₛ⟨ ctxtₛ
              (-C (● ⊔C (CC (-S (-S B)))))
              (symₛ -S--S) ⟩
      (-S ((-S (-S A)) ⊔S (-S (-S B))))
        ≡ₛ⟨ ctxtₛ
              (-C ●)
              (symₛ -S-⊓S-⊔S) ⟩
      (-S (-S ((-S A) ⊓S (-S B))))
        ≡ₛ⟨ -S--S ⟩
      (-S A) ⊓S (-S B) ∎ₛ

  bot-≤S-⁺ :
    {A : Term} ->
    botAG ≤S A ⁺
  bot-≤S-⁺ {A} =
    ≤S-cong-r
      {B = botAG ⊔S A}
      commu-⊔S
      ≤S-⊔S

  bot-≤S-⁻ :
    {A : Term} ->
    botAG ≤S A ⁻
  bot-≤S-⁻ {A} =
    ≤S-cong-r
      {B = botAG ⊔S (-S A)}
      commu-⊔S
      ≤S-⊔S

  A+C=B=>A=B-C :
    {A B C : Term} ->
    (A+C=B : A +S C ≡ₛ B) ->
    A ≡ₛ B -S C
  A+C=B=>A=B-C {A} {B} {C} A+C=B =
    beginₛ
      A
        ≡ₛ⟨ symₛ neutral-+S ⟩
      A +S botAG
        ≡ₛ⟨ ctxtₛ
              ((CC A) +C ●)
              (symₛ opp-+S) ⟩
      A +S (C -S C)
        ≡ₛ⟨ asso-+S ⟩
      (A +S C) -S C
        ≡ₛ⟨ ctxtₛ
              (● -C (CC C))
              A+C=B ⟩
      B -S C ∎ₛ

  A=A⁺-A⁻ :
    {A : Term} ->
    A ≡ₛ (A ⁺) -S (A ⁻)
  A=A⁺-A⁻ {A} = 
    A+C=B=>A=B-C
      (symₛ
        (beginₛ
          A ⁺
            ≡ₛ⟨ ctxtₛ
                  ((CC A) ⊔C ●)
                  (symₛ opp-+S) ⟩
          A ⊔S (A -S A)
            ≡ₛ⟨ ctxtₛ
                  (● ⊔C (CC (A -S A)))
                  (transₛ (symₛ neutral-+S) commu-+S) ⟩
          (botAG +S A) ⊔S (A -S A)
            ≡ₛ⟨ ctxtₛ
                  ((CC (botAG +S A)) ⊔C ●)
                  commu-+S ⟩
          (botAG +S A) ⊔S ((-S A) +S A)
            ≡ₛ⟨ commu-⊔S ⟩
          ((-S A) +S A) ⊔S (botAG +S A)
            ≡ₛ⟨ symₛ ⊔S-+S ⟩
          (A ⁻) +S A
            ≡ₛ⟨ commu-+S ⟩
          A +S (A ⁻) ∎ₛ))

  A-C=B=>A=B+C :
    {A B C : Term} ->
    (A-C=B : A -S C ≡ₛ B) ->
    A ≡ₛ B +S C
  A-C=B=>A=B+C {A} {B} {C} A-C=B =
    beginₛ
      A
        ≡ₛ⟨ symₛ neutral-+S ⟩
      A +S botAG
        ≡ₛ⟨ ctxtₛ
              ((CC A) +C ●)
              (symₛ opp-+S) ⟩
      A +S (C -S C)
        ≡ₛ⟨ ctxtₛ
              ((CC A) +C ●)
              commu-+S ⟩
      A +S ((-S C) +S C)
        ≡ₛ⟨ asso-+S ⟩
      (A -S C) +S C
        ≡ₛ⟨ ctxtₛ
              (● +C (CC C))
              A-C=B ⟩
      B +S C ∎ₛ

  ⊓S-+S :
    {A B C : Term} ->
    (A +S C) ⊓S (B +S C) ≡ₛ (A ⊓S B) +S C
  ⊓S-+S {A} {B} {C} =
    beginₛ
      (A +S C) ⊓S (B +S C)
        ≡ₛ⟨ symₛ -S--S ⟩
      -S (-S ((A +S C) ⊓S (B +S C)))
        ≡ₛ⟨ ctxtₛ
              (-C ●)
              -S-⊓S-⊔S ⟩
      -S ((-S (A +S C)) ⊔S (-S (B +S C)))
        ≡ₛ⟨ ctxtₛ
              (-C (● ⊔C (CC (-S (B +S C)))))
              -S-distri ⟩
      -S (((-S A) -S C) ⊔S (-S (B +S C)))
        ≡ₛ⟨ ctxtₛ
              (-C((CC ((-S A) -S C)) ⊔C ●))
              -S-distri ⟩
      -S (((-S A) -S C) ⊔S ((-S B) -S C))
        ≡ₛ⟨ ctxtₛ
              (-C ●)
              (symₛ ⊔S-+S) ⟩
      -S (((-S A) ⊔S (-S B)) -S C)
        ≡ₛ⟨ -S-distri ⟩
      (-S ((-S A) ⊔S (-S B))) -S (-S C)
        ≡ₛ⟨ ctxtₛ
              (● -C (CC (-S C)))
              -S-⊔S-⊓S ⟩
      ((-S (-S A)) ⊓S (-S (-S B))) -S (-S C)
        ≡ₛ⟨ ctxtₛ
              ((● ⊓C (CC (-S (-S B)))) -C (-C (CC C)))
              -S--S ⟩
      (A ⊓S (-S (-S B))) -S (-S C)
        ≡ₛ⟨ ctxtₛ
              (((CC A) ⊓C ●) -C (-C (CC C)))
              -S--S ⟩
      (A ⊓S B) -S (-S C)
        ≡ₛ⟨ ctxtₛ
              ((CC (A ⊓S B)) +C ●)
              -S--S ⟩
      (A ⊓S B) +S C ∎ₛ

  A⁺⊓SA⁻=0 :
    {A : Term} ->
    (A ⁺) ⊓S (A ⁻) ≡ₛ botAG
  A⁺⊓SA⁻=0 {A} =
    beginₛ
      (A ⁺) ⊓S (A ⁻)
        ≡ₛ⟨ ctxtₛ
              (● ⊓C (CC (A ⁻)))
              (A-C=B=>A=B+C
                (symₛ A=A⁺-A⁻)) ⟩
      (A +S (A ⁻)) ⊓S (A ⁻)
        ≡ₛ⟨ ctxtₛ
              ((CC (A +S (A ⁻))) ⊓C ●)
              (symₛ neutral-+S) ⟩
      (A +S (A ⁻)) ⊓S ((A ⁻) +S botAG)
        ≡ₛ⟨  ctxtₛ
              ((CC (A +S (A ⁻))) ⊓C ●)
              commu-+S ⟩
      (A +S (A ⁻)) ⊓S (botAG +S (A ⁻))
        ≡ₛ⟨ ⊓S-+S ⟩
      (A ⊓S botAG) +S (A ⁻)
        ≡ₛ⟨ commu-+S ⟩
      (A ⁻) +S (A ⊓S botAG)
        ≡ₛ⟨ ctxtₛ
              ((CC (A ⁻)) +C ●)
              (symₛ -S--S) ⟩
      (A ⁻) -S (-S (A ⊓S botAG))
        ≡ₛ⟨ ctxtₛ
              ((CC (A ⁻)) -C ●)
              -S-⊓S-⊔S ⟩
      (A ⁻) -S ((-S A) ⊔S (-S botAG))
        ≡ₛ⟨ ctxtₛ
              ((CC (A ⁻)) -C ((CC (-S A)) ⊔C ●))
              (symₛ -S-botAG) ⟩
      (A ⁻) -S (A ⁻)
        ≡ₛ⟨ opp-+S ⟩
      botAG ∎ₛ

  cond-0≤A⊔B :
    {A B : Term} ->
    (A⊔B=A⁺⊔B⁺ : A ⊔S B ≡ₛ (A ⁺) ⊔S (B ⁺)) ->
    botAG ≤S A ⊔S B
  cond-0≤A⊔B {A} {B} A⊔B=A⁺⊔B⁺ =
    transₛ
      commu-⊓S
      (⊔S-⊓S
        (beginₛ
          (A ⊔S B) ⊔S botAG
            ≡ₛ⟨ ctxtₛ
                  ((CC (A ⊔S B)) ⊔C ●)
                  (symₛ
                    (⊓S-⊔S
                      ≤S-refl)) ⟩
          (A ⊔S B) ⊔S (botAG ⊔S botAG)
            ≡ₛ⟨ symₛ asso-⊔S ⟩
          A ⊔S (B ⊔S (botAG ⊔S botAG))
            ≡ₛ⟨ ctxtₛ
                  ((CC A) ⊔C ●)
                  asso-⊔S ⟩
          A ⊔S ((B ⊔S botAG) ⊔S botAG)
            ≡ₛ⟨ ctxtₛ
                  ((CC A) ⊔C ●)
                  commu-⊔S ⟩
          A ⊔S (botAG ⊔S (B ⁺))
            ≡ₛ⟨ asso-⊔S ⟩
          (A ⁺) ⊔S (B ⁺)
            ≡ₛ⟨ symₛ A⊔B=A⁺⊔B⁺ ⟩
          A ⊔S B ∎ₛ))

  cond-A⊔B=A⁺⊔B⁺ :
    {A B : Term} ->
    (0≤A⊔B : botAG ≤S A ⊔S B) ->
    A ⊔S B ≡ₛ (A ⁺) ⊔S (B ⁺)
  cond-A⊔B=A⁺⊔B⁺ {A} {B} 0≤A⊔B =
    beginₛ
      A ⊔S B
        ≡ₛ⟨ symₛ
              (transₛ
                commu-⊔S
                (⊓S-⊔S
                  0≤A⊔B)) ⟩
      (A ⊔S B) ⊔S botAG
        ≡ₛ⟨ ctxtₛ
              ((CC (A ⊔S B)) ⊔C ●)
              (symₛ
              (⊓S-⊔S
                ≤S-refl)) ⟩
      (A ⊔S B) ⊔S (botAG ⊔S botAG)
        ≡ₛ⟨ symₛ asso-⊔S ⟩
      A ⊔S (B ⊔S (botAG ⊔S botAG))
        ≡ₛ⟨ ctxtₛ
              ((CC A) ⊔C ●)
              asso-⊔S ⟩
      A ⊔S ((B ⊔S botAG) ⊔S botAG)
        ≡ₛ⟨ ctxtₛ
              ((CC A) ⊔C ●)
              commu-⊔S ⟩
      A ⊔S (botAG ⊔S (B ⁺))
        ≡ₛ⟨ asso-⊔S ⟩
      (A ⁺) ⊔S (B ⁺) ∎ₛ

  lemma-⊔S-⁺ :
    {A B : Term} ->
    A ⊔S B ≡ₛ ((A -S B) ⁺) +S B
  lemma-⊔S-⁺ {A} {B} =
    beginₛ
      A ⊔S B
        ≡ₛ⟨ ctxtₛ
              (● ⊔C (CC B))
              (symₛ neutral-+S) ⟩
      (A +S botAG) ⊔S B
        ≡ₛ⟨ ctxtₛ
              (((CC A) +C ●) ⊔C (CC B))
              (symₛ opp-+S) ⟩
      (A +S (B -S B)) ⊔S B
        ≡ₛ⟨ ctxtₛ
              (((CC A) +C ●) ⊔C (CC B))
              commu-+S ⟩
      (A +S ((-S B) +S B)) ⊔S B
        ≡ₛ⟨ ctxtₛ
              (● ⊔C (CC B))
              asso-+S ⟩
      ((A -S B) +S B) ⊔S B
        ≡ₛ⟨ ctxtₛ
              ((CC ((A -S B) +S B)) ⊔C ●)
              (symₛ neutral-+S) ⟩
      ((A -S B) +S B) ⊔S (B +S botAG)
        ≡ₛ⟨ ctxtₛ
              ((CC ((A -S B) +S B)) ⊔C ●)
              commu-+S ⟩
      ((A -S B) +S B) ⊔S (botAG +S B)
        ≡ₛ⟨ symₛ ⊔S-+S ⟩
      ((A -S B) ⁺) +S B ∎ₛ

  lemma-⊓S-⁺ :
    {A B : Term} ->
    A ⊓S B ≡ₛ A -S ((A -S B) ⁺)
  lemma-⊓S-⁺ {A} {B} =
    A+C=B=>A=B-C
      (transₛ
        commu-+S
        (symₛ
          (A-C=B=>A=B+C
            (beginₛ
              A -S (A ⊓S B)
                ≡ₛ⟨ ctxtₛ
                      ((CC A) +C ●)
                      -S-⊓S-⊔S ⟩
              A +S ((-S A) ⊔S (-S B))
                ≡ₛ⟨ commu-+S ⟩
              ((-S A) ⊔S (-S B)) +S A
                ≡ₛ⟨ ⊔S-+S ⟩
              ((-S A) +S A) ⊔S ((-S B) +S A)
                ≡ₛ⟨ ctxtₛ
                      (● ⊔C ( CC ((-S B) +S A)))
                      commu-+S ⟩
              (A -S A) ⊔S ((-S B) +S A)
                ≡ₛ⟨ ctxtₛ
                      (● ⊔C ( CC ((-S B) +S A)))
                      opp-+S ⟩
              botAG ⊔S ((-S B) +S A)
                ≡ₛ⟨ ctxtₛ
                      (botC ⊔C ●)
                      commu-+S ⟩
              botAG ⊔S (A -S B)
                ≡ₛ⟨ commu-⊔S ⟩
              (A -S B) ⁺ ∎ₛ))))

  A⊔B+A⊓B=A+B :
    {A B : Term} ->
    (A ⊔S B) +S (A ⊓S B) ≡ₛ A +S B
  A⊔B+A⊓B=A+B {A} {B} =
    beginₛ
      (A ⊔S B) +S (A ⊓S B)
        ≡ₛ⟨ ctxtₛ
              (● +C (CC (A ⊓S B)))
              lemma-⊔S-⁺ ⟩
      (((A -S B) ⁺) +S B) +S (A ⊓S B)
        ≡ₛ⟨ ctxtₛ
              (● +C (CC (A ⊓S B)))
              commu-+S ⟩
      (B +S ((A -S B) ⁺)) +S (A ⊓S B)
        ≡ₛ⟨ ctxtₛ
              (CC (B +S ((A -S B) ⁺)) +C ●)
              lemma-⊓S-⁺ ⟩
      (B +S ((A -S B) ⁺)) +S (A -S ((A -S B) ⁺))
        ≡ₛ⟨ ctxtₛ
              (CC (B +S ((A -S B) ⁺)) +C ●)
              commu-+S ⟩
      (B +S ((A -S B) ⁺)) +S ((-S ((A -S B) ⁺)) +S A)
        ≡ₛ⟨ asso-+S ⟩
      ((B +S ((A -S B) ⁺)) +S (-S ((A -S B) ⁺))) +S A
        ≡ₛ⟨ ctxtₛ
              (● +C (CC A))
              (symₛ asso-+S) ⟩
      (B +S (((A -S B) ⁺) +S (-S ((A -S B) ⁺)))) +S A
        ≡ₛ⟨ ctxtₛ
            ((CC B +C ●) +C (CC A))
            opp-+S ⟩
      (B +S botAG) +S A
        ≡ₛ⟨ ctxtₛ
              (● +C (CC A))
              neutral-+S ⟩
      B +S A
        ≡ₛ⟨ commu-+S ⟩
      A +S B ∎ₛ

  ⊔S-distri-⊓S :
    {A B C : Term} ->
    (A ⊓S B) ⊔S C ≡ₛ (A ⊔S C) ⊓S (B ⊔S C)
  ⊔S-distri-⊓S {A} {B} {C} =
    ≤S-antisym
      (≤S-⊓S
        (⊔S-≤S
          (≤S-trans
            {B = A}
            ⊓S-≤S
            ≤S-⊔S)
          (≤S-cong-r
            {B = C ⊔S A}
            commu-⊔S
            ≤S-⊔S))
        ((⊔S-≤S
          (≤S-trans
            {B = B}
            (≤S-cong-l
              {A = B ⊓S A}
              commu-⊓S
              ⊓S-≤S)
            ≤S-⊔S)
          (≤S-cong-r
            {B = C ⊔S B}
            commu-⊔S
            ≤S-⊔S))))
      (≤S-cong-l
        {A = m}
        reflₛ
        (≤S-cong-r
          {B = (A ⊓S B) -S ((-S C) +S ((A ⊓S B) ⊓S C))}
          (beginₛ
            (A ⊓S B) -S ((-S C) +S ((A ⊓S B) ⊓S C))
              ≡ₛ⟨ ctxtₛ
                    (CC (A ⊓S B) +C ●)
                    -S-distri ⟩
            (A ⊓S B) +S ((-S (-S C)) -S ((A ⊓S B) ⊓S C))
              ≡ₛ⟨ ctxtₛ
                    (CC (A ⊓S B) +C (● -C (CC ((A ⊓S B) ⊓S C))))
                    -S--S ⟩
            (A ⊓S B) +S (C -S ((A ⊓S B) ⊓S C))
              ≡ₛ⟨ asso-+S ⟩
            ((A ⊓S B) +S C) -S ((A ⊓S B) ⊓S C)
              ≡ₛ⟨ symₛ
                    (A+C=B=>A=B-C
                      A⊔B+A⊓B=A+B) ⟩
            (A ⊓S B) ⊔S C ∎ₛ)
          (A+C≤B=>A≤B-C
            (≤S-⊓S
              (≤S-cong-l
                {A = (m +S ((A ⊓S B) ⊓S C)) -S C}
                (beginₛ
                  (m +S (A ⊓S B) ⊓S C) -S C
                    ≡ₛ⟨ symₛ asso-+S ⟩
                  m +S (((A ⊓S B) ⊓S C) -S C)
                    ≡ₛ⟨ ctxtₛ
                          ((CC m) +C ●)
                          commu-+S ⟩
                  m +S ((-S C) +S ((A ⊓S B) ⊓S C)) ∎ₛ)
                (≤S-cong-r
                  {B = (A +S C) -S C}
                  (beginₛ
                    (A +S C) -S C
                      ≡ₛ⟨ symₛ asso-+S ⟩
                    A +S (C -S C)
                      ≡ₛ⟨ ctxtₛ
                            ((CC A) +C ●)
                            opp-+S ⟩
                    A +S botAG
                      ≡ₛ⟨ neutral-+S ⟩
                    A ∎ₛ)
                  (≤S-+S
                    (≤S-cong-r
                      {B = (A ⊔S C) +S (A ⊓S C)}
                      A⊔B+A⊓B=A+B
                      (≤S-trans
                        {B = m +S (A ⊓S C)}
                        (A≤B=>C≤D=>A+C≤B+D
                          ≤S-refl
                          (≤S-cong-l
                            {A = (A ⊓S C) ⊓S B}
                            (beginₛ
                              (A ⊓S C) ⊓S B
                                ≡ₛ⟨ symₛ asso-⊓S ⟩
                              A ⊓S (C ⊓S B)
                                ≡ₛ⟨ ctxtₛ
                                      ((CC A) ⊓C ●)
                                      commu-⊓S ⟩
                              A ⊓S (B ⊓S C)
                                ≡ₛ⟨ asso-⊓S ⟩
                              (A ⊓S B) ⊓S C ∎ₛ)
                            ⊓S-≤S))
                        (≤S-+S
                          ⊓S-≤S))))))
              (≤S-cong-l
                {A = (m +S ((A ⊓S B) ⊓S C)) -S C}
                ((beginₛ
                  (m +S (A ⊓S B) ⊓S C) -S C
                    ≡ₛ⟨ symₛ asso-+S ⟩
                  m +S (((A ⊓S B) ⊓S C) -S C)
                    ≡ₛ⟨ ctxtₛ
                          ((CC m) +C ●)
                          commu-+S ⟩
                  m +S ((-S C) +S ((A ⊓S B) ⊓S C)) ∎ₛ))
                ((≤S-cong-r
                  {B = (B +S C) -S C}
                  ((beginₛ
                    (B +S C) -S C
                      ≡ₛ⟨ symₛ asso-+S ⟩
                    B +S (C -S C)
                      ≡ₛ⟨ ctxtₛ
                            ((CC B) +C ●)
                            opp-+S ⟩
                    B +S botAG
                      ≡ₛ⟨ neutral-+S ⟩
                    B ∎ₛ))
                  ((≤S-+S
                    (≤S-cong-r
                      {B = (B ⊔S C) +S (B ⊓S C)}
                      A⊔B+A⊓B=A+B
                      (≤S-trans
                        {B = m +S (B ⊓S C)}
                        ((A≤B=>C≤D=>A+C≤B+D
                          ≤S-refl
                          ((≤S-cong-l
                            {A = (B ⊓S C) ⊓S A}
                            (beginₛ
                              (B ⊓S C) ⊓S A
                                ≡ₛ⟨ commu-⊓S ⟩
                              A ⊓S (B ⊓S C)
                                ≡ₛ⟨ asso-⊓S ⟩
                              (A ⊓S B) ⊓S C ∎ₛ)
                            ⊓S-≤S))))
                        (≤S-+S
                          (≤S-cong-l
                            commu-⊓S
                            ⊓S-≤S)))))))))))))
    where
    m : Term
    m = (A ⊔S C) ⊓S (B ⊔S C)

  A⊔B=A⁺⊔B⁺-A⁻⊓B⁻ :
    {A B : Term} ->
    A ⊔S B ≡ₛ ((A ⁺) ⊔S (B ⁺)) -S ((A ⁻) ⊓S (B ⁻))
  A⊔B=A⁺⊔B⁺-A⁻⊓B⁻ {A} {B} =
    beginₛ
      A ⊔S B
        ≡ₛ⟨ A=A⁺-A⁻ ⟩
      ((A ⊔S B) ⁺) -S ((A ⊔S B) ⁻)
        ≡ₛ⟨ ctxtₛ
            (● -C (CC ((A ⊔S B) ⁻)))
               (beginₛ
                 (A ⊔S B) ⊔S botAG
                   ≡ₛ⟨ ctxtₛ
                       ((CC (A ⊔S B)) ⊔C ●)
                         (symₛ
                           (⊓S-⊔S
                             ≤S-refl)) ⟩
                 (A ⊔S B) ⊔S (botAG ⊔S botAG)
                   ≡ₛ⟨ symₛ asso-⊔S ⟩
                 A ⊔S (B ⊔S (botAG ⊔S botAG))
                   ≡ₛ⟨ ctxtₛ
                       ((CC A) ⊔C ●)
                         asso-⊔S ⟩
                 A ⊔S ((B ⊔S botAG) ⊔S botAG)
                   ≡ₛ⟨ ctxtₛ
                       ((CC A) ⊔C ●)
                         commu-⊔S ⟩
                 A ⊔S (botAG ⊔S (B ⁺))
                   ≡ₛ⟨ asso-⊔S ⟩
                 (A ⁺) ⊔S (B ⁺) ∎ₛ ) ⟩
      ((A ⁺) ⊔S (B ⁺)) -S ((A ⊔S B) ⁻)
        ≡ₛ⟨ ctxtₛ
            (CC ((A ⁺) ⊔S (B ⁺)) -C (● ⊔C botC))
              -S-⊔S-⊓S ⟩
      ((A ⁺) ⊔S (B ⁺)) -S (((-S A) ⊓S (-S B)) ⊔S botAG)
        ≡ₛ⟨  ctxtₛ
             (CC ((A ⁺) ⊔S (B ⁺)) -C ●)
               ⊔S-distri-⊓S ⟩
      ((A ⁺) ⊔S (B ⁺)) -S ((A ⁻) ⊓S (B ⁻)) ∎ₛ

  cond-0≤A⊔B-2 :
    {A B : Term} ->
    (A⁻⊓B⁻=0 : (A ⁻) ⊓S (B ⁻) ≡ₛ botAG) ->
    botAG ≤S A ⊔S B
  cond-0≤A⊔B-2 {A} {B} A⁻⊓B⁻=0 =
    cond-0≤A⊔B
      (beginₛ
        A ⊔S B
          ≡ₛ⟨ A⊔B=A⁺⊔B⁺-A⁻⊓B⁻ ⟩
        ((A ⁺) ⊔S (B ⁺)) -S ((A ⁻) ⊓S (B ⁻))
          ≡ₛ⟨ ctxtₛ
                (CC ((A ⁺) ⊔S (B ⁺)) -C ●)
                A⁻⊓B⁻=0 ⟩
        ((A ⁺) ⊔S (B ⁺)) -S botAG
          ≡ₛ⟨ ctxtₛ
                (CC ((A ⁺) ⊔S (B ⁺)) +C ●)
                (symₛ -S-botAG) ⟩
        ((A ⁺) ⊔S (B ⁺)) +S botAG
          ≡ₛ⟨ neutral-+S ⟩
        ((A ⁺) ⊔S (B ⁺)) ∎ₛ)

  cond-A⁻⊓B⁻=0 :
    {A B : Term} ->
    (0≤A⊔B : botAG ≤S A ⊔S B) ->
    (A ⁻) ⊓S (B ⁻) ≡ₛ botAG
  cond-A⁻⊓B⁻=0 {A} {B} 0≤A⊔B =
    beginₛ
      (A ⁻) ⊓S (B ⁻)
        ≡ₛ⟨ A+C=B=>A=B-C
              (transₛ
                commu-+S
                (symₛ
                  (A-C=B=>A=B+C
                    (symₛ
                      A⊔B=A⁺⊔B⁺-A⁻⊓B⁻)))) ⟩
      ((A ⁺) ⊔S (B ⁺)) -S (A ⊔S B)
        ≡ₛ⟨ ctxtₛ
              (● -C (CC (A ⊔S B)))
              (symₛ
                (cond-A⊔B=A⁺⊔B⁺
                  0≤A⊔B)) ⟩
      (A ⊔S B) -S (A ⊔S B)
        ≡ₛ⟨ opp-+S ⟩
      botAG ∎ₛ

  0≤abs :
    {A : Term} ->
    botAG ≤S abs A
  0≤abs {A} =
    cond-0≤A⊔B-2
      (beginₛ
        (A ⁻) ⊓S ((-S A) ⁻)
          ≡ₛ⟨ ctxtₛ
                ((CC (A ⁻)) ⊓C (● ⊔C botC))
                -S--S ⟩
        (A ⁻) ⊓S (A ⁺)
          ≡ₛ⟨ commu-⊓S ⟩
        (A ⁺) ⊓S (A ⁻)
          ≡ₛ⟨ A⁺⊓SA⁻=0 ⟩
        botAG ∎ₛ)

  *S-distri-⊔S :
    {A B : Term} ->
    2 *S (A ⊔S B) ≡ₛ (2 *S A) ⊔S (2 *S B)
  *S-distri-⊔S {A} {B} =
    symₛ
      (beginₛ
        (2 *S A) ⊔S (2 *S B)
          ≡ₛ⟨ symₛ
                (⊓S-⊔S
                  (transₛ
                    (ctxtₛ
                      ((● ⊓C (CC ((A +S A) ⊔S (B +S B)))))
                      (transₛ (symₛ neutral-+S) commu-+S)
                    )
                    (transₛ
                      (A≤B-C=>A+C≤B
                        (≤S-cong-r
                          {B = abs (A -S B)}
                          (beginₛ
                            abs (A -S B)
                              ≡ₛ⟨ reflₛ ⟩
                            (A -S B) ⊔S (-S (A -S B))
                              ≡ₛ⟨ ctxtₛ
                                    ((CC (A -S B)) ⊔C ●)
                                    (beginₛ
                                      -S (A -S B)
                                        ≡ₛ⟨ -S-distri ⟩
                                      (-S A) -S (-S B)
                                        ≡ₛ⟨ ctxtₛ
                                              (CC (-S A) +C ●)
                                              -S--S ⟩
                                      (-S A) +S B
                                        ≡ₛ⟨ commu-+S ⟩
                                      B -S A
                                        ≡ₛ⟨ ctxtₛ
                                              (● -C (CC A))
                                              (symₛ neutral-+S) ⟩
                                      (B +S botAG) -S A
                                        ≡ₛ⟨ ctxtₛ
                                              (((CC B) +C ●) -C (CC A))
                                              (symₛ opp-+S) ⟩
                                      (B +S (B -S B)) -S A
                                        ≡ₛ⟨ ctxtₛ
                                              (● -C (CC A))
                                              asso-+S ⟩
                                      ((B +S B) -S B) -S A
                                        ≡ₛ⟨ symₛ asso-+S ⟩
                                      (B +S B) +S ((-S B) -S A)
                                        ≡ₛ⟨ ctxtₛ
                                              ((CC (B +S B)) +C ●)
                                              commu-+S ⟩
                                      (B +S B) +S ((-S A) -S B) ∎ₛ) ⟩
                            (A -S B) ⊔S ((B +S B) +S ((-S A) +S (-S B)))
                              ≡ₛ⟨ ctxtₛ
                                    (● ⊔C (CC ((B +S B) +S ((-S A) +S (-S B)))))
                                    (beginₛ
                                      A +S (-S B)
                                        ≡ₛ⟨ ctxtₛ
                                              (● -C (CC B))
                                              (symₛ neutral-+S) ⟩
                                      (A +S botAG) -S B
                                        ≡ₛ⟨ ctxtₛ
                                              (((CC A) +C ●) -C (CC B))
                                              (symₛ opp-+S) ⟩
                                      (A +S (A -S A)) -S B
                                        ≡ₛ⟨ ctxtₛ
                                              (● -C (CC B))
                                              asso-+S ⟩
                                      ((A +S A) -S A) -S B
                                        ≡ₛ⟨ symₛ asso-+S ⟩
                                      (A +S A) +S ((-S A) -S B) ∎ₛ) ⟩
                            ((A +S A) +S ((-S A) +S (-S B))) ⊔S ((B +S B) +S ((-S A) +S (-S B)))
                              ≡ₛ⟨ symₛ ⊔S-+S ⟩
                            ((A +S A) ⊔S (B +S B)) +S ((-S A) +S (-S B))
                              ≡ₛ⟨ ctxtₛ
                                    ((CC ((A +S A) ⊔S (B +S B))) +C ●)
                                    (symₛ -S-distri) ⟩
                            ((A +S A) ⊔S (B +S B)) -S (A +S B) ∎ₛ)
                          0≤abs))
                      (transₛ commu-+S neutral-+S)))) ⟩
        (A +S B) ⊔S ((2 *S A) ⊔S (2 *S B))
          ≡ₛ⟨ commu-⊔S ⟩
        ((2 *S A) ⊔S (2 *S B)) ⊔S (A +S B)
          ≡ₛ⟨ symₛ asso-⊔S ⟩
        (2 *S A) ⊔S ((2 *S B) ⊔S (A +S B))
          ≡ₛ⟨ ctxtₛ
                ((CC (2 *S A)) ⊔C ●)
                commu-⊔S ⟩
        (2 *S A) ⊔S ((A +S B) ⊔S (2 *S B))
          ≡ₛ⟨ ctxtₛ
                ((CC (2 *S A)) ⊔C (● ⊔C (CC (2 *S B))))
                (symₛ
                  (⊓S-⊔S
                    ≤S-refl)) ⟩
        (2 *S A) ⊔S (((A +S B) ⊔S ((A +S B))) ⊔S (2 *S B))
          ≡ₛ⟨ ctxtₛ
                ((CC (2 *S A)) ⊔C ●)
                (symₛ asso-⊔S) ⟩
        (2 *S A) ⊔S ((A +S B) ⊔S ((A +S B) ⊔S (2 *S B)))
          ≡ₛ⟨ asso-⊔S ⟩
        ((2 *S A) ⊔S (A +S B)) ⊔S ((A +S B) ⊔S (2 *S B))
          ≡ₛ⟨ ctxtₛ
                (((CC (2 *S A)) ⊔C ●) ⊔C (CC ((A +S B) ⊔S (2 *S B))))
                commu-+S ⟩
        ((2 *S A) ⊔S (B +S A)) ⊔S ((A +S B) ⊔S (2 *S B))
          ≡ₛ⟨ ctxtₛ
                (● ⊔C (CC ((A +S B) ⊔S (2 *S B))))
                (symₛ ⊔S-+S) ⟩
        ((A ⊔S B) +S A) ⊔S ((A +S B) ⊔S (2 *S B))
          ≡ₛ⟨ ctxtₛ
                ((CC ((A ⊔S B) +S A)) ⊔C ●)
                (symₛ ⊔S-+S) ⟩
        ((A ⊔S B) +S A) ⊔S ((A ⊔S B) +S B)
          ≡ₛ⟨ ctxtₛ
                ((CC ((A ⊔S B) +S A)) ⊔C ●)
                commu-+S ⟩
        ((A ⊔S B) +S A) ⊔S (B +S (A ⊔S B))
          ≡ₛ⟨ ctxtₛ
                (● ⊔C (CC (B +S (A ⊔S B))))
                commu-+S ⟩
        (A +S (A ⊔S B)) ⊔S (B +S (A ⊔S B))
          ≡ₛ⟨ symₛ ⊔S-+S ⟩
        (2 *S (A ⊔S B)) ∎ₛ)

  *S-distri-⊓S :
    {A B : Term} ->
    2 *S (A ⊓S B) ≡ₛ (2 *S A) ⊓S (2 *S B)
  *S-distri-⊓S {A} {B} =
    beginₛ
      2 *S (A ⊓S B)
        ≡ₛ⟨ symₛ -S--S ⟩
      -S (-S (2 *S (A ⊓S B)))
        ≡ₛ⟨ ctxtₛ
              (-C ●)
              (symₛ (*S--S 2)) ⟩
      -S (2 *S (-S (A ⊓S B)))
        ≡ₛ⟨ ctxtₛ
              (-C (● +C ●))
              -S-⊓S-⊔S ⟩
      -S (2 *S ((-S A) ⊔S (-S B)))
        ≡ₛ⟨ ctxtₛ
              (-C ●)
              *S-distri-⊔S ⟩
      -S ((2 *S (-S A)) ⊔S (2 *S (-S B)))
        ≡ₛ⟨ ctxtₛ
              (-C (● ⊔C (CC (2 *S (-S B)))))
              (symₛ -S-distri) ⟩
      -S ((-S (2 *S A)) ⊔S (2 *S (-S B)))
        ≡ₛ⟨ ctxtₛ
              (-C ((CC (-S (2 *S A))) ⊔C ●))
              (symₛ -S-distri) ⟩
      -S ((-S (2 *S A)) ⊔S (-S (2 *S B)))
        ≡ₛ⟨ -S-⊔S-⊓S ⟩
      (-S (-S (2 *S A))) ⊓S (-S (-S (2 *S B)))
        ≡ₛ⟨ ctxtₛ
              (● ⊓C (-C (-C (2 *C (CC B)))))
              -S--S ⟩
      (2 *S A) ⊓S (-S (-S (2 *S B)))
        ≡ₛ⟨ ctxtₛ
              ((2 *C (CC A)) ⊓C ●)
              -S--S ⟩
      (2 *S A) ⊓S (2 *S B) ∎ₛ

  mean-≤S-⊔S :
    {A B : Term} ->
    A +S B ≤S 2 *S (A ⊔S B)
  mean-≤S-⊔S {A} {B} =
    ≤S-trans
      {B = A +S (A ⊔S B)}
      (A≤B=>C≤D=>A+C≤B+D
        ≤S-refl
        (≤S-cong-r
          {B = B ⊔S A}
          commu-⊔S
          ≤S-⊔S))
      (≤S-+S
        ≤S-⊔S)

  absA=A⁺+A⁻ :
    {A : Term} ->
    abs A ≡ₛ (A ⁺) +S (A ⁻)
  absA=A⁺+A⁻ {A} =
    beginₛ
      abs A
        ≡ₛ⟨ reflₛ ⟩
      A ⊔S (-S A)
        ≡ₛ⟨ ctxtₛ
              (● ⊔C (CC (-S A)))
              (symₛ neutral-+S) ⟩
      (A +S botAG) ⊔S (-S A)
        ≡ₛ⟨ ctxtₛ
              ((CC A +C ●) ⊔C (CC (-S A)))
              (symₛ opp-+S) ⟩
      (A +S (A -S A)) ⊔S (-S A)
        ≡ₛ⟨ ctxtₛ
              (● ⊔C (CC (-S A)))
              asso-+S ⟩
      ((A +S A) -S A) ⊔S (-S A)
        ≡ₛ⟨ ctxtₛ
              ((CC ((A +S A) -S A)) ⊔C ●)
              (transₛ
                (symₛ neutral-+S)
                commu-+S) ⟩
      ((A +S A) -S A) ⊔S (botAG -S A)
        ≡ₛ⟨ symₛ ⊔S-+S ⟩
      ((2 *S A) ⊔S botAG) -S A
        ≡ₛ⟨ ctxtₛ
              (● -C (CC A))
              (beginₛ
                (A +S A) ⊔S botAG
                  ≡ₛ⟨ ctxtₛ
                        ((CC (2 *S A)) ⊔C ●)
                        (symₛ neutral-+S) ⟩
                (2 *S A) ⊔S (2 *S botAG)
                  ≡ₛ⟨ symₛ *S-distri-⊔S ⟩
                2 *S (A ⁺) ∎ₛ) ⟩
      (2 *S (A ⁺)) -S A
        ≡ₛ⟨ symₛ asso-+S ⟩
      (A ⁺) +S ((A ⁺) -S A)
        ≡ₛ⟨ ctxtₛ
              (CC (A ⁺) +C ●)
              (symₛ
                (A+C=B=>A=B-C
                  (transₛ
                    commu-+S
                    (symₛ
                      (A-C=B=>A=B+C
                        (symₛ A=A⁺-A⁻)))))) ⟩
      (A ⁺) +S (A ⁻) ∎ₛ

  A⁺≤absA :
    {A : Term} ->
    (A ⁺) ≤S abs A
  A⁺≤absA {A} =
    ≤S-cong-l
      {A = (A ⁺) +S botAG}
      neutral-+S
      (≤S-cong-r
        {B = (A ⁺) +S (A ⁻)}
        (symₛ absA=A⁺+A⁻)
        (A≤B=>C≤D=>A+C≤B+D
          ≤S-refl
          (≤S-cong-r
            {B = botAG ⊔S (-S A)}
            commu-⊔S
            ≤S-⊔S)))

  A⁻≤absA :
    {A : Term} ->
    (A ⁻) ≤S abs A
  A⁻≤absA {A} =
    ≤S-cong-l
      {A = botAG +S (A ⁻)}
      (transₛ commu-+S neutral-+S)
      (≤S-cong-r
        {B = (A ⁺) +S (A ⁻)}
        (symₛ absA=A⁺+A⁻)
        (A≤B=>C≤D=>A+C≤B+D
          (≤S-cong-r
            {B = botAG ⊔S A}
            commu-⊔S
            ≤S-⊔S)
          ≤S-refl))

  absA=0=>A=0 :
    {A : Term} ->
    (absA=0 : abs A ≡ₛ botAG) ->
    A ≡ₛ botAG
  absA=0=>A=0 {A} absA=0 =
    transₛ
      A=A⁺-A⁻
      (transₛ
        (ctxtₛ
          (● -C (CC (A ⁻)))
          (≤S-antisym
            (≤S-cong-r
              {B = abs A}
              absA=0
              A⁺≤absA)
            (≤S-cong-r
              {B = botAG ⊔S A}
              commu-⊔S
              ≤S-⊔S)))
        (transₛ
          (ctxtₛ
            (botC -C ●)
            (≤S-antisym
              (≤S-cong-r
                {B = abs A}
                absA=0
                A⁻≤absA)
              (≤S-cong-r
                {B = botAG ⊔S (-S A)}
                commu-⊔S
                ≤S-⊔S)))
          opp-+S))

  A⊓-SA≤0 :
    {A : Term} ->
    A ⊓S (-S A) ≤S botAG
  A⊓-SA≤0 {A} =
    ≤S-cong-r
      {B = -S botAG}
      (symₛ -S-botAG)
      (≤S-cong-l
        {A = -S (A ⊔S (-S A))}
        (beginₛ
          -S (A ⊔S (-S A))
            ≡ₛ⟨ -S-⊔S-⊓S ⟩
          (-S A) ⊓S (-S (-S A))
            ≡ₛ⟨ ctxtₛ
                  (CC (-S A) ⊓C ●)
                  -S--S ⟩
          (-S A) ⊓S A
            ≡ₛ⟨ commu-⊓S ⟩
          A ⊓S (-S A) ∎ₛ)
        (≤S--S
          0≤abs))

  2A=0=>A=0 :
    {A : Term} ->
    (2A=0 : 2 *S A ≡ₛ botAG) ->
    A ≡ₛ botAG
  2A=0=>A=0 {A} 2A=0 =
    absA=0=>A=0
      (≤S-antisym
        (≤S-cong-l
          {A = A ⊓S (-S A)}
          (beginₛ
            A ⊓S (-S A)
              ≡ₛ⟨ ctxtₛ
                    ((CC A) ⊓C ●)
                    (symₛ A=-A) ⟩
            A ⊓S A
              ≡ₛ⟨ ≤S-refl ⟩
            A
              ≡ₛ⟨ symₛ
                    (⊓S-⊔S
                      ≤S-refl) ⟩
            A ⊔S A
              ≡ₛ⟨ ctxtₛ
                    ((CC A) ⊔C ●)
                    A=-A ⟩
            A ⊔S (-S A) ∎ₛ)
          A⊓-SA≤0)
        0≤abs)
    where
    A=-A : A ≡ₛ -S A
    A=-A = 
      beginₛ
        A
          ≡ₛ⟨ A+C=B=>A=B-C
                2A=0 ⟩
        botAG -S A
          ≡ₛ⟨ commu-+S ⟩
        (-S A) +S botAG
          ≡ₛ⟨ neutral-+S ⟩
        -S A ∎ₛ

  2A=2B=>A=B :
    {A B : Term} ->
    (2A=2B : 2 *S A ≡ₛ 2 *S B) ->
    A ≡ₛ B
  2A=2B=>A=B {A} {B} 2A=2B =
    beginₛ
      A
        ≡ₛ⟨ A-C=B=>A=B+C
              (2A=0=>A=0
                (beginₛ
                  2 *S (A -S B)
                    ≡ₛ⟨ symₛ asso-+S ⟩
                  A +S ((-S B) +S (A -S B))
                    ≡ₛ⟨ ctxtₛ
                          ((CC A) +C ●)
                          commu-+S ⟩
                  A +S ((A -S B) -S B)
                    ≡ₛ⟨ ctxtₛ
                          ((CC A) +C ●)
                          (symₛ asso-+S) ⟩
                  A +S (A +S ((-S B) -S B))
                    ≡ₛ⟨ asso-+S ⟩
                  (A +S A) +S ((-S B) -S B)
                    ≡ₛ⟨ ctxtₛ
                          ((CC (2 *S A)) +C ●)
                          (symₛ -S-distri) ⟩
                  (2 *S A) -S (2 *S B)
                    ≡ₛ⟨ symₛ
                          (A+C=B=>A=B-C
                            (beginₛ
                              botAG +S (B +S B)
                                ≡ₛ⟨ commu-+S ⟩
                              (B +S B) +S botAG
                                ≡ₛ⟨ neutral-+S ⟩
                              B +S B
                                ≡ₛ⟨ symₛ 2A=2B ⟩
                              A +S A ∎ₛ)) ⟩
                  botAG ∎ₛ)) ⟩
      botAG +S B
        ≡ₛ⟨ commu-+S ⟩
      B +S botAG
        ≡ₛ⟨ neutral-+S ⟩
      B ∎ₛ

  2A≤2B=>A≤B :
    {A B : Term} ->
    (2A≤2B : (2 *S A) ≤S (2 *S B)) ->
    A ≤S B
  2A≤2B=>A≤B {A} {B} 2A≤2B =
    2A=2B=>A=B
      (transₛ
        *S-distri-⊓S
        2A≤2B)

  A+B⁻≤A⁻+B⁻ :
    {A B : Term} ->
    (A +S B) ⁻ ≤S (A ⁻) +S (B ⁻)
  A+B⁻≤A⁻+B⁻ {A} {B} =
    ⊔S-≤S
      (≤S-cong-l
        (symₛ -S-distri)
        (A≤B=>C≤D=>A+C≤B+D
          ≤S-⊔S
          ≤S-⊔S))
      (≤S-cong-l
        neutral-+S
        (A≤B=>C≤D=>A+C≤B+D
          bot-≤S-⁻
          bot-≤S-⁻))
-- Proposition max-distri-min : forall f g h, (f ⊓ g) ⊔ (f ⊓ h) = (g ⊔ h) ⊓ f.

-- Proposition -S-neg-leq-id-leq-pos : forall f, (-- negF f) ≤ f ≤ posF f.

-- Proposition leq-iff-pos-leq-and-leq-neg : forall f g, f ≤ g <-> (posF f ≤ posF g) /\ (negF g ≤ negF f).

-- Proposition max--S-min-eq-abs : forall f g, f ⊔ g -- f ⊓ g = |f -- g|.

-- Proposition def-max-2 : forall f g, 2 ** f ⊔ g = (f +S+S g)  +S+S |f -- g|.

-- Proposition basic-inequality : forall f, f ⊓ (-- f) = bot <->  f = bot .
  
-- Proposition bot-leq-id-implies-abs-eq-id : forall f, bot ≤ f -> | f | = f.
