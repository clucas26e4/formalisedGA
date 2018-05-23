module Nat where
  
  open import Data.Nat public
  open import Data.Nat.Properties public
  open import Equality
  open import Data.Empty
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Induction.WellFounded


  notSucEqZero : {k : ℕ} -> ¬ (suc k ≡ zero)
  notSucEqZero {k} = λ { ()}

  a=a+0 :
    {a : ℕ} ->
    a ≡ a + 0
--{{{
  a=a+0 {zero} =
    refl
  a=a+0 {suc a} =
    cong suc a=a+0
--}}}
    
  sa+b=a+sb :
    {a b : ℕ} ->
    suc (a + b) ≡ a + suc b
--{{{
  sa+b=a+sb {zero} {b} =
    refl
  sa+b=a+sb {suc a} {b} =
    cong suc (sa+b=a+sb {a} {b})
--}}}

  commu-+ :
    {a b : ℕ} ->
    a + b ≡ b + a
--{{{
  commu-+ {zero} {b} =
    a=a+0
  commu-+ {suc a} {b} =
    trans
      (cong suc (commu-+ {a} {b}))
      (sa+b=a+sb {b} {a})
--}}}

  ¬sk≤k :
    {k : ℕ} ->
    ¬ (suc k ≤ k)
--{{{
  ¬sk≤k {zero} ()
  ¬sk≤k {suc k} (s≤s sk≤k) =
    ¬sk≤k sk≤k
--}}}

  injSuc :
    {a b : ℕ} ->
    suc a ≡ suc b ->
    a ≡ b
--{{{
  injSuc refl =
    refl
--}}}

  _≡?_ :
    (a b : ℕ) ->
    Dec (a ≡ b)
--{{{
  zero ≡? zero =
    yes refl
  zero ≡? suc b = 
    no λ { ()}
  suc a ≡? zero = 
    no λ { ()}
  suc a ≡? suc b with a ≡? b
  suc a ≡? suc b | yes p =
    yes (cong suc p)
  suc a ≡? suc b | no ¬p =
    no λ x → ¬p (injSuc x)
--}}}

  k≤sk :
    {k : ℕ} ->
    k ≤ suc k
--{{{
  k≤sk {zero} =
    z≤n
  k≤sk {suc k} =
    s≤s k≤sk
--}}}

  ¬k<k'=>k'≤k :
    {k k' : ℕ} ->
    ¬ k < k' ->
    k' ≤ k
--{{{
  ¬k<k'=>k'≤k {zero} {zero} ¬k<k' =
    z≤n
  ¬k<k'=>k'≤k {zero} {suc k'} ¬k<k' =
    ⊥-elim (¬k<k' (s≤s z≤n))
  ¬k<k'=>k'≤k {suc k} {zero} ¬k<k' =
    z≤n
  ¬k<k'=>k'≤k {suc k} {suc k'} ¬k<k' =
    s≤s (¬k<k'=>k'≤k λ x → ¬k<k' (s≤s x))
--}}}


  k≤k'=>k⊔k'=k' :
    {k k' : ℕ} ->
    (k≤k' : k ≤ k') ->
    k ⊔ k' ≡ k'
--{{{
  k≤k'=>k⊔k'=k' {zero} {zero} k≤k' =
    refl
  k≤k'=>k⊔k'=k' {zero} {suc k'} k≤k' =
    refl
  k≤k'=>k⊔k'=k' {suc k} {zero} ()
  k≤k'=>k⊔k'=k' {suc k} {suc k'} (s≤s k≤k') =
    cong suc (k≤k'=>k⊔k'=k' k≤k')
--}}}

  cong-≤-l :
    {k k' k'' : ℕ} ->
    (k=k' : k ≡ k') ->
    (k≤k'' : k ≤ k'') ->
    k' ≤ k''
--{{{
  cong-≤-l refl k≤k'' =
    k≤k''
--}}}

  cong-≤-r :
    {k k' k'' : ℕ} ->
    (k=k' : k ≡ k') ->
    (k≤k'' : k'' ≤ k) ->
    k'' ≤ k'
--{{{
  cong-≤-r refl k''≤k =
    k''≤k
--}}}


  ⊔-≤ :
    {a b c : ℕ} ->
    a ≤ c ->
    b ≤ c ->
    a ⊔ b ≤ c
--{{{
  ⊔-≤ {zero} {zero} {zero} a≤c b≤c =
    ≤-refl
  ⊔-≤ {zero} {suc b} {zero} a≤c ()
  ⊔-≤ {suc a} {b} {zero} () b≤c
  ⊔-≤ {zero} {zero} {suc c} a≤c b≤c =
    z≤n
  ⊔-≤ {zero} {suc b} {suc c} a≤c b≤c =
    b≤c
  ⊔-≤ {suc a} {zero} {suc c} a≤c b≤c =
    a≤c
  ⊔-≤ {suc a} {suc b} {suc c} (s≤s a≤c) (s≤s b≤c) =
    s≤s (⊔-≤ a≤c b≤c)
--}}}

  ≤-⊔ :
    {a b : ℕ} ->
    a ≤ a ⊔ b
--{{{
  ≤-⊔ {zero} {b} =
    z≤n
  ≤-⊔ {suc a} {zero} =
    ≤-refl
  ≤-⊔ {suc a} {suc b} =
    s≤s ≤-⊔
--}}}

  ¬a⊔b=a=>a⊔b=b :
    {a b : ℕ} ->
    ¬ (a ⊔ b ≡ a) ->
    a ⊔ b ≡ b
--{{{
  ¬a⊔b=a=>a⊔b=b {zero} {zero} ¬a⊔b=a =
    ⊥-elim (¬a⊔b=a refl)
  ¬a⊔b=a=>a⊔b=b {zero} {suc b} ¬a⊔b=a =
    refl
  ¬a⊔b=a=>a⊔b=b {suc a} {zero} ¬a⊔b=a =
    ⊥-elim (¬a⊔b=a refl)
  ¬a⊔b=a=>a⊔b=b {suc a} {suc b} ¬a⊔b=a =
    cong suc (¬a⊔b=a=>a⊔b=b {a} {b} λ x → ¬a⊔b=a (cong suc x))
--}}}

  a≤b=>¬a=b=>a<b :
    {a b : ℕ} ->
    a ≤ b ->
    ¬ (a ≡ b) ->
    a < b
  a≤b=>¬a=b=>a<b {zero} {zero} a≤b ¬a=b =
    ⊥-elim (¬a=b refl)
  a≤b=>¬a=b=>a<b {zero} {suc b} a≤b ¬a=b =
    s≤s z≤n
  a≤b=>¬a=b=>a<b {suc a} {zero} () ¬a=b
  a≤b=>¬a=b=>a<b {suc a} {suc b} (s≤s a≤b) ¬a=b =
    s≤s (a≤b=>¬a=b=>a<b {a} {b} a≤b (λ x → ¬a=b (cong suc x)))

  sa⊔b=sa⊔sb :
    {a b : ℕ} ->
    suc (a ⊔ b) ≡ (suc a) ⊔ (suc b)
  sa⊔b=sa⊔sb {a} {b} =
    refl

  a≤a+b :
    {a b : ℕ} ->
    a ≤ a + b
  a≤a+b {zero} {zero} =
    ≤-refl
  a≤a+b {zero} {suc b} =
    z≤n
  a≤a+b {suc a} {b} =
    s≤s a≤a+b

  a≤b=>c≤d=>a+c≤b+d :
    {a b c d : ℕ} ->
    a ≤ b ->
    c ≤ d ->
    a + c ≤ b + d
  a≤b=>c≤d=>a+c≤b+d z≤n z≤n =
    z≤n
  a≤b=>c≤d=>a+c≤b+d {.0} {b} {suc c} {suc d} z≤n (s≤s c≤d) =
    cong-≤-r
      {suc (b + d)}
      (sa+b=a+sb {b} {d})
      (s≤s (a≤b=>c≤d=>a+c≤b+d {0} {b} z≤n c≤d))
  a≤b=>c≤d=>a+c≤b+d (s≤s a≤b) c≤d =
    s≤s (a≤b=>c≤d=>a+c≤b+d a≤b c≤d)

  k<k'=>¬k=k' :
    {k k' : ℕ} ->
    k < k' ->
    ¬ k ≡ k'
  k<k'=>¬k=k' {zero} {zero} () x
  k<k'=>¬k=k' {zero} {suc k'} k<k' ()
  k<k'=>¬k=k' {suc k} {zero} () x
  k<k'=>¬k=k' {suc k} {suc k'} (s≤s k<k') x =
    k<k'=>¬k=k' k<k' (injSuc x)

  a-b≤a :
    (a b : ℕ) ->
    a ∸ b ≤ a
  a-b≤a zero zero =
    z≤n
  a-b≤a zero (suc b) =
    z≤n
  a-b≤a (suc a) zero =
    ≤-refl
  a-b≤a (suc a) (suc b) =
    ≤-trans
      (a-b≤a a b)
      k≤sk

  a≤b=>c-b≤c-a :
    {a b : ℕ} ->
    (c : ℕ) ->
    (a≤b : a ≤ b) ->
    (c ∸ b) ≤ (c ∸ a)
  a≤b=>c-b≤c-a {zero} {zero} zero a≤b =
    z≤n
  a≤b=>c-b≤c-a {zero} {zero} (suc c) a≤b =
    ≤-refl
  a≤b=>c-b≤c-a {zero} {suc b} zero a≤b =
    z≤n
  a≤b=>c-b≤c-a {zero} {suc b} (suc c) a≤b = 
    ≤-trans
      (a-b≤a c b)
      k≤sk
  a≤b=>c-b≤c-a {suc a} {zero} c ()
  a≤b=>c-b≤c-a {suc a} {suc b} zero a≤b =
    z≤n
  a≤b=>c-b≤c-a {suc a} {suc b} (suc c) (s≤s a≤b) =
    a≤b=>c-b≤c-a c a≤b

  a≤b=>a-c≤b-c :
   {a b : ℕ} ->
   (c : ℕ) ->
   (a≤b : a ≤ b) ->
   a ∸ c ≤ b ∸ c
  a≤b=>a-c≤b-c {zero} {zero} zero a≤b =
    z≤n
  a≤b=>a-c≤b-c {zero} {zero} (suc c) a≤b =
    z≤n
  a≤b=>a-c≤b-c {zero} {suc b} zero a≤b =
    z≤n
  a≤b=>a-c≤b-c {zero} {suc b} (suc c) a≤b =
    z≤n
  a≤b=>a-c≤b-c {suc a} {zero} c ()
  a≤b=>a-c≤b-c {suc a} {suc b} zero a≤b =
    a≤b
  a≤b=>a-c≤b-c {suc a} {suc b} (suc c) (s≤s a≤b) =
    a≤b=>a-c≤b-c c a≤b

  a<b=>a≤b :
    {a b : ℕ} ->
    a < b ->
    a ≤ b
  a<b=>a≤b a<b =
    ≤-trans
      k≤sk
      a<b

  ¬a≤b=>b<a :
    {a b : ℕ} ->
    ¬ (a ≤ b) ->
    b < a
  ¬a≤b=>b<a {zero} {b} ¬a≤b =
    ⊥-elim (¬a≤b z≤n)
  ¬a≤b=>b<a {suc a} {zero} ¬a≤b =
    s≤s z≤n
  ¬a≤b=>b<a {suc a} {suc b} ¬a≤b =
    s≤s (¬a≤b=>b<a {a} {b} (λ x → ¬a≤b (s≤s x)))

  a⊔b⊔c=0=>a⊔b=0 :
    {a b c : ℕ} ->
    a ⊔ b ⊔ c ≡ 0 ->
    a ⊔ b ≡ 0
  a⊔b⊔c=0=>a⊔b=0 {zero} {zero} {c} eq =
    refl
  a⊔b⊔c=0=>a⊔b=0 {zero} {suc b} {zero} eq =
    ⊥-elim
      (notSucEqZero eq)
  a⊔b⊔c=0=>a⊔b=0 {zero} {suc b} {suc c} eq =
    ⊥-elim
      (notSucEqZero eq)
  a⊔b⊔c=0=>a⊔b=0 {suc a} {zero} {zero} eq = 
    ⊥-elim
      (notSucEqZero eq)
  a⊔b⊔c=0=>a⊔b=0 {suc a} {zero} {suc c} eq = 
    ⊥-elim
      (notSucEqZero eq)
  a⊔b⊔c=0=>a⊔b=0 {suc a} {suc b} {zero} eq = 
    ⊥-elim
      (notSucEqZero eq)
  a⊔b⊔c=0=>a⊔b=0 {suc a} {suc b} {suc c} eq = 
    ⊥-elim
      (notSucEqZero eq)

  a⊔b=0=>a⊔b⊔b=0 :
    {a b : ℕ} ->
    a ⊔ b ≡ 0 ->
    a ⊔ b ⊔ b ≡ 0
  a⊔b=0=>a⊔b⊔b=0 {zero} {zero} eq =
    refl
  a⊔b=0=>a⊔b⊔b=0 {zero} {suc b} eq = 
    ⊥-elim
      (notSucEqZero eq)
  a⊔b=0=>a⊔b⊔b=0 {suc a} {zero} eq = 
    ⊥-elim
      (notSucEqZero eq)
  a⊔b=0=>a⊔b⊔b=0 {suc a} {suc b} eq = 
    ⊥-elim
      (notSucEqZero eq)

  a⊔b⊔c=0=>a⊔b+c=0 :
    {a b c : ℕ} ->
    a ⊔ b ⊔ c ≡ 0 ->
    a ⊔ (b + c) ≡ 0
  a⊔b⊔c=0=>a⊔b+c=0 {zero} {zero} {zero} eq =
    refl
  a⊔b⊔c=0=>a⊔b+c=0 {zero} {zero} {suc c} eq = 
    ⊥-elim
      (notSucEqZero eq)
  a⊔b⊔c=0=>a⊔b+c=0 {zero} {suc b} {zero} eq = 
    ⊥-elim
      (notSucEqZero eq)
  a⊔b⊔c=0=>a⊔b+c=0 {zero} {suc b} {suc c} eq = 
    ⊥-elim
      (notSucEqZero eq)
  a⊔b⊔c=0=>a⊔b+c=0 {suc a} {zero} {zero} eq = 
    ⊥-elim
      (notSucEqZero eq)
  a⊔b⊔c=0=>a⊔b+c=0 {suc a} {zero} {suc c} eq = 
    ⊥-elim
      (notSucEqZero eq)
  a⊔b⊔c=0=>a⊔b+c=0 {suc a} {suc b} {zero} eq = 
    ⊥-elim
      (notSucEqZero eq)
  a⊔b⊔c=0=>a⊔b+c=0 {suc a} {suc b} {suc c} eq = 
    ⊥-elim
      (notSucEqZero eq)

  a⊔b=0=>a+b=0 :
    {a b : ℕ} ->
    a ⊔ b ≡ 0 ->
    a + b ≡ 0
  a⊔b=0=>a+b=0 {zero} {zero} eq =
    refl
  a⊔b=0=>a+b=0 {zero} {suc b} eq = 
    ⊥-elim
      (notSucEqZero eq)
  a⊔b=0=>a+b=0 {suc a} {zero} eq = 
    ⊥-elim
      (notSucEqZero eq)
  a⊔b=0=>a+b=0 {suc a} {suc b} eq = 
    ⊥-elim
      (notSucEqZero eq)


  --
  --
  -- Recursion on <
  --
  --
  ℕ-acc-Fun :
    (a b : ℕ) ->
    a < b ->
    Acc _<_ a
--{{{
  ℕ-acc-Fun a zero ()
  ℕ-acc-Fun zero (suc b) a<b =
    acc λ { y ()}
  ℕ-acc-Fun (suc a) (suc b) (s≤s a<b) =
    acc λ y x → ℕ-acc-Fun y b (≤-trans x a<b)

  ℕ-acc :
    (a : ℕ) ->
    Acc _<_ a
  ℕ-acc a =
    acc λ y x -> ℕ-acc-Fun y a x
--}}}
    
