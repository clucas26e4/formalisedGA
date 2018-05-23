module Syntax.ListTerm.Canonic where
  
  {- STDLIB -}
  open import Nat
  open import Equality
  open import Data.Empty
  open import Relation.Nullary
  
  {- Syntax -}
  open import Syntax.Term
  open import Syntax.ListTerm
  open import Syntax.ListTerm.Properties
  
  {- Semantic -}
  open import Semantic.SemEquality
  open import Semantic.SemEquality.Properties
  open import Semantic.Interpretation

  insertCanonic :
    (Γ : ListTerm) ->
    nbOpListFor Γ ≡ 0 ->
    ℕ ->
    ListTerm
  insertCanonic [] opΓ=0 k =
    [] ∷ varAG k
  insertCanonic (Γ ∷ varAG x) opΓ=0 k with k ≤? x
  insertCanonic (Γ ∷ varAG x) opΓ=0 k | yes p =
    (insertCanonic Γ opΓ=0 k) ∷ (varAG x)
  insertCanonic (Γ ∷ varAG x) opΓ=0 k | no ¬p =
    Γ ∷ varAG x ∷ varAG k
  insertCanonic (Γ ∷ botAG) opΓ=0 k =
    ⊥-elim (notSucEqZero opΓ=0)
  insertCanonic (Γ ∷ (A ⊔S A₁)) opΓ=0 k = 
    ⊥-elim (notSucEqZero opΓ=0)
  insertCanonic (Γ ∷ (A +S A₁)) opΓ=0 k = 
    ⊥-elim (notSucEqZero opΓ=0)
  insertCanonic (Γ ∷ (A ⊓S A₁)) opΓ=0 k = 
    ⊥-elim (notSucEqZero opΓ=0)
  insertCanonic (Γ ∷ (-S A)) opΓ=0 k = 
    ⊥-elim (notSucEqZero opΓ=0)

  insertCanonicKeepOp : 
    (Γ : ListTerm) ->
    (opΓ=0 : nbOpListFor Γ ≡ 0) ->
    (k : ℕ) ->
    nbOpListFor (insertCanonic Γ opΓ=0 k) ≡ 0
  insertCanonicKeepOp [] opΓ=0 k =
    refl
  insertCanonicKeepOp (Γ ∷ varAG x) opΓ=0 k with k ≤? x
  insertCanonicKeepOp (Γ ∷ varAG x) opΓ=0 k | yes p =
    insertCanonicKeepOp Γ opΓ=0 k 
  insertCanonicKeepOp (Γ ∷ varAG x) opΓ=0 k | no ¬p =
    opΓ=0
  insertCanonicKeepOp (Γ ∷ botAG) opΓ=0 k = 
      ⊥-elim (notSucEqZero opΓ=0)
  insertCanonicKeepOp (Γ ∷ (A ⊔S A₁)) opΓ=0 k = 
      ⊥-elim (notSucEqZero opΓ=0)
  insertCanonicKeepOp (Γ ∷ (A +S A₁)) opΓ=0 k = 
      ⊥-elim (notSucEqZero opΓ=0)
  insertCanonicKeepOp (Γ ∷ (A ⊓S A₁)) opΓ=0 k = 
      ⊥-elim (notSucEqZero opΓ=0)
  insertCanonicKeepOp (Γ ∷ (-S A)) opΓ=0 k = 
      ⊥-elim (notSucEqZero opΓ=0)

  insertCanonicDoExchange :
    (Γ : ListTerm) ->
    (opΓ=0 : nbOpListFor Γ ≡ 0) ->
    (k : ℕ) ->
    ListExchange (Γ ∷ varAG k) (insertCanonic Γ opΓ=0 k)
  insertCanonicDoExchange [] opΓ=0 k =
    idLE
  insertCanonicDoExchange (Γ ∷ varAG x) opΓ=0 k with k ≤? x
  insertCanonicDoExchange (Γ ∷ varAG x) opΓ=0 k | yes p =
    transLE
      {Γ₂ = Γ ∷ varAG k ∷ varAG x}
      (exLE
        idLE)
      (indLE
        (insertCanonicDoExchange Γ opΓ=0 k))
  insertCanonicDoExchange (Γ ∷ varAG x) opΓ=0 k | no ¬p =
    idLE
  insertCanonicDoExchange (Γ ∷ botAG) opΓ=0 k = 
      ⊥-elim (notSucEqZero opΓ=0)
  insertCanonicDoExchange (Γ ∷ (A ⊔S A₁)) opΓ=0 k = 
      ⊥-elim (notSucEqZero opΓ=0)
  insertCanonicDoExchange (Γ ∷ (A +S A₁)) opΓ=0 k = 
      ⊥-elim (notSucEqZero opΓ=0)
  insertCanonicDoExchange (Γ ∷ (A ⊓S A₁)) opΓ=0 k = 
      ⊥-elim (notSucEqZero opΓ=0)
  insertCanonicDoExchange (Γ ∷ (-S A)) opΓ=0 k = 
      ⊥-elim (notSucEqZero opΓ=0)

  mutual
    toCanonic :
      (Γ : ListTerm) ->
      nbOpListFor Γ ≡ 0 ->
      ListTerm
    toCanonic [] opΓ=0 =
      []
    toCanonic (Γ ∷ varAG x) opΓ=0 =
      insertCanonic (toCanonic Γ opΓ=0) (toCanonicKeepOp Γ opΓ=0) x
    toCanonic (Γ ∷ botAG) opΓ=0 = 
      ⊥-elim (notSucEqZero opΓ=0)
    toCanonic (Γ ∷ (A ⊔S A₁)) opΓ=0 = 
      ⊥-elim (notSucEqZero opΓ=0)
    toCanonic (Γ ∷ (A +S A₁)) opΓ=0 = 
      ⊥-elim (notSucEqZero opΓ=0)
    toCanonic (Γ ∷ (A ⊓S A₁)) opΓ=0 = 
      ⊥-elim (notSucEqZero opΓ=0)
    toCanonic (Γ ∷ (-S A)) opΓ=0 = 
      ⊥-elim (notSucEqZero opΓ=0)

    toCanonicKeepOp :
      (Γ : ListTerm) ->
      (opΓ=0 : nbOpListFor Γ ≡ 0) ->
      nbOpListFor (toCanonic Γ opΓ=0) ≡ 0
    toCanonicKeepOp [] opΓ=0 =
      refl
    toCanonicKeepOp (Γ ∷ varAG x) opΓ=0 =
      insertCanonicKeepOp (toCanonic Γ opΓ=0) (toCanonicKeepOp Γ opΓ=0) x
    toCanonicKeepOp (Γ ∷ botAG) opΓ=0 = 
      ⊥-elim (notSucEqZero opΓ=0)
    toCanonicKeepOp (Γ ∷ (A ⊔S A₁)) opΓ=0 = 
      ⊥-elim (notSucEqZero opΓ=0)
    toCanonicKeepOp (Γ ∷ (A +S A₁)) opΓ=0 = 
      ⊥-elim (notSucEqZero opΓ=0)
    toCanonicKeepOp (Γ ∷ (A ⊓S A₁)) opΓ=0 = 
      ⊥-elim (notSucEqZero opΓ=0)
    toCanonicKeepOp (Γ ∷ (-S A)) opΓ=0 = 
      ⊥-elim (notSucEqZero opΓ=0)

  toCanonicDoExchange :
    (Γ : ListTerm) ->
    (opΓ=0 : nbOpListFor Γ ≡ 0) ->
    ListExchange Γ (toCanonic Γ opΓ=0)
  toCanonicDoExchange [] opΓ=0 =
    idLE
  toCanonicDoExchange (Γ ∷ varAG x) opΓ=0 =
    transLE
      {Γ₂ = (toCanonic Γ opΓ=0) ∷ varAG x}
      (indLE
        (toCanonicDoExchange Γ opΓ=0))
      (insertCanonicDoExchange (toCanonic Γ opΓ=0) (toCanonicKeepOp Γ opΓ=0) x)
  toCanonicDoExchange (Γ ∷ botAG) opΓ=0 = 
      ⊥-elim (notSucEqZero opΓ=0)
  toCanonicDoExchange (Γ ∷ (A ⊔S A₁)) opΓ=0 = 
      ⊥-elim (notSucEqZero opΓ=0)
  toCanonicDoExchange (Γ ∷ (A +S A₁)) opΓ=0 = 
      ⊥-elim (notSucEqZero opΓ=0)
  toCanonicDoExchange (Γ ∷ (A ⊓S A₁)) opΓ=0 = 
      ⊥-elim (notSucEqZero opΓ=0)
  toCanonicDoExchange (Γ ∷ (-S A)) opΓ=0 = 
      ⊥-elim (notSucEqZero opΓ=0)

  maxVar :
    ListTerm ->
    ℕ
  maxVar [] =
    0
  maxVar (Γ ∷ varAG k) = (maxVar Γ) ⊔ k
  maxVar (Γ ∷ _) = maxVar Γ

  data Canonic : ListTerm -> Set where
    []Canonic :
      Canonic []
    consCanonic :
      (k : ℕ) ->
      (Γ : ListTerm) ->
      maxVar Γ ≤ k ->
      Canonic Γ ->
      Canonic (Γ ∷ varAG k)

  maxVarCanonic :
    {Γ : ListTerm} ->
    {k : ℕ} ->
    Canonic (Γ ∷ varAG k) ->
    maxVar (Γ ∷ varAG k) ≡ k
  maxVarCanonic {.Γ} {.k} (consCanonic k Γ x canΓ) =
    k≤k'=>k⊔k'=k' x

  notOccurCanonic :
    {Γ : ListTerm} ->
    {k : ℕ} ->
    Canonic (Γ ∷ varAG k) ->
    (k' : ℕ) ->
    k < k' ->
    nbOccurVar (Γ ∷ varAG k) k' ≡ 0
  notOccurCanonic {Γ} {k} canΓ k' k<k' with k ≡? k'
  notOccurCanonic {Γ} {k} canΓ k' k<k' | yes p =
    ⊥-elim (k<k'=>¬k=k' k<k' p)
  notOccurCanonic {[]} {k} canΓ k' k<k' | no ¬p =
    refl
  notOccurCanonic {Γ ∷ varAG x} {.k} (consCanonic k .(Γ ∷ varAG x) x₁ canΓ) k' k<k' | no ¬p =
    notOccurCanonic
      canΓ
      k'
      (≤-trans
        (s≤s
          (cong-≤-l
            {maxVar Γ ⊔ x}
            (maxVarCanonic canΓ)
            x₁))
        k<k') 
  notOccurCanonic {Γ ∷ botAG} {.k} (consCanonic k .(Γ ∷ botAG) x ()) k' k<k' | no ¬p
  notOccurCanonic {Γ ∷ (A ⊔S A₁)} {.k} (consCanonic k .(Γ ∷ (A ⊔S A₁)) x ()) k' k<k' | no ¬p 
  notOccurCanonic {Γ ∷ (A +S A₁)} {.k} (consCanonic k .(Γ ∷ (A +S A₁)) x ()) k' k<k' | no ¬p
  notOccurCanonic {Γ ∷ (A ⊓S A₁)} {.k} (consCanonic k .(Γ ∷ (A ⊓S A₁)) x ()) k' k<k' | no ¬p
  notOccurCanonic {Γ ∷ (-S A)} {.k} (consCanonic k .(Γ ∷ (-S A)) x ()) k' k<k' | no ¬p

  maxVarInsertCanonic :
    (Γ : ListTerm) ->
    (opΓ : nbOpListFor Γ ≡ 0) ->
    (k : ℕ) ->
    maxVar (insertCanonic Γ opΓ k) ≡ (maxVar Γ) ⊔ k
  maxVarInsertCanonic [] opΓ k =
    refl
  maxVarInsertCanonic (Γ ∷ varAG x) opΓ k with k ≤? x
  maxVarInsertCanonic (Γ ∷ varAG x) opΓ k | yes p =
    begin
      maxVar (insertCanonic Γ opΓ k) ⊔ x
        ≡⟨ cong
             (λ y -> y ⊔ x)
             (maxVarInsertCanonic Γ opΓ k) ⟩
      maxVar Γ ⊔ k ⊔ x
        ≡⟨ ⊔-assoc (maxVar Γ) k x ⟩
      maxVar Γ ⊔ (k ⊔ x)
        ≡⟨ cong
             (λ y -> maxVar Γ ⊔ y)
             (⊔-comm k x) ⟩
      maxVar Γ ⊔ (x ⊔ k)
        ≡⟨ sym (⊔-assoc (maxVar Γ) x k) ⟩
      maxVar Γ ⊔ x ⊔ k ∎
  maxVarInsertCanonic (Γ ∷ varAG x) opΓ k | no ¬p =
    refl
  maxVarInsertCanonic (Γ ∷ botAG) opΓ k = 
    ⊥-elim (notSucEqZero opΓ)
  maxVarInsertCanonic (Γ ∷ (A ⊔S A₁)) opΓ k = 
    ⊥-elim (notSucEqZero opΓ)
  maxVarInsertCanonic (Γ ∷ (A +S A₁)) opΓ k = 
    ⊥-elim (notSucEqZero opΓ)
  maxVarInsertCanonic (Γ ∷ (A ⊓S A₁)) opΓ k = 
    ⊥-elim (notSucEqZero opΓ)
  maxVarInsertCanonic (Γ ∷ (-S A)) opΓ k = 
    ⊥-elim (notSucEqZero opΓ)
    
  insertCanonicKeepCanonic :
    (Γ : ListTerm) ->
    (opΓ : nbOpListFor Γ ≡ 0) ->
    (k : ℕ) ->
    Canonic Γ ->
    Canonic (insertCanonic Γ opΓ k)
  insertCanonicKeepCanonic [] opΓ k canΓ =
    consCanonic k [] z≤n []Canonic
  insertCanonicKeepCanonic (Γ ∷ varAG x) opΓ k (consCanonic .x .Γ x₁ canΓ) with k ≤? x
  insertCanonicKeepCanonic (Γ ∷ varAG x) opΓ k (consCanonic .x .Γ x₁ canΓ) | yes p =
    consCanonic
    x
    (insertCanonic Γ opΓ k)
    (cong-≤-l
      {maxVar Γ ⊔ k}
      (sym (maxVarInsertCanonic Γ opΓ k))
      (⊔-≤
        x₁
        p))
    (insertCanonicKeepCanonic Γ opΓ k canΓ)
  insertCanonicKeepCanonic (Γ ∷ varAG x) opΓ k (consCanonic .x .Γ x₁ canΓ) | no ¬p =
    consCanonic
    k
    (Γ ∷ varAG x)
    (cong-≤-l
      {x}
      (sym (k≤k'=>k⊔k'=k' x₁))
      (a<b=>a≤b
        (¬a≤b=>b<a ¬p)))
    (consCanonic
      x
      Γ
      x₁
      canΓ)
  insertCanonicKeepCanonic (Γ ∷ botAG) opΓ k canΓ = 
    ⊥-elim (notSucEqZero opΓ)
  insertCanonicKeepCanonic (Γ ∷ (A ⊔S A₁)) opΓ k canΓ = 
    ⊥-elim (notSucEqZero opΓ)
  insertCanonicKeepCanonic (Γ ∷ (A +S A₁)) opΓ k canΓ = 
    ⊥-elim (notSucEqZero opΓ)
  insertCanonicKeepCanonic (Γ ∷ (A ⊓S A₁)) opΓ k canΓ = 
    ⊥-elim (notSucEqZero opΓ)
  insertCanonicKeepCanonic (Γ ∷ (-S A)) opΓ k canΓ = 
    ⊥-elim (notSucEqZero opΓ)
    

  toCanonicIsCanonic :
    (Γ : ListTerm) ->
    (opΓ : nbOpListFor Γ ≡ 0) ->
    Canonic (toCanonic Γ opΓ)
  toCanonicIsCanonic [] opΓ =
    []Canonic
  toCanonicIsCanonic (Γ ∷ varAG x) opΓ =
    insertCanonicKeepCanonic
      (toCanonic Γ opΓ)
      (toCanonicKeepOp Γ opΓ)
      x
      (toCanonicIsCanonic Γ opΓ)
  toCanonicIsCanonic (Γ ∷ botAG) opΓ =
    ⊥-elim (notSucEqZero opΓ)
  toCanonicIsCanonic (Γ ∷ (A ⊔S A₁)) opΓ = 
    ⊥-elim (notSucEqZero opΓ)
  toCanonicIsCanonic (Γ ∷ (A +S A₁)) opΓ = 
    ⊥-elim (notSucEqZero opΓ)
  toCanonicIsCanonic (Γ ∷ (A ⊓S A₁)) opΓ = 
    ⊥-elim (notSucEqZero opΓ)
  toCanonicIsCanonic (Γ ∷ (-S A)) opΓ = 
    ⊥-elim (notSucEqZero opΓ)

  sameVar=>sameCanonic :
    (T D : ListTerm) ->
    (canT : Canonic T) ->
    (canD : Canonic D) ->
    ((k : ℕ) -> nbOccurVar T k ≡ nbOccurVar D k) ->
    T ≡ D
  sameVar=>sameCanonic .[] .[] []Canonic []Canonic sameVar =
    refl
  sameVar=>sameCanonic .[] .(Γ ∷ varAG k) []Canonic (consCanonic k Γ x canD) sameVar with sameVar k
  sameVar=>sameCanonic .[] .(Γ ∷ varAG k) []Canonic (consCanonic k Γ x canD) sameVar | 0=suc with k ≡? k
  sameVar=>sameCanonic .[] .(Γ ∷ varAG k) []Canonic (consCanonic k Γ x canD) sameVar | 0=suc | yes p =
    ⊥-elim (notSucEqZero (sym 0=suc))
  sameVar=>sameCanonic .[] .(Γ ∷ varAG k) []Canonic (consCanonic k Γ x canD) sameVar | 0=suc | no ¬p =
    ⊥-elim (¬p refl)
  sameVar=>sameCanonic .(Γ ∷ varAG k) .[] (consCanonic k Γ x canT) []Canonic sameVar with sameVar k
  sameVar=>sameCanonic .(Γ ∷ varAG k) .[] (consCanonic k Γ x canD) []Canonic sameVar | 0=suc with k ≡? k
  sameVar=>sameCanonic .(Γ ∷ varAG k) .[] (consCanonic k Γ x canD) []Canonic sameVar | 0=suc | yes p =
    ⊥-elim (notSucEqZero 0=suc)
  sameVar=>sameCanonic .(Γ ∷ varAG k) .[] (consCanonic k Γ x canD) []Canonic sameVar | 0=suc | no ¬p =
    ⊥-elim (¬p refl)
  sameVar=>sameCanonic .(Γ ∷ varAG k) .(Γ₁ ∷ varAG k₁) (consCanonic k Γ x canT) (consCanonic k₁ Γ₁ x₁ canD) sameVar with k₁ ≡? k
  sameVar=>sameCanonic .(Γ ∷ varAG k) .(Γ₁ ∷ varAG k) (consCanonic .k Γ x canT) (consCanonic k Γ₁ x₁ canD) sameVar | yes refl with sameVar k
  sameVar=>sameCanonic .(Γ ∷ varAG k) .(Γ₁ ∷ varAG k) (consCanonic .k Γ x canT) (consCanonic k Γ₁ x₁ canD) sameVar | yes refl | eq' with k ≡? k
  sameVar=>sameCanonic .(Γ ∷ varAG k) .(Γ₁ ∷ varAG k) (consCanonic .k Γ x canT) (consCanonic k Γ₁ x₁ canD) sameVar | yes refl | eq' | yes p =
    cong
      (λ T' -> T' ∷ varAG k)
      {Γ}
      {Γ₁}
      (sameVar=>sameCanonic
        Γ
        Γ₁
        canT
        canD
        (λ {k' -> nbOccurVarSameHead Γ Γ₁ (varAG k) k' (sameVar k')}))
  sameVar=>sameCanonic .(Γ ∷ varAG k) .(Γ₁ ∷ varAG k) (consCanonic .k Γ x canT) (consCanonic k Γ₁ x₁ canD) sameVar | yes refl | eq' | no ¬p =
    ⊥-elim (¬p refl)
  sameVar=>sameCanonic .(Γ ∷ varAG k) .(Γ₁ ∷ varAG k₁) (consCanonic k Γ x canT) (consCanonic k₁ Γ₁ x₁ canD) sameVar | no ¬p with k <? k₁
  sameVar=>sameCanonic .(Γ ∷ varAG k) .(Γ₁ ∷ varAG k₁) (consCanonic k Γ x canT) (consCanonic k₁ Γ₁ x₁ canD) sameVar | no ¬p | yes p =
    ⊥-elim
      (notSucEqZero
        {nbOccurVar Γ₁ k₁}
        (begin
          suc (nbOccurVar Γ₁ k₁)
            ≡⟨ sym (unfoldNbOccurVar Γ₁ k₁) ⟩
          (nbOccurVar (Γ₁ ∷ varAG k₁) k₁)
            ≡⟨ sym (sameVar k₁) ⟩
          (nbOccurVar (Γ ∷ varAG k) k₁)
            ≡⟨ notOccurCanonic (consCanonic k Γ x canT) k₁ p ⟩
          zero ∎))
  sameVar=>sameCanonic .(Γ ∷ varAG k) .(Γ₁ ∷ varAG k₁) (consCanonic k Γ x canT) (consCanonic k₁ Γ₁ x₁ canD) sameVar | no ¬p | no ¬p₁ with k₁ <? k
  sameVar=>sameCanonic .(Γ ∷ varAG k) .(Γ₁ ∷ varAG k₁) (consCanonic k Γ x canT) (consCanonic k₁ Γ₁ x₁ canD) sameVar | no ¬p | no ¬p₁ | yes p = 
    ⊥-elim
      (notSucEqZero
        {nbOccurVar Γ k}
        (begin
          suc (nbOccurVar Γ k)
            ≡⟨ sym (unfoldNbOccurVar Γ k) ⟩
          (nbOccurVar (Γ ∷ varAG k) k)
            ≡⟨ sameVar k ⟩
          (nbOccurVar (Γ₁ ∷ varAG k₁) k)
            ≡⟨ notOccurCanonic (consCanonic k₁ Γ₁ x₁ canD) k p ⟩
          zero ∎))
  sameVar=>sameCanonic .(Γ ∷ varAG k) .(Γ₁ ∷ varAG k₁) (consCanonic k Γ x canT) (consCanonic k₁ Γ₁ x₁ canD) sameVar | no ¬p | no ¬p₁ | no ¬p₂ =
    ⊥-elim
      (¬p
        (≤-antisym
          {k₁}
          {k}
          (¬k<k'=>k'≤k
            ¬p₁)
          (¬k<k'=>k'≤k
            ¬p₂)))
  
  canonicNoOp :
    {Γ : ListTerm} ->
    (canΓ : Canonic Γ) ->
    nbOpListFor Γ ≡ 0
  canonicNoOp {.[]} []Canonic =
    refl
  canonicNoOp {.(Γ ∷ varAG k)} (consCanonic k Γ x canΓ) =
    canonicNoOp canΓ
