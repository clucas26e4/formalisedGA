module Syntax.ListTerm.Properties where
  
  {- STDLIB -}
  open import Nat
  open import Equality
  open import Data.Empty
  open import Relation.Nullary
  
  {- Syntax -}
  open import Syntax.Term
  open import Syntax.ListTerm
  
  {- Semantic -}
  open import Semantic.SemEquality
  open import Semantic.SemEquality.Properties
  open import Semantic.Interpretation

  sem-union-eq-plus :
    {Γ Γ' : ListTerm} ->
    ⟦ union Γ Γ' ⟧L ≡ₛ ⟦ Γ ⟧L +S ⟦ Γ' ⟧L
  sem-union-eq-plus {Γ} {[]} =
    symₛ neutral-+S
  sem-union-eq-plus {[]} {[] ∷ A} =
    transₛ
      (symₛ neutral-+S)
      commu-+S
  sem-union-eq-plus {Γ ∷ A₁} {[] ∷ A} =
    ctxtₛ
      ((CC (⟦ Γ ⟧L +S A₁)) +C ●)
      (symₛ
        (transₛ
          commu-+S
          neutral-+S))
  sem-union-eq-plus {[]} {Γ' ∷ A₁ ∷ A} =
    beginₛ
      ⟦ union [] Γ' ∷ A₁ ⟧L +S A
        ≡ₛ⟨ ctxtₛ
              (● +C (CC A))
              (sem-union-eq-plus {[]} {Γ' ∷ A₁}) ⟩
      (botAG +S ⟦ Γ' ∷ A₁ ⟧L) +S A
        ≡ₛ⟨ symₛ asso-+S ⟩
      botAG +S (⟦ Γ' ∷ A₁ ⟧L +S A) ∎ₛ
  sem-union-eq-plus {Γ ∷ A₂} {Γ' ∷ A₁ ∷ A} = 
    beginₛ
      ⟦ union (Γ ∷ A₂) Γ' ∷ A₁ ⟧L +S A
        ≡ₛ⟨ ctxtₛ
              (● +C (CC A))
              (sem-union-eq-plus {Γ ∷ A₂} {Γ' ∷ A₁}) ⟩
      (⟦ Γ ∷ A₂ ⟧L +S ⟦ Γ' ∷ A₁ ⟧L) +S A
        ≡ₛ⟨ symₛ asso-+S ⟩
      ⟦ Γ ∷ A₂ ⟧L +S (⟦ Γ' ∷ A₁ ⟧L +S A) ∎ₛ

  ListExchangeSem :
    {Γ Γ' : ListTerm} ->
    (Γ=Γ' : ListExchange Γ Γ') ->
    ⟦ Γ ⟧L ≡ₛ ⟦ Γ' ⟧L
  ListExchangeSem {Γ} {.Γ} idLE =
    reflₛ
  ListExchangeSem {(Γ ∷ A ∷ B)} {(Γ' ∷ .B ∷ .A)} (exLE Γ=Γ') =
    beginₛ
      (⟦ Γ ⟧L +S A) +S B
        ≡ₛ⟨ ctxtₛ
              ((● +C (CC A)) +C (CC B))
              (ListExchangeSem Γ=Γ') ⟩
      (⟦ Γ' ⟧L +S A) +S B
        ≡ₛ⟨ symₛ asso-+S ⟩
      ⟦ Γ' ⟧L +S (A +S B)
        ≡ₛ⟨ ctxtₛ
              ((CC (⟦ Γ' ⟧L)) +C ●)
              commu-+S ⟩
      ⟦ Γ' ⟧L +S (B +S A)
        ≡ₛ⟨ asso-+S ⟩
      (⟦ Γ' ⟧L +S B) +S A ∎ₛ
  ListExchangeSem {Γ} {Γ'} (transLE Γ=Γ' Γ=Γ'') =
    transₛ (ListExchangeSem Γ=Γ') (ListExchangeSem (Γ=Γ''))
  ListExchangeSem {Γ ∷ F} {Γ' ∷ .F} (indLE Γ=Γ') =
    ctxtₛ
      (● +C (CC F))
      (ListExchangeSem Γ=Γ')

  ListExchangeSym :
    {Γ Γ' : ListTerm} ->
    (Γ=Γ' : ListExchange Γ Γ') ->
    ListExchange Γ' Γ
  ListExchangeSym idLE =
    idLE
  ListExchangeSym (exLE Γ=Γ') =
    exLE (ListExchangeSym Γ=Γ')
  ListExchangeSym (transLE Γ=Γ' Γ=Γ'') =
    transLE (ListExchangeSym Γ=Γ'') (ListExchangeSym Γ=Γ')
  ListExchangeSym (indLE Γ=Γ') =
    indLE (ListExchangeSym Γ=Γ')

  ListExchangeKeepOperator :
    {Γ Γ' : ListTerm} ->
    (Γ=Γ' : ListExchange Γ Γ') ->
    nbOpListFor Γ ≡ nbOpListFor Γ'
  ListExchangeKeepOperator idLE =
    refl
  ListExchangeKeepOperator {Γ ∷ A ∷ B} {Γ' ∷ .B ∷ .A} (exLE Γ=Γ') =
    begin
      nbOpFor B + (nbOpFor A + nbOpListFor Γ)
        ≡⟨ sym (+-assoc (nbOpFor B) (nbOpFor A) (nbOpListFor Γ)) ⟩
      (nbOpFor B + nbOpFor A) + nbOpListFor Γ
        ≡⟨ cong (λ x -> (nbOpFor B + nbOpFor A) + x) (ListExchangeKeepOperator Γ=Γ') ⟩
      (nbOpFor B + nbOpFor A) + nbOpListFor Γ'
        ≡⟨ cong (λ x -> x + (nbOpListFor Γ')) (+-comm (nbOpFor B) (nbOpFor A)) ⟩
      (nbOpFor A + nbOpFor B) + nbOpListFor Γ'
        ≡⟨ +-assoc (nbOpFor A) (nbOpFor B) (nbOpListFor Γ') ⟩
      nbOpFor A + (nbOpFor B + nbOpListFor Γ') ∎
  ListExchangeKeepOperator (transLE Γ=Γ' Γ=Γ'') =
    trans (ListExchangeKeepOperator Γ=Γ') (ListExchangeKeepOperator Γ=Γ'')
  ListExchangeKeepOperator {Γ ∷ F} {Γ' ∷ .F}(indLE Γ=Γ') =
    cong (λ x -> (nbOpFor F) + x) (ListExchangeKeepOperator Γ=Γ')

  nbOccurVarSameHead :
    (Γ Γ' : ListTerm) ->
    (A : Term) ->
    (k : ℕ) ->
    nbOccurVar (Γ ∷ A) k ≡ nbOccurVar (Γ' ∷ A) k ->
    nbOccurVar Γ k ≡ nbOccurVar Γ' k
  nbOccurVarSameHead Γ Γ' (varAG x) k eq  with x ≡? k
  nbOccurVarSameHead Γ Γ' (varAG x) k eq | yes p =
    suc-injective eq
  nbOccurVarSameHead Γ Γ' (varAG x) k eq | no ¬p =
    eq
  nbOccurVarSameHead Γ Γ' botAG k eq =
    eq
  nbOccurVarSameHead Γ Γ' (A ⊔S A₁) k eq  = 
    eq
  nbOccurVarSameHead Γ Γ' (A +S A₁) k eq = 
    eq
  nbOccurVarSameHead Γ Γ' (A ⊓S A₁) k eq = 
    eq
  nbOccurVarSameHead Γ Γ' (-S A) k eq = 
    eq

  unfoldNbOccurVar :
    (Γ : ListTerm) ->
    (k : ℕ) ->
    (nbOccurVar (Γ ∷ varAG k) k) ≡ suc (nbOccurVar Γ k)
  unfoldNbOccurVar Γ k with k ≡? k
  unfoldNbOccurVar Γ k | yes p =
    refl
  unfoldNbOccurVar Γ k | no ¬p =
    ⊥-elim (¬p refl)

  unionAsso :
    (Γ Γ' Γ'' : ListTerm) ->
    union (union Γ Γ') Γ'' ≡ union Γ (union Γ' Γ'')
  unionAsso Γ Γ' [] =
    refl
  unionAsso Γ Γ' (Γ'' ∷ A) =
    cong
      (λ x -> x ∷ A)
      (unionAsso Γ Γ' Γ'')

  union[]T=T :
    (T : ListTerm) ->
    union [] T ≡ T
  union[]T=T [] =
    refl
  union[]T=T (T ∷ A) =
    cong
      (λ x -> x ∷ A)
      (union[]T=T T)

  unionKeepListExchange :
    {A B C D : ListTerm} ->
    (A=B : ListExchange A B) ->
    (C=D : ListExchange C D) ->
    ListExchange (union A C) (union B D)
  unionKeepListExchange {A} {B} {[]} {.[]} A=B idLE =
    A=B
  unionKeepListExchange {A} {B} {C ∷ A₁} {.(C ∷ A₁)} A=B idLE =
    indLE (unionKeepListExchange A=B (idLE {C}))
  unionKeepListExchange {A} {B} {(C ∷ H ∷ H')} {(D ∷ .H' ∷ .H)} A=B (exLE C=D) =
    exLE (unionKeepListExchange A=B C=D)
  unionKeepListExchange {A} {B} {[]} {D} A=B (transLE C=D C=D₁) =
    transLE
      (unionKeepListExchange A=B C=D)
      (unionKeepListExchange (idLE {B}) C=D₁)
  unionKeepListExchange {A} {B} {C ∷ A₁} {D} A=B (transLE {Γ₂ = Γ₂} C=D C=D₁) = 
    transLE
      (unionKeepListExchange A=B C=D)
      (unionKeepListExchange (idLE {B}) C=D₁)
  unionKeepListExchange {A} {B} {(C ∷ H)} {(D ∷ .H)} A=B (indLE C=D) =
    indLE (unionKeepListExchange A=B C=D)

  unionSymExchange :
    (Γ Γ' : ListTerm) ->
    ListExchange (union Γ Γ') (union Γ' Γ)
  unionSymExchange [] [] =
    idLE
  unionSymExchange [] (Γ' ∷ A) =
    ListExchangeCong
      {Γ' ∷ A}
      (sym (union[]T=T (Γ' ∷ A)))
      idLE
  unionSymExchange (Γ ∷ A) [] =
    ListExchangeSym
      (ListExchangeCong
        {Γ ∷ A}
        (sym (union[]T=T (Γ ∷ A)))
        idLE)
  unionSymExchange (Γ ∷ A) (Γ' ∷ A₁) =
    transLE
      {Γ₂ = (union Γ' Γ) ∷ A ∷ A₁}
      (indLE
        (unionSymExchange (Γ ∷ A) Γ'))
      (transLE
        {Γ₂ = union Γ' Γ ∷ A₁ ∷ A}
        (exLE idLE)
        (transLE
          {Γ₂ = union Γ Γ' ∷ A₁ ∷ A}
          (indLE
            (indLE
              (unionSymExchange Γ' Γ)))
          (indLE
            (unionSymExchange Γ (Γ' ∷ A₁)))))

  unionOp :
    (T T' : ListTerm) ->
    nbOpListFor (union T T') ≡ nbOpListFor T + nbOpListFor T'
  unionOp T [] =
    +-comm 0 (nbOpListFor T)
  unionOp T (T' ∷ A) = 
    begin
      (nbOpFor A + nbOpListFor (union T T'))
        ≡⟨ cong
             (λ x -> nbOpFor A + x)
             (unionOp T T') ⟩
      nbOpFor A + (nbOpListFor T + nbOpListFor T')
        ≡⟨ sym
             (+-assoc (nbOpFor A) (nbOpListFor T) (nbOpListFor T')) ⟩
      nbOpFor A + nbOpListFor T + nbOpListFor T'
        ≡⟨ cong
             (λ x -> x + nbOpListFor T')
             (+-comm (nbOpFor A) (nbOpListFor T)) ⟩
      nbOpListFor T + nbOpFor A + nbOpListFor T'
        ≡⟨ +-assoc (nbOpListFor T) (nbOpFor A) (nbOpListFor T') ⟩
      nbOpListFor T + (nbOpFor A + nbOpListFor T') ∎
