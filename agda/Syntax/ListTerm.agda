{-                                                  -
 -                                                  -
 -     Module of definition of a list of formulas   -
 -                                                  -
 -                                                  -}

module Syntax.ListTerm where
  
  {- STDLIB -}
  open import Nat
  open import Equality
  open import Data.Empty
  open import Relation.Nullary
  
  {- Syntax -}
  open import Syntax.Term
  
  {- Semantic -}
  
  {- Definition of a list of forumla (Γ or Δ) -}
  data ListTerm : Set where
    [] :
      ListTerm
    _∷_ :
      (Γ : ListTerm) ->
      (A : Term) ->
      ListTerm
  
  infixl 30 _∷_

  union :
    ListTerm ->
    ListTerm ->
    ListTerm
  union Γ [] =
    Γ
  union Γ (Γ' ∷ A) =
    (union Γ Γ') ∷ A
  
  {- Function to count operators -}
  nbOpListFor :
    (L : ListTerm) ->
    ℕ
  nbOpListFor [] =
    0
  nbOpListFor (l ∷ F) =
    (nbOpFor F) + (nbOpListFor l)
  
  topNbOpList :
    (Γ : ListTerm) ->
    ℕ
  topNbOpList [] =
    0
  topNbOpList (Γ ∷ A) =
    nbOpFor A
  
  {- ListExchange definition and properties -}
  data ListExchange : (Γ Γ' : ListTerm) -> Set where
    idLE :
      {Γ : ListTerm} ->
      ListExchange Γ Γ
    exLE :
      {Γ Γ' : ListTerm}{A B : Term} ->
      (Γ=Γ' : ListExchange Γ Γ') ->
      ListExchange (Γ ∷ A ∷ B) (Γ' ∷ B ∷ A)
    transLE :
      {Γ₁ Γ₂ Γ₃ : ListTerm} ->
      (Γ₁=Γ₂ : ListExchange Γ₁ Γ₂) ->
      (Γ₂=Γ₃ : ListExchange Γ₂ Γ₃) ->
      ListExchange Γ₁ Γ₃
    indLE :
      {Γ Γ' : ListTerm} ->
      {F : Term} ->
      (Γ=Γ' : ListExchange Γ Γ') ->
      ListExchange (Γ ∷ F) (Γ' ∷ F)

  putHeadList :
    (T : ListTerm) ->
    (F : Term) ->
    ListTerm
  putHeadList [] F =
    [] ∷ F
  putHeadList (T ∷ A) F =
    (putHeadList T F) ∷ A

  putHeadListExchange :
    {Γ : ListTerm} ->
    {F : Term} ->
    ListExchange (Γ ∷ F) (putHeadList Γ F)
  putHeadListExchange {[]} =
    idLE
  putHeadListExchange {Γ ∷ A} =
    transLE
      (exLE
        idLE)
      (indLE
        putHeadListExchange)

  ListDoExchangeFun :
    (Γ : ListTerm) ->
    (nbOpList topNbOp : ℕ) ->
    ListTerm
  ListDoExchangeFun [] nbOpList topNbOp =
    []
  ListDoExchangeFun (Γ ∷ A) zero topNbOp =
    Γ ∷ A
  ListDoExchangeFun (Γ ∷ A) (suc nbOpList) zero =
    putHeadList
      (ListDoExchangeFun
        Γ
        (suc nbOpList)
        (topNbOpList Γ))
      A
  ListDoExchangeFun (Γ ∷ A) (suc nbOpList) (suc topNbOp) =
    Γ ∷ A

  ListExchangeSubst :
    {Γ Γ' : ListTerm} ->
    (Γ=Γ' : Γ ≡ Γ') ->
    ListExchange Γ Γ'
  ListExchangeSubst refl =
    idLE
  ListExchangeCong :
    {Γ1 Γ2 Γ3 : ListTerm} ->
    (Γ1=Γ2 : Γ1 ≡ Γ2) ->
    (LEΓ1Γ3 : ListExchange Γ1 Γ3) ->
    ListExchange Γ2 Γ3
  ListExchangeCong refl LEΓ1Γ3 = LEΓ1Γ3

  abstract
    ListDoExchangeFunCorrect :
      {Γ : ListTerm} ->
      ListExchange Γ (ListDoExchangeFun Γ (nbOpListFor Γ) (topNbOpList Γ))
    ListDoExchangeFunCorrect {[]} =
      idLE
    ListDoExchangeFunCorrect {Γ ∷ varAG x} with nbOpListFor Γ | inspect nbOpListFor Γ
    ListDoExchangeFunCorrect {Γ ∷ varAG x} | zero | eq =
      idLE
    ListDoExchangeFunCorrect {Γ ∷ varAG x} | suc k | [ eq ] =
      transLE
        (indLE
          ListDoExchangeFunCorrect)
        (transLE
          {Γ₂ = (ListDoExchangeFun Γ (suc k) (topNbOpList Γ) ∷ varAG x)}
          (ListExchangeSubst
            (cong
              (λ k₁ → ListDoExchangeFun Γ k₁ (topNbOpList Γ) ∷ varAG x)
              eq))
          putHeadListExchange)
    ListDoExchangeFunCorrect {Γ ∷ botAG}  = 
      idLE
    ListDoExchangeFunCorrect {Γ ∷ (A ⊔S A₁)} with (nbOpFor A + nbOpFor A₁ + 1 + nbOpListFor Γ)
    ListDoExchangeFunCorrect {Γ ∷ (A ⊔S A₁)} | zero =
      idLE
    ListDoExchangeFunCorrect {Γ ∷ (A ⊔S A₁)} | suc k with (nbOpFor A + nbOpFor A₁ + 1) | inspect (λ x -> nbOpFor x + nbOpFor A₁ + 1) A
    ListDoExchangeFunCorrect {Γ ∷ (A ⊔S A₁)} | suc k | zero | [ eq ] =
      ⊥-elim
        (notSucEqZero
          (begin
            suc (nbOpFor A + nbOpFor A₁)
              ≡⟨ refl ⟩
            1 + nbOpFor A + nbOpFor A₁
              ≡⟨ +-comm 1 (nbOpFor A + nbOpFor A₁) ⟩
            nbOpFor A + nbOpFor A₁ + 1
              ≡⟨ eq ⟩
            zero ∎))
    ListDoExchangeFunCorrect {Γ ∷ (A ⊔S A₁)} | suc k | suc k' | eq =
      idLE
    ListDoExchangeFunCorrect {Γ ∷ (A +S A₁)} with (nbOpFor A + nbOpFor A₁ + 1 + nbOpListFor Γ)
    ListDoExchangeFunCorrect {Γ ∷ (A +S A₁)} | zero =
      idLE
    ListDoExchangeFunCorrect {Γ ∷ (A +S A₁)} | suc k with (nbOpFor A + nbOpFor A₁ + 1) | inspect (λ x -> nbOpFor x + nbOpFor A₁ + 1) A
    ListDoExchangeFunCorrect {Γ ∷ (A +S A₁)} | suc k | zero | [ eq ] =
      ⊥-elim
        (notSucEqZero
          (begin
            suc (nbOpFor A + nbOpFor A₁)
              ≡⟨ refl ⟩
            1 + nbOpFor A + nbOpFor A₁
              ≡⟨ +-comm 1 (nbOpFor A + nbOpFor A₁) ⟩
            nbOpFor A + nbOpFor A₁ + 1
              ≡⟨ eq ⟩
            zero ∎))
    ListDoExchangeFunCorrect {Γ ∷ (A +S A₁)} | suc k | suc k' | eq =
      idLE
    ListDoExchangeFunCorrect {Γ ∷ (A ⊓S A₁)} with (nbOpFor A + nbOpFor A₁ + 1 + nbOpListFor Γ)
    ListDoExchangeFunCorrect {Γ ∷ (A ⊓S A₁)} | zero =
      idLE
    ListDoExchangeFunCorrect {Γ ∷ (A ⊓S A₁)} | suc k with (nbOpFor A + nbOpFor A₁ + 1) | inspect (λ x -> nbOpFor x + nbOpFor A₁ + 1) A
    ListDoExchangeFunCorrect {Γ ∷ (A ⊓S A₁)} | suc k | zero | [ eq ] =
      ⊥-elim
        (notSucEqZero
          (begin
            suc (nbOpFor A + nbOpFor A₁)
              ≡⟨ refl ⟩
            1 + nbOpFor A + nbOpFor A₁
              ≡⟨ +-comm 1 (nbOpFor A + nbOpFor A₁) ⟩
            nbOpFor A + nbOpFor A₁ + 1
              ≡⟨ eq ⟩
            zero ∎))
    ListDoExchangeFunCorrect {Γ ∷ (A ⊓S A₁)} | suc k | suc k' | eq =
      idLE
    ListDoExchangeFunCorrect {Γ ∷ (-S A)} with (nbOpFor A + 1 + nbOpListFor Γ)
    ListDoExchangeFunCorrect {Γ ∷ (-S A)} | zero =
      idLE
    ListDoExchangeFunCorrect {Γ ∷ (-S A)} | suc k with (nbOpFor A + 1) | inspect (λ x -> nbOpFor x + 1) A
    ListDoExchangeFunCorrect {Γ ∷ (-S A)} | suc k | zero | [ eq ] =
      ⊥-elim
        (notSucEqZero
          (begin
            suc (nbOpFor A)
              ≡⟨ refl ⟩
            1 + nbOpFor A
              ≡⟨ +-comm 1 (nbOpFor A) ⟩
            nbOpFor A + 1
              ≡⟨ eq ⟩
            zero ∎))
    ListDoExchangeFunCorrect {Γ ∷ (-S A)} | suc k | suc k' | eq =
      idLE

  ListDoExchange :
    (Γ : ListTerm) -> ListTerm
  ListDoExchange Γ =
    ListDoExchangeFun Γ (nbOpListFor Γ) (topNbOpList Γ)

  abstract
    ¬putHeadList=[] :
      (Γ : ListTerm) -> 
      (A : Term) ->
      ¬ putHeadList Γ A ≡ []
    ¬putHeadList=[] [] A = 
      λ {()}
    ¬putHeadList=[] (Γ ∷ A') A = 
      λ {()}
    
    ¬ListDoExchangeΓ∷A=[] :
      (Γ : ListTerm) ->
      (A : Term) ->
      ¬(ListDoExchange (Γ ∷ A) ≡ [])
    ¬ListDoExchangeΓ∷A=[] Γ A with nbOpListFor (Γ ∷ A)
    ¬ListDoExchangeΓ∷A=[] Γ A | zero  = 
      λ {()}
    ¬ListDoExchangeΓ∷A=[] Γ A | suc nbOp with topNbOpList (Γ ∷ A)
    ¬ListDoExchangeΓ∷A=[] Γ A | suc nbOp | zero = 
      ¬putHeadList=[] (ListDoExchangeFun Γ (suc nbOp) (topNbOpList Γ)) A
    ¬ListDoExchangeΓ∷A=[] Γ A | suc nbOp | suc nbOpTop = 
      λ {()}
    
    ListDoExchangeCorrect :
      {Γ : ListTerm} ->
      ListExchange Γ (ListDoExchange Γ)
    ListDoExchangeCorrect {Γ} = ListDoExchangeFunCorrect {Γ}

    putHeadNoVar :
      {Γ : ListTerm} ->
      {B : Term} ->
      (Γ¬Var : (Γ' : ListTerm)(k : ℕ) -> ¬ (Γ ≡ Γ' ∷ (varAG k))) ->
      (Γ¬[] : ¬ (Γ ≡ [])) ->
      ((Γ' : ListTerm)(k : ℕ) -> ¬ (putHeadList Γ B ≡ Γ' ∷ (varAG k)))
    putHeadNoVar {[]} Γ¬Var Γ¬[] =
      ⊥-elim
        (Γ¬[]
          refl)
    putHeadNoVar {Γ ∷ varAG x} Γ¬Var Γ¬[] =
      ⊥-elim
        (Γ¬Var
          Γ
          x
          refl)
    putHeadNoVar {Γ ∷ botAG} Γ¬Var Γ¬[] =
      λ {Γ' k ()}
    putHeadNoVar {Γ ∷ (A ⊔S A₁)} Γ¬Var Γ¬[] =
      λ {Γ' k ()}
    putHeadNoVar {Γ ∷ (A +S A₁)} Γ¬Var Γ¬[] =
      λ {Γ' k ()}
    putHeadNoVar {Γ ∷ (A ⊓S A₁)} Γ¬Var Γ¬[] =
      λ {Γ' k ()}
    putHeadNoVar {Γ ∷ (-S A)} Γ¬Var Γ¬[] =
      λ {Γ' k ()}

    ListDoExchangeNoVar :
      {Γ : ListTerm} ->
      (nbOp≠z : ¬(nbOpListFor Γ ≡ 0)) ->
      (Γ' : ListTerm)(k : ℕ) -> ¬ (ListDoExchange Γ ≡ Γ' ∷ (varAG k))
    ListDoExchangeNoVar {[]} nbOp¬z =
      ⊥-elim
        (nbOp¬z
          refl)
    ListDoExchangeNoVar {[] ∷ varAG x} nbOp¬z = 
      ⊥-elim
        (nbOp¬z
          refl)
    ListDoExchangeNoVar {[] ∷ botAG} nbOp¬z with nbOpListFor ([] ∷ botAG) | topNbOpList ([] ∷ botAG)
    ListDoExchangeNoVar {[] ∷ botAG} nbOp¬z | op | top =
      λ {Γ' k ()}
    ListDoExchangeNoVar {[] ∷ (A ⊔S A₁)} nbOp¬z with nbOpListFor ([] ∷ (A ⊔S A₁)) | topNbOpList ([] ∷ (A ⊔S A₁))
    ListDoExchangeNoVar {[] ∷ (A ⊔S A₁)} nbOp¬z | nbOp | nbOpTop =
      λ {Γ' k ()}
    ListDoExchangeNoVar {[] ∷ (A +S A₁)} nbOp¬z with nbOpListFor ([] ∷ (A +S A₁)) | topNbOpList ([] ∷ (A +S A₁))
    ListDoExchangeNoVar {[] ∷ (A +S A₁)} nbOp¬z | nbOp | nbOpTop =
      λ {Γ' k ()}
    ListDoExchangeNoVar {[] ∷ (A ⊓S A₁)} nbOp¬z with nbOpListFor ([] ∷ (A ⊓S A₁)) | topNbOpList ([] ∷ (A ⊓S A₁))
    ListDoExchangeNoVar {[] ∷ (A ⊓S A₁)} nbOp¬z | nbOp | nbOpTop =
      λ {Γ' k ()}
    ListDoExchangeNoVar {[] ∷ (-S A)} nbOp¬z with nbOpListFor ([] ∷ (-S A)) | topNbOpList ([] ∷ (-S A))
    ListDoExchangeNoVar {[] ∷ (-S A)} nbOp¬z | nbOp | nbOpTop =
      λ {Γ' k ()}
    ListDoExchangeNoVar {Γ ∷ A₁ ∷ A} nbOp¬z with nbOpListFor (Γ ∷ A₁ ∷ A) | inspect nbOpListFor (Γ ∷ A₁ ∷ A) | topNbOpList (Γ ∷ A₁ ∷ A) | inspect topNbOpList (Γ ∷ A₁ ∷ A)
    ListDoExchangeNoVar {Γ ∷ A₁ ∷ A} nbOp¬z | zero | [ eq ] | nbOpTop | [ eq₁ ] =
      ⊥-elim
        (nbOp¬z
          (trans
            (cong
              (λ x -> x + (nbOpFor A₁ + nbOpListFor Γ))
              (sym eq₁))
            eq))
    ListDoExchangeNoVar {Γ ∷ A₁ ∷ A} nbOp¬z | suc nbOp | eq | zero | eq' with nbOpListFor (Γ ∷ A₁) | inspect nbOpListFor (Γ ∷ A₁)
    ListDoExchangeNoVar {Γ ∷ A₁ ∷ A} nbOp¬z | suc nbOp | eq | zero | eq' | zero | [ eq₁ ] =
      ⊥-elim
        (nbOp¬z
          refl)
    ListDoExchangeNoVar {Γ ∷ A₁ ∷ A} nbOp¬z | suc nbOp | eq | zero | eq' | suc nbOp' | [ eq₁ ] =
      λ Γ' k x →
        putHeadNoVar
          {ListDoExchange
          (Γ ∷ A₁)}
          {A}
          (ListDoExchangeNoVar
            {Γ ∷ A₁}
            (λ x₁ →
              nbOp¬z
                (trans
                  (sym eq₁)
                  x₁)))
          (¬ListDoExchangeΓ∷A=[] Γ A₁)
          Γ'
          k
          (begin
            putHeadList (ListDoExchange (Γ ∷ A₁)) A
              ≡⟨ refl ⟩
            putHeadList (ListDoExchangeFun (Γ ∷ A₁) (nbOpListFor (Γ ∷ A₁)) (topNbOpList (Γ ∷ A₁))) A
              ≡⟨ refl ⟩
            putHeadList (ListDoExchangeFun (Γ ∷ A₁) (nbOpListFor (Γ ∷ A₁)) (nbOpFor A₁)) A
              ≡⟨ cong
                   (λ x → putHeadList (ListDoExchangeFun (Γ ∷ A₁) x (nbOpFor A₁)) A)
                   eq₁ ⟩
            putHeadList (ListDoExchangeFun (Γ ∷ A₁) (suc nbOp') (nbOpFor A₁)) A
              ≡⟨ x ⟩
            Γ' ∷ varAG k ∎)
    ListDoExchangeNoVar {Γ ∷ A₁ ∷ varAG x} nbOp¬z | suc nbOp | eq | suc nbOpTop | [ () ]
    ListDoExchangeNoVar {Γ ∷ A₁ ∷ botAG} nbOp¬z | suc nbOp | eq | suc nbOpTop | [ eq₁ ] =
      λ {Γ' k ()}
    ListDoExchangeNoVar {Γ ∷ A₁ ∷ (A ⊔S A₂)} nbOp¬z | suc nbOp | eq | suc nbOpTop | [ eq₁ ] = 
      λ {Γ' k ()}
    ListDoExchangeNoVar {Γ ∷ A₁ ∷ (A +S A₂)} nbOp¬z | suc nbOp | eq | suc nbOpTop | [ eq₁ ] = 
      λ {Γ' k ()}
    ListDoExchangeNoVar {Γ ∷ A₁ ∷ (A ⊓S A₂)} nbOp¬z | suc nbOp | eq | suc nbOpTop | [ eq₁ ] = 
      λ {Γ' k ()}
    ListDoExchangeNoVar {Γ ∷ A₁ ∷ (-S A)} nbOp¬z | suc nbOp | eq | suc nbOpTop | [ eq₁ ] = 
      λ {Γ' k ()}

    ListExchangeKeepOp :
      {Γ Γ' : ListTerm} ->
      ListExchange Γ Γ' ->
      nbOpListFor Γ ≡ nbOpListFor Γ'
    ListExchangeKeepOp {Γ} {.Γ} idLE =
      refl
    ListExchangeKeepOp {(Γ ∷ A ∷ B)} {(Γ' ∷ .B ∷ .A)} (exLE Γ=Γ') =
      begin
        nbOpFor B + (nbOpFor A + nbOpListFor Γ)
          ≡⟨ sym (+-assoc (nbOpFor B) (nbOpFor A) (nbOpListFor Γ)) ⟩
        (nbOpFor B + nbOpFor A) + nbOpListFor Γ
          ≡⟨ cong
               (λ x -> x + nbOpListFor Γ)
               (+-comm (nbOpFor B) (nbOpFor A)) ⟩
        (nbOpFor A + nbOpFor B) + nbOpListFor Γ
          ≡⟨ cong
               (λ x -> (nbOpFor A + nbOpFor B) + x)
               (ListExchangeKeepOp Γ=Γ') ⟩
        (nbOpFor A + nbOpFor B) + nbOpListFor Γ'
          ≡⟨ +-assoc (nbOpFor A) (nbOpFor B) (nbOpListFor Γ') ⟩
        nbOpFor A + (nbOpFor B + nbOpListFor Γ') ∎
    ListExchangeKeepOp {Γ} {Γ'} (transLE Γ=Γ' Γ=Γ'') =
      trans (ListExchangeKeepOp Γ=Γ') (ListExchangeKeepOp Γ=Γ'')
    ListExchangeKeepOp {(Γ ∷ H)} {(Γ' ∷ .H)} (indLE Γ=Γ') =
      cong (λ x -> nbOpFor H + x) (ListExchangeKeepOp Γ=Γ')

  nbOccurVar :
    (T : ListTerm) ->
    (k : ℕ) ->
    ℕ
  nbOccurVar [] k =
    0
  nbOccurVar (T ∷ varAG x) k with x ≡? k
  nbOccurVar (T ∷ varAG x) k | yes p =
    suc (nbOccurVar T k)
  nbOccurVar (T ∷ varAG x) k | no ¬p = 
    nbOccurVar T k
  nbOccurVar (T ∷ botAG) k = 
    nbOccurVar T k
  nbOccurVar (T ∷ (A ⊔S A₁)) k = 
    nbOccurVar T k
  nbOccurVar (T ∷ (A +S A₁)) k = 
    nbOccurVar T k
  nbOccurVar (T ∷ (A ⊓S A₁)) k = 
    nbOccurVar T k
  nbOccurVar (T ∷ (-S A)) k = 
    nbOccurVar T k
