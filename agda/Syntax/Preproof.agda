module Syntax.Preproof where
  {- STDLIB -}

  {- Syntax -}
  open import Syntax.Term
  open import Syntax.ListTerm
  open import Syntax.Seq
  open import Syntax.HSeq

  {- Semantic -}

  data Preproof : HSeq -> Set where
    leaf :
      (G : HSeq) ->
      Preproof G
    PreZ-L :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      Preproof (G ∣ (Γ , Δ)) ->
      Preproof (G ∣ (Γ ∷ botAG , Δ))
    PreZ-R :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      Preproof (G ∣ (Γ , Δ)) ->
      Preproof (G ∣ (Γ , Δ ∷ botAG))
    Preminus-L :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A : Term) ->
      Preproof (G ∣ (Γ , Δ ∷ A)) ->
      Preproof (G ∣ (Γ ∷ (-S A) , Δ))
    Preminus-R :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A : Term) ->
      Preproof (G ∣ (Γ ∷ A , Δ)) ->
      Preproof (G ∣ (Γ , Δ ∷ (-S A)))
    Preplus-L :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      Preproof (G ∣(Γ ∷ A ∷ B , Δ)) ->
      Preproof (G ∣ (Γ ∷ (A +S B), Δ))
    Preplus-R :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      Preproof (G ∣ (Γ , Δ ∷ A ∷ B)) ->
      Preproof (G ∣ (Γ , Δ ∷ (A +S B)))
    Premax-L :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      Preproof (G ∣(Γ ∷ A , Δ)) ->
      Preproof (G ∣(Γ ∷ B , Δ)) ->
      Preproof (G ∣(Γ ∷ (A ⊔S B), Δ))
    Premax-R :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      Preproof (G ∣(Γ , Δ ∷ A)∣(Γ , Δ ∷ B)) ->
      Preproof (G ∣(Γ , Δ ∷ (A ⊔S B)))
    Premin-L :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      Preproof (G ∣ (Γ ∷ A , Δ) ∣ (Γ ∷ B , Δ)) ->
      Preproof (G ∣ (Γ ∷ (A ⊓S B), Δ))
    Premin-R :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      Preproof (G ∣ (Γ , Δ ∷ A)) ->
      Preproof (G ∣ (Γ , Δ ∷ B)) ->
      Preproof (G ∣ (Γ , Δ ∷ (A ⊓S B)))
    PreZ-L-head :  
      (Γ Δ : ListTerm) ->
      Preproof (head (Γ , Δ)) ->
      Preproof (head (Γ ∷ botAG , Δ))
    PreZ-R-head :
      (Γ Δ : ListTerm) ->
      Preproof (head (Γ , Δ)) ->
      Preproof (head (Γ , Δ ∷ botAG))
    Preminus-L-head :
      (Γ Δ : ListTerm) ->
      (A : Term) ->
      Preproof (head (Γ , Δ ∷ A)) ->
      Preproof (head (Γ ∷ (-S A), Δ))
    Preminus-R-head :
      (Γ Δ : ListTerm) ->
      (A : Term) ->
      Preproof (head (Γ ∷ A , Δ)) ->
      Preproof (head (Γ , Δ ∷ (-S A)))
    Preplus-L-head :
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      Preproof (head (Γ ∷ A ∷ B , Δ)) ->
      Preproof (head (Γ ∷ (A +S B), Δ))
    Preplus-R-head :
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      Preproof (head(Γ , Δ ∷ A ∷ B)) ->
      Preproof (head(Γ , Δ ∷ (A +S B)))
    Premax-L-head :
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      Preproof (head(Γ ∷ A , Δ)) ->
      Preproof (head(Γ ∷ B , Δ)) ->
      Preproof (head(Γ ∷ (A ⊔S B), Δ))
    Premax-R-head :
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      Preproof (head(Γ , Δ ∷ A)∣(Γ , Δ ∷ B)) ->
      Preproof (head(Γ , Δ ∷ (A ⊔S B)))
    Premin-L-head :
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      Preproof (head (Γ ∷ A , Δ) ∣ (Γ ∷ B , Δ)) ->
      Preproof (head (Γ ∷ (A ⊓S B), Δ))
    Premin-R-head :
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      Preproof (head (Γ , Δ ∷ A)) ->
      Preproof (head (Γ , Δ ∷ B)) ->
      Preproof (head (Γ , Δ ∷ (A ⊓S B)))
    Preseq-exchange :
      (G : HSeq) ->
      (Γ Γ' Δ Δ' : ListTerm) ->
      ListExchange Γ Γ' ->
      ListExchange Δ Δ' ->
      Preproof (G ∣ (Γ , Δ)) ->
      Preproof (G ∣ (Γ' , Δ'))
    Preseq-exchange-head :
      (Γ Γ' Δ Δ' : ListTerm) ->
      ListExchange Γ Γ' ->
      ListExchange Δ Δ' ->
      Preproof (head (Γ , Δ)) ->
      Preproof (head (Γ' , Δ'))
    Prehseq-exchange :
      (G G' : HSeq) ->
      HSeqExchange G G' ->
      Preproof G ->
      Preproof G'


  
