module Syntax.Preproof where
  {- STDLIB -}

  {- Syntax -}
  open import Syntax.Term
  open import Syntax.ListTerm
  open import Syntax.Seq
  open import Syntax.HSeq
  open import Syntax.HSeqList
  open import Syntax.Proof

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
      
  getLeaf :
    {G : HSeq} ->
    (ppG : Preproof G) ->
    HSeqList
  getLeaf (leaf G) = 
    G ∷H []H
  getLeaf (PreZ-L G Γ Δ ppG) =
    getLeaf ppG
  getLeaf (PreZ-R G Γ Δ ppG) =
    getLeaf ppG
  getLeaf (Preminus-L G Γ Δ A ppG) =
    getLeaf ppG
  getLeaf (Preminus-R G Γ Δ A ppG) =
    getLeaf ppG
  getLeaf (Preplus-L G Γ Δ A B ppG) =
    getLeaf ppG
  getLeaf (Preplus-R G Γ Δ A B ppG) =
    getLeaf ppG
  getLeaf (Premax-L G Γ Δ A B ppG ppG₁) =
    unionHL (getLeaf ppG) (getLeaf ppG₁)
  getLeaf (Premax-R G Γ Δ A B ppG) =
    getLeaf ppG
  getLeaf (Premin-L G Γ Δ A B ppG) =
    getLeaf ppG
  getLeaf (Premin-R G Γ Δ A B ppG ppG₁) =
    unionHL (getLeaf ppG) (getLeaf ppG₁)
  getLeaf (PreZ-L-head Γ Δ ppG) =
    getLeaf ppG
  getLeaf (PreZ-R-head Γ Δ ppG) =
    getLeaf ppG
  getLeaf (Preminus-L-head Γ Δ A ppG) =
    getLeaf ppG
  getLeaf (Preminus-R-head Γ Δ A ppG) =
    getLeaf ppG
  getLeaf (Preplus-L-head Γ Δ A B ppG) =
    getLeaf ppG
  getLeaf (Preplus-R-head Γ Δ A B ppG) =
    getLeaf ppG
  getLeaf (Premax-L-head Γ Δ A B ppG ppG₁) =
    unionHL (getLeaf ppG) (getLeaf ppG₁)
  getLeaf (Premax-R-head Γ Δ A B ppG) =
    getLeaf ppG
  getLeaf (Premin-L-head Γ Δ A B ppG) =
    getLeaf ppG
  getLeaf (Premin-R-head Γ Δ A B ppG ppG₁) =
    unionHL (getLeaf ppG) (getLeaf ppG₁)
  getLeaf (Preseq-exchange G Γ Γ' Δ Δ' x x₁ ppG) =
    getLeaf ppG
  getLeaf (Preseq-exchange-head Γ Γ' Δ Δ' x x₁ ppG) =
    getLeaf ppG
  getLeaf (Prehseq-exchange G G' x ppG) =
    getLeaf ppG

  finishProof :
    {G : HSeq} ->
    (ppG : Preproof G) ->
    (pLeaf : Prooflist (getLeaf ppG)) ->
    Proof G
  finishProof (leaf G) (consP pLeaf pG) =
    pG
  finishProof (PreZ-L G Γ Δ ppG) pLeaf =
    Z-L
      G
      Γ
      Δ
      (finishProof ppG pLeaf)
  finishProof (PreZ-R G Γ Δ ppG) pLeaf =
    Z-R
      G
      Γ
      Δ
      (finishProof ppG pLeaf)
  finishProof (Preminus-L G Γ Δ A ppG) pLeaf =
    minus-L
      G
      Γ
      Δ
      A
      (finishProof ppG pLeaf)
  finishProof (Preminus-R G Γ Δ A ppG) pLeaf =
    minus-R
      G
      Γ
      Δ
      A
      (finishProof ppG pLeaf)
  finishProof (Preplus-L G Γ Δ A B ppG) pLeaf =
    plus-L
      G
      Γ
      Δ
      A
      B
      (finishProof ppG pLeaf)
  finishProof (Preplus-R G Γ Δ A B ppG) pLeaf =
    plus-R
      G
      Γ
      Δ
      A
      B
      (finishProof ppG pLeaf)
  finishProof (Premax-L G Γ Δ A B ppG ppG₁) pLeaf =
    max-L
      G
      Γ
      Δ
      A
      B
      (finishProof ppG (Prooflist-L (getLeaf ppG) (getLeaf ppG₁) pLeaf))
      (finishProof ppG₁ (Prooflist-R (getLeaf ppG) (getLeaf ppG₁) pLeaf))
  finishProof (Premax-R G Γ Δ A B ppG) pLeaf =
    max-R
      G
      Γ
      Δ
      A
      B
      (finishProof ppG pLeaf)
  finishProof (Premin-L G Γ Δ A B ppG) pLeaf =
    min-L
      G
      Γ
      Δ
      A
      B
      (finishProof ppG pLeaf)
  finishProof (Premin-R G Γ Δ A B ppG ppG₁) pLeaf =
    min-R
      G
      Γ
      Δ
      A
      B
      (finishProof ppG (Prooflist-L (getLeaf ppG) (getLeaf ppG₁) pLeaf))
      (finishProof ppG₁ (Prooflist-R (getLeaf ppG) (getLeaf ppG₁) pLeaf))
  finishProof (PreZ-L-head Γ Δ ppG) pLeaf =
    Z-L-head
      Γ
      Δ
      (finishProof ppG pLeaf)
  finishProof (PreZ-R-head Γ Δ ppG) pLeaf =
    Z-R-head
      Γ
      Δ
      (finishProof ppG pLeaf)
  finishProof (Preminus-L-head Γ Δ A ppG) pLeaf =
    minus-L-head
      Γ
      Δ
      A
      (finishProof ppG pLeaf)
  finishProof (Preminus-R-head Γ Δ A ppG) pLeaf =
    minus-R-head
      Γ
      Δ
      A
      (finishProof ppG pLeaf)
  finishProof (Preplus-L-head Γ Δ A B ppG) pLeaf =
    plus-L-head
      Γ
      Δ
      A
      B
      (finishProof ppG pLeaf)
  finishProof (Preplus-R-head Γ Δ A B ppG) pLeaf =
    plus-R-head
      Γ
      Δ
      A
      B
      (finishProof ppG pLeaf)
  finishProof (Premax-L-head Γ Δ A B ppG ppG₁) pLeaf =
    max-L-head
      Γ
      Δ
      A
      B
      (finishProof ppG (Prooflist-L (getLeaf ppG) (getLeaf ppG₁) pLeaf))
      (finishProof ppG₁ (Prooflist-R (getLeaf ppG) (getLeaf ppG₁) pLeaf))
  finishProof (Premax-R-head Γ Δ A B ppG) pLeaf =
    max-R-head
      Γ
      Δ
      A
      B
      (finishProof ppG pLeaf)
  finishProof (Premin-L-head Γ Δ A B ppG) pLeaf =
    min-L-head
      Γ
      Δ
      A
      B
      (finishProof ppG pLeaf)
  finishProof (Premin-R-head Γ Δ A B ppG ppG₁) pLeaf =
    min-R-head
      Γ
      Δ
      A
      B
      (finishProof ppG (Prooflist-L (getLeaf ppG) (getLeaf ppG₁) pLeaf))
      (finishProof ppG₁ (Prooflist-R (getLeaf ppG) (getLeaf ppG₁) pLeaf))
  finishProof (Preseq-exchange G Γ Γ' Δ Δ' x x₁ ppG) pLeaf =
    seq-exchange
      G
      Γ
      Γ'
      Δ
      Δ'
      x
      x₁
      (finishProof ppG pLeaf)
  finishProof (Preseq-exchange-head Γ Γ' Δ Δ' x x₁ ppG) pLeaf =
    seq-exchange-head
      Γ
      Γ'
      Δ
      Δ'
      x
      x₁
      (finishProof ppG pLeaf)
  finishProof (Prehseq-exchange G G' x ppG) pLeaf =
    hseq-exchange
      G
      G'
      x
      (finishProof ppG pLeaf)
