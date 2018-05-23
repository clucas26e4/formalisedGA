module Syntax.CutProof where
  {- STDLIB -}
  open import Equality

  {- Syntax -}
  open import Syntax.Term
  open import Syntax.ListTerm
  open import Syntax.Seq
  open import Syntax.HSeq

  {- Semantic -}


  data CutProof : HSeq -> Set where
    -- Axioms
    ax :
      (A : Term) ->
      CutProof (head ([] ∷ A , [] ∷ A))
    Δ-ax :
      CutProof (head ([] , []))
    -- Structural Rules
    W :
      (G : HSeq) ->
      (Γ1 Γ2 Δ1 Δ2 : ListTerm) ->
      CutProof (G ∣ (Γ1 , Δ1)) ->
      CutProof (G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    C :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      CutProof (G ∣ (Γ , Δ) ∣ (Γ , Δ)) ->
      CutProof (G ∣ (Γ , Δ))
    S :
      (G : HSeq) ->
      (Γ1 Γ2 Δ1 Δ2 : ListTerm) ->
      CutProof (G ∣ (union Γ1 Γ2 , union Δ1 Δ2)) ->
      CutProof (G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    M :
      (G : HSeq) ->
      (Γ1 Γ2 Δ1 Δ2 : ListTerm) ->
      CutProof (G ∣ (Γ1 , Δ1)) ->
      CutProof (G ∣ (Γ2 , Δ2)) ->
      CutProof (G ∣ (union Γ1 Γ2 , union Δ1 Δ2))
    W-head :
      (Γ1 Γ2 Δ1 Δ2 : ListTerm) ->
      CutProof (head (Γ1 , Δ1)) ->
      CutProof (head (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    C-head :
      (Γ Δ : ListTerm) ->
      CutProof (head (Γ , Δ) ∣ (Γ , Δ)) ->
      CutProof (head (Γ , Δ))
    S-head :
      (Γ1 Γ2 Δ1 Δ2 : ListTerm) ->
      CutProof (head (union Γ1 Γ2 , union Δ1 Δ2)) ->
      CutProof (head (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    M-head :
      (Γ1 Γ2 Δ1 Δ2 : ListTerm) ->
      CutProof (head (Γ1 , Δ1)) ->
      CutProof (head (Γ2 , Δ2)) ->
      CutProof (head (union Γ1 Γ2 , union Δ1 Δ2))
    -- Logical Rules
    Z-L :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      CutProof (G ∣ (Γ , Δ)) ->
      CutProof (G ∣ (Γ ∷ botAG , Δ))
    Z-R :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      CutProof (G ∣ (Γ , Δ)) ->
      CutProof (G ∣ (Γ , Δ ∷ botAG))
    minus-L :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A : Term) ->
      CutProof (G ∣ (Γ , Δ ∷ A)) ->
      CutProof (G ∣ (Γ ∷ (-S A) , Δ))
    minus-R :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A : Term) ->
      CutProof (G ∣ (Γ ∷ A , Δ)) ->
      CutProof (G ∣ (Γ , Δ ∷ (-S A)))
    plus-L :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      CutProof (G ∣(Γ ∷ A ∷ B , Δ)) ->
      CutProof (G ∣ (Γ ∷ (A +S B), Δ))
    plus-R :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      CutProof (G ∣ (Γ , Δ ∷ A ∷ B)) ->
      CutProof (G ∣ (Γ , Δ ∷ (A +S B)))
    max-L :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      CutProof (G ∣(Γ ∷ A , Δ)) ->
      CutProof (G ∣(Γ ∷ B , Δ)) ->
      CutProof (G ∣(Γ ∷ (A ⊔S B), Δ))
    max-R :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      CutProof (G ∣(Γ , Δ ∷ A)∣(Γ , Δ ∷ B)) ->
      CutProof (G ∣(Γ , Δ ∷ (A ⊔S B)))
    min-L :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      CutProof (G ∣ (Γ ∷ A , Δ) ∣ (Γ ∷ B , Δ)) ->
      CutProof (G ∣ (Γ ∷ (A ⊓S B), Δ))
    min-R :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      CutProof (G ∣ (Γ , Δ ∷ A)) ->
      CutProof (G ∣ (Γ , Δ ∷ B)) ->
      CutProof (G ∣ (Γ , Δ ∷ (A ⊓S B)))
    Z-L-head :  
      (Γ Δ : ListTerm) ->
      CutProof (head (Γ , Δ)) ->
      CutProof (head (Γ ∷ botAG , Δ))
    Z-R-head :
      (Γ Δ : ListTerm) ->
      CutProof (head (Γ , Δ)) ->
      CutProof (head (Γ , Δ ∷ botAG))
    minus-L-head :
      (Γ Δ : ListTerm) ->
      (A : Term) ->
      CutProof (head (Γ , Δ ∷ A)) ->
      CutProof (head (Γ ∷ (-S A), Δ))
    minus-R-head :
      (Γ Δ : ListTerm) ->
      (A : Term) ->
      CutProof (head (Γ ∷ A , Δ)) ->
      CutProof (head (Γ , Δ ∷ (-S A)))
    plus-L-head :
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      CutProof (head (Γ ∷ A ∷ B , Δ)) ->
      CutProof (head (Γ ∷ (A +S B), Δ))
    plus-R-head :
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      CutProof (head(Γ , Δ ∷ A ∷ B)) ->
      CutProof (head(Γ , Δ ∷ (A +S B)))
    max-L-head :
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      CutProof (head(Γ ∷ A , Δ)) ->
      CutProof (head(Γ ∷ B , Δ)) ->
      CutProof (head(Γ ∷ (A ⊔S B), Δ))
    max-R-head :
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      CutProof (head(Γ , Δ ∷ A)∣(Γ , Δ ∷ B)) ->
      CutProof (head(Γ , Δ ∷ (A ⊔S B)))
    min-L-head :
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      CutProof (head (Γ ∷ A , Δ) ∣ (Γ ∷ B , Δ)) ->
      CutProof (head (Γ ∷ (A ⊓S B), Δ))
    min-R-head :
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      CutProof (head (Γ , Δ ∷ A)) ->
      CutProof (head (Γ , Δ ∷ B)) ->
      CutProof (head (Γ , Δ ∷ (A ⊓S B)))
    seq-exchange :
      (G : HSeq) ->
      (Γ Γ' Δ Δ' : ListTerm) ->
      ListExchange Γ Γ' ->
      ListExchange Δ Δ' ->
      CutProof (G ∣ (Γ , Δ)) ->
      CutProof (G ∣ (Γ' , Δ'))
    -- Exchange Rules
    seq-exchange-head :
      (Γ Γ' Δ Δ' : ListTerm) ->
      ListExchange Γ Γ' ->
      ListExchange Δ Δ' ->
      CutProof (head (Γ , Δ)) ->
      CutProof (head (Γ' , Δ'))
    hseq-exchange :
      (G G' : HSeq) ->
      HSeqExchange G G' ->
      CutProof G ->
      CutProof G'
    -- Cut rule
    cut :
      (Γ₁ Γ₂ Δ₁ Δ₂ : ListTerm) ->
      (A : Term) ->
      CutProof (head (Γ₁ ∷ A , Δ₁)) ->
      CutProof (head (Γ₂ , Δ₂ ∷ A)) ->
      CutProof (head (union Γ₁ Γ₂ , union Δ₁ Δ₂))

  CutProofCong :
    {G G' : HSeq} ->
    CutProof G ->
    G ≡ G' ->
    CutProof G'
  CutProofCong PG refl = PG
