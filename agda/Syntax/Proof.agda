module Syntax.Proof where
  {- STDLIB -}
  open import Equality

  {- Syntax -}
  open import Syntax.Term
  open import Syntax.ListTerm
  open import Syntax.Seq
  open import Syntax.HSeq

  {- Semantic -}


  data Proof : HSeq -> Set where
    -- Axioms
    ax :
      (A : Term) ->
      Proof (head ([] ∷ A , [] ∷ A))
    Δ-ax :
      Proof (head ([] , []))
    -- Structural Rules
    W :
      (G : HSeq) ->
      (Γ1 Γ2 Δ1 Δ2 : ListTerm) ->
      Proof (G ∣ (Γ1 , Δ1)) ->
      Proof (G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    C :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      Proof (G ∣ (Γ , Δ) ∣ (Γ , Δ)) ->
      Proof (G ∣ (Γ , Δ))
    S :
      (G : HSeq) ->
      (Γ1 Γ2 Δ1 Δ2 : ListTerm) ->
      Proof (G ∣ (union Γ1 Γ2 , union Δ1 Δ2)) ->
      Proof (G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    M :
      (G : HSeq) ->
      (Γ1 Γ2 Δ1 Δ2 : ListTerm) ->
      Proof (G ∣ (Γ1 , Δ1)) ->
      Proof (G ∣ (Γ2 , Δ2)) ->
      Proof (G ∣ (union Γ1 Γ2 , union Δ1 Δ2))
    W-head :
      (Γ1 Γ2 Δ1 Δ2 : ListTerm) ->
      Proof (head (Γ1 , Δ1)) ->
      Proof (head (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    C-head :
      (Γ Δ : ListTerm) ->
      Proof (head (Γ , Δ) ∣ (Γ , Δ)) ->
      Proof (head (Γ , Δ))
    S-head :
      (Γ1 Γ2 Δ1 Δ2 : ListTerm) ->
      Proof (head (union Γ1 Γ2 , union Δ1 Δ2)) ->
      Proof (head (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    M-head :
      (Γ1 Γ2 Δ1 Δ2 : ListTerm) ->
      Proof (head (Γ1 , Δ1)) ->
      Proof (head (Γ2 , Δ2)) ->
      Proof (head (union Γ1 Γ2 , union Δ1 Δ2))
    -- Logical Rules
    Z-L :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      Proof (G ∣ (Γ , Δ)) ->
      Proof (G ∣ (Γ ∷ botAG , Δ))
    Z-R :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      Proof (G ∣ (Γ , Δ)) ->
      Proof (G ∣ (Γ , Δ ∷ botAG))
    minus-L :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A : Term) ->
      Proof (G ∣ (Γ , Δ ∷ A)) ->
      Proof (G ∣ (Γ ∷ (-S A) , Δ))
    minus-R :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A : Term) ->
      Proof (G ∣ (Γ ∷ A , Δ)) ->
      Proof (G ∣ (Γ , Δ ∷ (-S A)))
    plus-L :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      Proof (G ∣(Γ ∷ A ∷ B , Δ)) ->
      Proof (G ∣ (Γ ∷ (A +S B), Δ))
    plus-R :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      Proof (G ∣ (Γ , Δ ∷ A ∷ B)) ->
      Proof (G ∣ (Γ , Δ ∷ (A +S B)))
    max-L :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      Proof (G ∣(Γ ∷ A , Δ)) ->
      Proof (G ∣(Γ ∷ B , Δ)) ->
      Proof (G ∣(Γ ∷ (A ⊔S B), Δ))
    max-R :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      Proof (G ∣(Γ , Δ ∷ A)∣(Γ , Δ ∷ B)) ->
      Proof (G ∣(Γ , Δ ∷ (A ⊔S B)))
    min-L :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      Proof (G ∣ (Γ ∷ A , Δ) ∣ (Γ ∷ B , Δ)) ->
      Proof (G ∣ (Γ ∷ (A ⊓S B), Δ))
    min-R :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      Proof (G ∣ (Γ , Δ ∷ A)) ->
      Proof (G ∣ (Γ , Δ ∷ B)) ->
      Proof (G ∣ (Γ , Δ ∷ (A ⊓S B)))
    Z-L-head :  
      (Γ Δ : ListTerm) ->
      Proof (head (Γ , Δ)) ->
      Proof (head (Γ ∷ botAG , Δ))
    Z-R-head :
      (Γ Δ : ListTerm) ->
      Proof (head (Γ , Δ)) ->
      Proof (head (Γ , Δ ∷ botAG))
    minus-L-head :
      (Γ Δ : ListTerm) ->
      (A : Term) ->
      Proof (head (Γ , Δ ∷ A)) ->
      Proof (head (Γ ∷ (-S A), Δ))
    minus-R-head :
      (Γ Δ : ListTerm) ->
      (A : Term) ->
      Proof (head (Γ ∷ A , Δ)) ->
      Proof (head (Γ , Δ ∷ (-S A)))
    plus-L-head :
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      Proof (head (Γ ∷ A ∷ B , Δ)) ->
      Proof (head (Γ ∷ (A +S B), Δ))
    plus-R-head :
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      Proof (head(Γ , Δ ∷ A ∷ B)) ->
      Proof (head(Γ , Δ ∷ (A +S B)))
    max-L-head :
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      Proof (head(Γ ∷ A , Δ)) ->
      Proof (head(Γ ∷ B , Δ)) ->
      Proof (head(Γ ∷ (A ⊔S B), Δ))
    max-R-head :
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      Proof (head(Γ , Δ ∷ A)∣(Γ , Δ ∷ B)) ->
      Proof (head(Γ , Δ ∷ (A ⊔S B)))
    min-L-head :
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      Proof (head (Γ ∷ A , Δ) ∣ (Γ ∷ B , Δ)) ->
      Proof (head (Γ ∷ (A ⊓S B), Δ))
    min-R-head :
      (Γ Δ : ListTerm) ->
      (A B : Term) ->
      Proof (head (Γ , Δ ∷ A)) ->
      Proof (head (Γ , Δ ∷ B)) ->
      Proof (head (Γ , Δ ∷ (A ⊓S B)))
    -- Exchange rules
    seq-exchange :
      (G : HSeq) ->
      (Γ Γ' Δ Δ' : ListTerm) ->
      ListExchange Γ Γ' ->
      ListExchange Δ Δ' ->
      Proof (G ∣ (Γ , Δ)) ->
      Proof (G ∣ (Γ' , Δ'))
    seq-exchange-head :
      (Γ Γ' Δ Δ' : ListTerm) ->
      ListExchange Γ Γ' ->
      ListExchange Δ Δ' ->
      Proof (head (Γ , Δ)) ->
      Proof (head (Γ' , Δ'))
    hseq-exchange :
      (G G' : HSeq) ->
      HSeqExchange G G' ->
      Proof G ->
      Proof G'

  ProofCong :
    {G G' : HSeq} ->
    Proof G ->
    G ≡ G' ->
    Proof G'
  ProofCong PG refl = PG
