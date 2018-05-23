module Semantic.Interpretation where
  {- STDLIB -}
  open import Nat

  {- Syntax -}
  open import Syntax.Term
  open import Syntax.ListTerm
  open import Syntax.Seq
  open import Syntax.HSeq

  {- Semantic -}
  open import Semantic.SemEquality
  open import Semantic.SemEquality.Properties

  ⟦_⟧L :
    ListTerm ->
    Term
  ⟦ [] ⟧L =
    botAG
  ⟦ Γ ∷ A ⟧L =
    ⟦ Γ ⟧L +S A

  ⟦_⟧S :
    Seq ->
    Term
  ⟦ (Γ , Δ) ⟧S =
    ⟦ Δ ⟧L -S (⟦ Γ ⟧L)

  ⟦_⟧ :
    HSeq ->
    Term
  ⟦ head H ⟧ =
    ⟦ H ⟧S
  ⟦ G ∣ H ⟧ =
    (⟦ G ⟧) ⊔S (⟦ H ⟧S)
