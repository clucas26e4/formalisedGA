module Syntax.ListSeq where

  {- STDLIB -}
  open import Nat
  open import Equality

  {- Syntax -}
  open import Syntax.Term
  open import Syntax.ListTerm
  open import Syntax.Seq

  data ListSeq : Set where
    []S :
      ListSeq
    _∷S_ :
      (H : Seq) ->
      (l : ListSeq) ->
      ListSeq

  lengthListSeq :
    (l : ListSeq) ->
    ℕ
  lengthListSeq []S =
    0
  lengthListSeq (H ∷S l) =
    1 + (lengthListSeq l)

  --
  --
  -- List of sequent with a constant number of operator
  --
  --
  data ConstantList : ListSeq -> ℕ -> Set where
    Const[] :
      {k : ℕ} ->
      ConstantList []S k
    Const∷ :
      {k : ℕ} ->
      (H : Seq) ->
      {l : ListSeq} ->
      nbOpSeq H ≡ k ->
      ConstantList l k ->
      ConstantList (H ∷S l) k
