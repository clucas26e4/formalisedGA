{-                                                  -
 -                                                  -
 -     Module of definition of an sequent           -
 -                                                  -
 -                                                  -}

module Syntax.Seq where

  {- STDLIB -}
  open import Nat

  {- Syntax -}
  open import Syntax.Term
  open import Syntax.ListTerm

  {- Semantic -}

  data Seq : Set where
    _,_ :
      (T : ListTerm) ->
      (D : ListTerm) ->
      Seq

  nbOpSeq :
    (H : Seq) ->
    ℕ
  nbOpSeq (l1 , l2) =
    nbOpListFor l1 + nbOpListFor l2

  nbOpSeqTop :
    (H : Seq) ->
    ℕ
  nbOpSeqTop (l1 , l2) =
    topNbOpList l1 + topNbOpList l2

  unionSeq :
    Seq ->
    Seq ->
    Seq
  unionSeq (T , D) (T' , D') =
    (union T T' , union D D')
