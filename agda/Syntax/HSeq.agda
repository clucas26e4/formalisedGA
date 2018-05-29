{-                                                  -
 -                                                  -
 -     Module of definition of an hypersequent      -
 -                                                  -
 -                                                  -}

module Syntax.HSeq where

  {- STDLIB -}
  open import Nat
  open import Equality
  open import Data.Empty
  open import Relation.Nullary

  {- Syntax -}
  open import Syntax.Term
  open import Syntax.ListTerm
  open import Syntax.Seq


  {- Semantic -}

  {- Definition of an hypersequent -}
  data HSeq : Set where
    head :
      (H : Seq) ->
      HSeq
    _∣_ :
      (G : HSeq) ->
      (H : Seq) ->
      HSeq

  infixl 50 _∣_

  maxOp :
    (G : HSeq) ->
    ℕ
  maxOp (head H) =
    nbOpSeq H
  maxOp (G ∣ H) =
    maxOp G ⊔ nbOpSeq H

  size :
    (G : HSeq) ->
    ℕ
  size (head H) =
    1
  size (G ∣ H) =
    suc (size G)


  insert :
    (G : HSeq) ->
    (H : Seq) ->
    HSeq
  insert (head H₁) H with nbOpSeq H₁ <? nbOpSeq H
  insert (head H₁) H | yes p =
    head H₁ ∣ H
  insert (head H₁) H | no ¬p =
    head H ∣ H₁
  insert (G ∣ H₁) H with nbOpSeq H₁ <? nbOpSeq H
  insert (G ∣ H₁) H | yes p =
    G ∣ H₁ ∣ H
  insert (G ∣ H₁) H | no ¬p =
    (insert G H) ∣ H₁

  order :
    (G : HSeq) ->
    HSeq
  order (head H) =
    head H
  order (G ∣ H) =
    insert (order G) H

  --
  --
  -- Exchange
  --
  --
  data HSeqExchange : (G G' : HSeq) -> Set where
    idHE :
      {G : HSeq} ->
      HSeqExchange G G
    exHE :
      {G G' : HSeq}{H H' : Seq} ->
      (G=G' : HSeqExchange G G') ->
      HSeqExchange (G ∣ H ∣ H') (G' ∣ H' ∣ H)
    exHE-head :
      {H H' : Seq} ->
      HSeqExchange (head H ∣ H') (head H' ∣ H)
    transHE :
      {G₁ G₂ G₃ : HSeq} ->
      (G₁=G₂ : HSeqExchange G₁ G₂) ->
      (G₂=G₃ : HSeqExchange G₂ G₃) ->
      HSeqExchange G₁ G₃
    indHE :
      (G G' : HSeq) ->
      {H : Seq} ->
      (G=G' : HSeqExchange G G') ->
      HSeqExchange (G ∣ H) (G' ∣ H)

  push-front :
    (G : HSeq) ->
    (H : Seq) ->
    HSeq
  push-front (head H') H =
    head H ∣ H'
  push-front (G ∣ H') H =
    (push-front G H) ∣ H'

  unionHSeq :
    (G G' : HSeq) ->
    HSeq
  unionHSeq G (head H) =
    G ∣ H
  unionHSeq G (G' ∣ H) =
    (unionHSeq G G') ∣ H
