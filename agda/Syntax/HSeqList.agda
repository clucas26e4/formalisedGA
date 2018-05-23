{-                                                  -
 -                                                  -
 -   Module of definition of a list of hypersequent -
 -                                                  -
 -                                                  -}

module Syntax.HSeqList where

  {- STDLIB -}
  open import Nat
  open import Equality

  {- Syntax -}
  open import Syntax.Term
  open import Syntax.ListTerm
  open import Syntax.Seq
  open import Syntax.HSeq
  open import Syntax.Proof

  {- Semantic -}
  open import Semantic.SemEquality
  open import Semantic.Interpretation

  data HSeqList : Set where
    []H :
      HSeqList
    _∷H_ :
      HSeq ->
      HSeqList ->
      HSeqList

  unionHL : (l1 l2 : HSeqList) -> HSeqList
  unionHL []H l2 = l2
  unionHL (x ∷H l1) l2 = x ∷H (unionHL l1 l2)

  --
  --
  -- Proof of a list of hypersequent
  --
  --

  data Prooflist : HSeqList -> Set where
    []P :
      Prooflist []H
    consP :
      {l : HSeqList} ->
      {G : HSeq} ->
      (pl : Prooflist l) ->
      (pG : Proof G) ->
      Prooflist (G ∷H l)

  Prooflist-L :
    (l1 l2 : HSeqList) ->
    (pl : Prooflist (unionHL l1 l2)) ->
    Prooflist l1
  Prooflist-L []H l2 pl =
    []P
  Prooflist-L (x ∷H l1) l2 (consP pl pG) =
    consP (Prooflist-L l1 l2 pl) pG

  Prooflist-R :
    (l1 l2 : HSeqList) ->
    (pl : Prooflist (unionHL l1 l2)) ->
    Prooflist l2
  Prooflist-R []H l2 pl =
    pl
  Prooflist-R (x ∷H l1) l2 (consP pl pG) =
    Prooflist-R l1 l2 pl

  --
  --
  -- Atomic HSeqList : List with only atomic hypersequent
  --
  --
  data AtomicHSeqList : HSeqList -> Set where
    atomic[]H :
      AtomicHSeqList []H
    atomicConsH :
      {l : HSeqList} ->
      {G : HSeq} ->
      AtomicHSeqList l ->
      maxOp G ≡ 0 ->
      AtomicHSeqList (G ∷H l)

  unionAtomicIsAtomic :
    {l l' : HSeqList} ->
    AtomicHSeqList l ->
    AtomicHSeqList l' ->
    AtomicHSeqList (unionHL l l')
  unionAtomicIsAtomic {[]H} {l'} al al' =
    al'
  unionAtomicIsAtomic {x ∷H l} {l'} (atomicConsH al x₁) al' =
    atomicConsH (unionAtomicIsAtomic al al') x₁

  data PosList : HSeqList -> Set where
    pos[]H :
      PosList []H
    pos∷H :
      {l : HSeqList} ->
      {H : HSeq} ->
      PosList l ->
      botAG ≤S ⟦ H ⟧ ->
      PosList (H ∷H l)

  unionPosIsPos :
    {l1 l2 : HSeqList} ->
    PosList l1 ->
    PosList l2 ->
    PosList (unionHL l1 l2)
  unionPosIsPos {[]H} {l2} posL1 posL2 =
    posL2
  unionPosIsPos {x ∷H l1} {l2} (pos∷H posL1 x₁) posL2 =
    pos∷H
      (unionPosIsPos posL1 posL2)
      x₁
