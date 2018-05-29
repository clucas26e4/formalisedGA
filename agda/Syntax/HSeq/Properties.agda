module Syntax.HSeq.Properties where
  {- STDLIB -}
  open import Nat
  open import Equality
  open import Data.Empty
  open import Relation.Nullary

  {- Syntax -}
  open import Syntax.Term
  open import Syntax.ListTerm
  open import Syntax.Seq
  open import Syntax.HSeq

  {- Semantic -}


  HSeqExchangeSym :
    {G G' : HSeq} ->
    (G=G' : HSeqExchange G G') ->
    HSeqExchange G' G
  HSeqExchangeSym idHE =
    idHE
  HSeqExchangeSym {G ∣ H ∣ H'} {G' ∣ .H' ∣ .H} (exHE G=G') =
    exHE (HSeqExchangeSym G=G')
  HSeqExchangeSym {head H ∣ H'} {head .H' ∣ .H} exHE-head =
    exHE-head
  HSeqExchangeSym (transHE G=G' G=G'') =
    transHE (HSeqExchangeSym G=G'') (HSeqExchangeSym G=G')
  HSeqExchangeSym (indHE G G' G=G') =
    indHE G' G (HSeqExchangeSym G=G')

  insertDoExchange :
    (G : HSeq) ->
    (H : Seq) ->
    HSeqExchange (G ∣ H) (insert G H)
  insertDoExchange (head H₁) H with nbOpSeq H₁ <? nbOpSeq H
  insertDoExchange (head H₁) H | yes p =
    idHE
  insertDoExchange (head H₁) H | no ¬p =
    exHE-head
  insertDoExchange (G ∣ H₁) H with nbOpSeq H₁ <? nbOpSeq H
  insertDoExchange (G ∣ H₁) H | yes p =
    idHE
  insertDoExchange (G ∣ H₁) H | no ¬p =
    transHE
      (exHE idHE)
      (indHE (G ∣ H) (insert G H) (insertDoExchange G H))

  orderDoExchange :
    (G : HSeq) ->
    HSeqExchange G (order G)
  orderDoExchange (head H) =
    idHE
  orderDoExchange (G ∣ H) = 
    transHE
      (indHE G (order G) (orderDoExchange G))
      (insertDoExchange (order G) H)

  unionHSeqKeepExchange :
    {G1 G2 G3 G4 : HSeq} ->
    (G1=G2 : HSeqExchange G1 G2) ->
    (G3=G4 : HSeqExchange G3 G4) ->
    HSeqExchange (unionHSeq G1 G3) (unionHSeq G2 G4)
  unionHSeqKeepExchange {G1} {head H} {head .H₁} {head H₁} G1=G2 idHE =
    indHE G1 (head H) G1=G2
  unionHSeqKeepExchange {G1} {head H} {head H₂} {head H₁} G1=G2 (transHE G3=G4 G3=G5) =
    transHE (unionHSeqKeepExchange G1=G2 G3=G4) (unionHSeqKeepExchange (idHE {head H}) G3=G5)
  unionHSeqKeepExchange {G1} {head H} {G3 ∣ H₂} {head H₁} G1=G2 (transHE G3=G4 G3=G5) = 
    transHE (unionHSeqKeepExchange G1=G2 G3=G4) (unionHSeqKeepExchange (idHE {head H}) G3=G5)
  unionHSeqKeepExchange {G1} {head H} {head H₂} {G4 ∣ H₁} G1=G2 (transHE G3=G4 G3=G5) = 
    transHE (unionHSeqKeepExchange G1=G2 G3=G4) (unionHSeqKeepExchange (idHE {head H}) G3=G5)
  unionHSeqKeepExchange {G1} {head H} {G3 ∣ H₂} {.G3 ∣ .H₂} G1=G2 idHE =
    indHE (unionHSeq G1 G3) (unionHSeq (head H) G3) (unionHSeqKeepExchange G1=G2 (idHE {G3}))
  unionHSeqKeepExchange {G1} {head H} {G3 ∣ .H₁ ∣ H₂} {G4 ∣ .H₂ ∣ H₁} G1=G2 (exHE G3=G4) =
    exHE (unionHSeqKeepExchange G1=G2 G3=G4)
  unionHSeqKeepExchange {G1} {head H} {.(head H₁) ∣ H₂} {.(head H₂) ∣ H₁} G1=G2 exHE-head =
    exHE G1=G2
  unionHSeqKeepExchange {G1} {head H} {G3 ∣ H₂} {G4 ∣ H₁} G1=G2 (transHE G3=G4 G3=G5) =
    transHE (unionHSeqKeepExchange G1=G2 G3=G4) (unionHSeqKeepExchange (idHE {head H}) G3=G5)
  unionHSeqKeepExchange {G1} {head H} {G3 ∣ H₂} {G4 ∣ .H₂} G1=G2 (indHE .G3 .G4 G3=G4) =
    indHE (unionHSeq G1 G3) (unionHSeq (head H) G4) (unionHSeqKeepExchange G1=G2 G3=G4)
  unionHSeqKeepExchange {G1} {G2 ∣ H} {head H₁} {.(head H₁)} G1=G2 idHE =
    indHE G1 (G2 ∣ H) G1=G2
  unionHSeqKeepExchange {G1} {G2 ∣ H} {G3 ∣ H₁} {.(G3 ∣ H₁)} G1=G2 idHE =
    indHE (unionHSeq G1 G3) (unionHSeq (G2 ∣ H) G3) (unionHSeqKeepExchange G1=G2 (idHE {G3}))
  unionHSeqKeepExchange {G1} {G2 ∣ H} {G3 ∣ H1 ∣ H2} {(G4 ∣ .H2 ∣ .H1)} G1=G2 (exHE G3=G4) =
    exHE (unionHSeqKeepExchange G1=G2 G3=G4)
  unionHSeqKeepExchange {G1} {G2 ∣ H} {(head H1 ∣ H2)} {(head .H2 ∣ .H1)} G1=G2 exHE-head =
    exHE G1=G2
  unionHSeqKeepExchange {G1} {G2 ∣ H} {head H₁} {head H₂} G1=G2 (transHE G3=G4 G3=G5) =
    transHE (unionHSeqKeepExchange G1=G2 G3=G4) (unionHSeqKeepExchange (idHE {G2 ∣ H}) G3=G5)
  unionHSeqKeepExchange {G1} {G2 ∣ H} {head H₁} {G4 ∣ H₂} G1=G2 (transHE G3=G4 G3=G5) =
    transHE (unionHSeqKeepExchange G1=G2 G3=G4) (unionHSeqKeepExchange (idHE {G2 ∣ H}) G3=G5)
  unionHSeqKeepExchange {G1} {G2 ∣ H} {G3 ∣ H₁} {head H₂} G1=G2 (transHE G3=G4 G3=G5) = 
    transHE (unionHSeqKeepExchange G1=G2 G3=G4) (unionHSeqKeepExchange (idHE {G2 ∣ H}) G3=G5)
  unionHSeqKeepExchange {G1} {G2 ∣ H} {G3 ∣ H₁} {G4 ∣ H₂} G1=G2 (transHE G3=G4 G3=G5) = 
    transHE (unionHSeqKeepExchange G1=G2 G3=G4) (unionHSeqKeepExchange (idHE {G2 ∣ H}) G3=G5)
  unionHSeqKeepExchange {G1} {G2 ∣ H} {.(G ∣ _)} {.(G' ∣ _)} G1=G2 (indHE G G' G3=G4) =
    indHE (unionHSeq G1 G) (unionHSeq (G2 ∣ H) G') (unionHSeqKeepExchange G1=G2 G3=G4)

  unionHSeqExStep :
    (G G' : HSeq) ->
    (H : Seq) ->
    HSeqExchange (unionHSeq (G ∣ H) G') (unionHSeq G (unionHSeq (head H) G'))
  unionHSeqExStep G (head H₁) H =
    idHE
  unionHSeqExStep G (G' ∣ H₁) H =
    indHE
      (unionHSeq (G ∣ H) G')
      (unionHSeq G (unionHSeq (head H) G'))
      (unionHSeqExStep G G' H)

  unionHSeqSymEx :
    (G1 G2 : HSeq) ->
    HSeqExchange (unionHSeq G1 G2) (unionHSeq G2 G1)
  unionHSeqSymEx (head H) (head H₁) =
    exHE-head
  unionHSeqSymEx (head H) (G2 ∣ H₁) =
    transHE
      {unionHSeq (head H) G2 ∣ H₁}
      {G2 ∣ H ∣ H₁}
      {G2 ∣ H₁ ∣ H}
      (indHE
        (unionHSeq (head H) G2)
        (G2 ∣ H)
        (unionHSeqSymEx (head H) G2))
      (exHE
        (idHE {G2}))
  unionHSeqSymEx (G1 ∣ H) (head H₁) =
    transHE
      {G1 ∣ H ∣ H₁}
      {G1 ∣ H₁ ∣ H}
      {unionHSeq (head H₁) G1 ∣ H}
      (exHE
        (idHE {G1}))
      (indHE
        (G1 ∣ H₁)
        (unionHSeq (head H₁) G1)
        (unionHSeqSymEx G1 (head H₁)))
  unionHSeqSymEx (G1 ∣ H) (G2 ∣ H₁) =
    transHE
      {unionHSeq (G1 ∣ H) G2 ∣ H₁}
      {unionHSeq G1 (unionHSeq (head H) G2) ∣ H₁}
      {unionHSeq (G2 ∣ H₁) G1 ∣ H}
      (indHE
        (unionHSeq (G1 ∣ H) G2)
        (unionHSeq G1 (unionHSeq (head H) G2))
        (unionHSeqExStep G1 G2 H))
      (transHE
        {unionHSeq G1 (unionHSeq (head H) G2) ∣ H₁}
        {unionHSeq G1 (G2 ∣ H) ∣ H₁}
        {unionHSeq (G2 ∣ H₁) G1 ∣ H}
        (indHE
          (unionHSeq G1 (unionHSeq (head H) G2))
          (unionHSeq G1 G2 ∣ H)
          (unionHSeqKeepExchange
            (idHE {G1})
            (unionHSeqSymEx (head H) G2)))
        (transHE
          {unionHSeq G1 G2 ∣ H ∣ H₁}
          {unionHSeq G1 G2 ∣ H₁ ∣ H}
          {unionHSeq (G2 ∣ H₁) G1 ∣ H}
          (exHE
            (idHE {unionHSeq G1 G2}))
          (indHE
            (unionHSeq G1 (G2 ∣ H₁))
            (unionHSeq (G2 ∣ H₁) G1)
            (unionHSeqSymEx G1 (G2 ∣ H₁)))))

  HSeqExchangeKeepOp :
    {G G' : HSeq} ->
    HSeqExchange G G' ->
    maxOp G ≡ maxOp G'
  HSeqExchangeKeepOp {G} {.G} idHE =
    refl
  HSeqExchangeKeepOp {(G ∣ H ∣ H')} {(G' ∣ .H' ∣ .H)} (exHE G=G') =
    begin
      maxOp G ⊔ nbOpSeq H ⊔ nbOpSeq H'
        ≡⟨ ⊔-assoc (maxOp G) (nbOpSeq H) (nbOpSeq H') ⟩
      maxOp G ⊔ (nbOpSeq H ⊔ nbOpSeq H')
        ≡⟨ cong
             (λ x -> x ⊔ (nbOpSeq H ⊔ nbOpSeq H'))
             (HSeqExchangeKeepOp G=G') ⟩
      maxOp G' ⊔ (nbOpSeq H ⊔ nbOpSeq H')
        ≡⟨ cong
             (λ x -> maxOp G' ⊔ x)
             (⊔-comm (nbOpSeq H) (nbOpSeq H')) ⟩
      maxOp G' ⊔ (nbOpSeq H' ⊔ nbOpSeq H)
        ≡⟨ sym
             (⊔-assoc (maxOp G') (nbOpSeq H') (nbOpSeq H)) ⟩
      maxOp G' ⊔ nbOpSeq H' ⊔ nbOpSeq H ∎
  HSeqExchangeKeepOp {(head H ∣ H')} {.(head _ ∣ _)} exHE-head =
    ⊔-comm (nbOpSeq H) (nbOpSeq H')
  HSeqExchangeKeepOp {G} {G'} (transHE G=G' G=G'') =
    trans
      (HSeqExchangeKeepOp G=G')
      (HSeqExchangeKeepOp G=G'')
  HSeqExchangeKeepOp {(.G ∣ H)} {.(G' ∣ _)} (indHE G G' G=G') =
    cong
      (λ x -> x ⊔ nbOpSeq H)
      (HSeqExchangeKeepOp G=G')
