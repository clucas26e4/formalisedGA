module Syntax.HSeq.Ordered where

  {- STDLIB -}
  open import Nat
  open import Equality
  open import Data.Empty
  open import Relation.Nullary

  {- SYNTAX -}
  open import Syntax.Term
  open import Syntax.ListTerm
  open import Syntax.Seq
  open import Syntax.HSeq
  open import Syntax.ListSeq

  {- SEMANTIC -}
  
  data OrderedHSeq : HSeq -> Set where
    HeadOrdered :
      (H : Seq) ->
      OrderedHSeq (head H)
    ConsOrdered :
      {G : HSeq} ->
      {H : Seq} ->
      OrderedHSeq G ->
      maxOp G ≤ nbOpSeq H ->
      OrderedHSeq (G ∣ H)

  lengthLastBlock :
    {G : HSeq} ->
    (OG : OrderedHSeq G) ->
    ℕ
  lengthLastBlock {head H} OG =
    1
  lengthLastBlock {G ∣ H} OG with maxOp G <? nbOpSeq H
  lengthLastBlock {G ∣ H} OG | yes p =
    1
  lengthLastBlock {G ∣ H} (ConsOrdered OG x) | no ¬p =
    suc (lengthLastBlock OG)

  substOrdered :
    {G G' : HSeq} ->
    (G=G' : G ≡ G') ->
    (OG : OrderedHSeq G) ->
    OrderedHSeq G'
  substOrdered refl OG = OG

  maxOpOrder :
    {G : HSeq} ->
    {H : Seq} ->
    (OGH : OrderedHSeq (G ∣ H)) ->
    maxOp (G ∣ H) ≡ nbOpSeq H
  maxOpOrder (ConsOrdered OGH x) =
    k≤k'=>k⊔k'=k' x

  insertMaxOp :
    (G : HSeq) ->
    (H : Seq) ->
    maxOp (insert G H) ≡ maxOp G ⊔ nbOpSeq H
  insertMaxOp (head H₁) H with nbOpSeq H₁ <? nbOpSeq H
  insertMaxOp (head H₁) H | yes p =
    refl
  insertMaxOp (head H₁) H | no ¬p =
    ⊔-comm (nbOpSeq H) (nbOpSeq H₁)
  insertMaxOp (G ∣ H₁) H with nbOpSeq H₁ <? nbOpSeq H
  insertMaxOp (G ∣ H₁) H | yes p =
    refl
  insertMaxOp (G ∣ H₁) H | no ¬p =
    begin
      maxOp (insert G H) ⊔ nbOpSeq H₁
        ≡⟨ cong (λ x -> x ⊔ nbOpSeq H₁) (insertMaxOp G H) ⟩
      maxOp G ⊔ nbOpSeq H ⊔ nbOpSeq H₁
        ≡⟨ ⊔-assoc (maxOp G) (nbOpSeq H) (nbOpSeq H₁) ⟩
      maxOp G ⊔ (nbOpSeq H ⊔ nbOpSeq H₁)
        ≡⟨ cong (λ x -> maxOp G ⊔ x) (⊔-comm (nbOpSeq H) (nbOpSeq H₁)) ⟩
      maxOp G ⊔ (nbOpSeq H₁ ⊔ nbOpSeq H)
        ≡⟨ sym (⊔-assoc (maxOp G) (nbOpSeq H₁) (nbOpSeq H)) ⟩
      maxOp G ⊔ nbOpSeq H₁ ⊔ nbOpSeq H ∎

  insertKeepOrder :
    {G : HSeq} ->
    {H : Seq} ->
    (OG : OrderedHSeq G) ->
    OrderedHSeq (insert G H)
  insertKeepOrder {head H₁} {H} OG with nbOpSeq H₁ <? nbOpSeq H
  insertKeepOrder {head H₁} {H} OG | yes p =
    ConsOrdered (HeadOrdered H₁) (≤-trans k≤sk p)
  insertKeepOrder {head H₁} {H} OG | no ¬p =
    ConsOrdered (HeadOrdered H) (¬k<k'=>k'≤k ¬p)
  insertKeepOrder {G ∣ H₁} {H} OG  with nbOpSeq H₁ <? nbOpSeq H
  insertKeepOrder {G ∣ H₁} {H} OG | yes p =
    ConsOrdered OG (≤-trans
                     (cong-≤-l
                       (sym
                         (maxOpOrder OG))
                       ≤-refl)
                     (≤-trans
                       k≤sk
                       p))
  insertKeepOrder {G ∣ H₁} {H} (ConsOrdered OG x) | no ¬p =
    ConsOrdered (insertKeepOrder OG) (cong-≤-l
                                       (sym (insertMaxOp G H))
                                       (⊔-≤ x (¬k<k'=>k'≤k ¬p)))
   
  orderCorrect :
    (G : HSeq) ->
    OrderedHSeq (order G)
  orderCorrect (head H) =
    HeadOrdered H
  orderCorrect (G ∣ H) with order G | inspect order G
  orderCorrect (G ∣ H) | head H₁ | [ eq ] with nbOpSeq H₁ <? nbOpSeq H
  orderCorrect (G ∣ H) | head H₁ | [ eq ] | yes p =
    ConsOrdered (HeadOrdered H₁) (≤-trans k≤sk p)
  orderCorrect (G ∣ H) | head H₁ | [ eq ] | no ¬p =
    ConsOrdered (HeadOrdered H) (¬k<k'=>k'≤k ¬p)
  orderCorrect (G ∣ H) | OG ∣ H₁ | [ eq ] with nbOpSeq H₁ <? nbOpSeq H
  orderCorrect (G ∣ H) | OG ∣ H₁ | [ eq ] | yes p =
    ConsOrdered (substOrdered eq (orderCorrect G)) (≤-trans
                                                     (≤-trans
                                                       (cong-≤-l
                                                         (sym
                                                           (maxOpOrder
                                                             (substOrdered eq (orderCorrect G))))
                                                       ≤-refl)
                                                     k≤sk)
                                                   p)
  orderCorrect (G ∣ H) | OG ∣ H₁ | [ eq ] | no ¬p with substOrdered eq (orderCorrect G)
  orderCorrect (G ∣ H) | OG ∣ H₁ | [ eq ] | no ¬p | ConsOrdered OG₁ x₁ =
    ConsOrdered (insertKeepOrder OG₁) (cong-≤-l
                                        (sym (insertMaxOp OG H))
                                        (⊔-≤ x₁ (¬k<k'=>k'≤k ¬p)))
