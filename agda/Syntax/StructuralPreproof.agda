module Syntax.StructuralPreproof where
  {- STDLIB -}
  open import Equality
  open import Nat

  {- Syntax -}
  open import Syntax.Term
  open import Syntax.ListTerm
  open import Syntax.ListTerm.Properties
  open import Syntax.Seq
  open import Syntax.HSeq

  {- Semantic -}


  data StructuralPreproof : HSeq -> Set where
    structuralLeaf :
      (G : HSeq) ->
      StructuralPreproof G
    SW :
      (G : HSeq) ->
      (Γ1 Γ2 Δ1 Δ2 : ListTerm) ->
      StructuralPreproof (G ∣ (Γ1 , Δ1)) ->
      StructuralPreproof (G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    SC :
      (G : HSeq) ->
      (Γ Δ : ListTerm) ->
      StructuralPreproof (G ∣ (Γ , Δ) ∣ (Γ , Δ)) ->
      StructuralPreproof (G ∣ (Γ , Δ))
    SS :
      (G : HSeq) ->
      (Γ1 Γ2 Δ1 Δ2 : ListTerm) ->
      StructuralPreproof (G ∣ (union Γ1 Γ2 , union Δ1 Δ2)) ->
      StructuralPreproof (G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    SW-head :
      (Γ1 Γ2 Δ1 Δ2 : ListTerm) ->
      StructuralPreproof (head (Γ1 , Δ1)) ->
      StructuralPreproof (head (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    SC-head :
      (Γ Δ : ListTerm) ->
      StructuralPreproof (head (Γ , Δ) ∣ (Γ , Δ)) ->
      StructuralPreproof (head (Γ , Δ))
    SS-head :
      (Γ1 Γ2 Δ1 Δ2 : ListTerm) ->
      StructuralPreproof (head (union Γ1 Γ2 , union Δ1 Δ2)) ->
      StructuralPreproof (head (Γ1 , Δ1) ∣ (Γ2 , Δ2))
    Sseq-exchange :
      (G : HSeq) ->
      (Γ Γ' Δ Δ' : ListTerm) ->
      ListExchange Γ Γ' ->
      ListExchange Δ Δ' ->
      StructuralPreproof (G ∣ (Γ , Δ)) ->
      StructuralPreproof (G ∣ (Γ' , Δ'))
    Sseq-exchange-head :
      (Γ Γ' Δ Δ' : ListTerm) ->
      ListExchange Γ Γ' ->
      ListExchange Δ Δ' ->
      StructuralPreproof (head (Γ , Δ)) ->
      StructuralPreproof (head (Γ' , Δ'))
    Shseq-exchange :
      (G G' : HSeq) ->
      HSeqExchange G G' ->
      StructuralPreproof G ->
      StructuralPreproof G'

  addFirst :
    (G : HSeq) ->
    {G' : HSeq} ->
    (sppG' : StructuralPreproof G') ->
    StructuralPreproof (unionHSeq G G')
  addFirst G (structuralLeaf G₁) =
    structuralLeaf (unionHSeq G G₁)
  addFirst G (SW G₁ Γ1 Γ2 Δ1 Δ2 sppG') =
    SW (unionHSeq G G₁) Γ1 Γ2 Δ1 Δ2 (addFirst G sppG')
  addFirst G (SC G₁ Γ Δ sppG') =
    SC (unionHSeq G G₁) Γ Δ (addFirst G sppG')
  addFirst G (SS G₁ Γ1 Γ2 Δ1 Δ2 sppG') =
    SS (unionHSeq G G₁) Γ1 Γ2 Δ1 Δ2 (addFirst G sppG')
  addFirst G (SW-head Γ1 Γ2 Δ1 Δ2 sppG') =
    SW G Γ1 Γ2 Δ1 Δ2 (addFirst G sppG')
  addFirst G (SC-head Γ Δ sppG') =
    SC G Γ Δ (addFirst G sppG')
  addFirst G (SS-head Γ1 Γ2 Δ1 Δ2 sppG') =
    SS G Γ1 Γ2 Δ1 Δ2 (addFirst G sppG')
  addFirst G (Sseq-exchange G₁ Γ Γ' Δ Δ' x x₁ sppG') =
    Sseq-exchange (unionHSeq G G₁) Γ Γ' Δ Δ' x x₁ (addFirst G sppG')
  addFirst G (Sseq-exchange-head Γ Γ' Δ Δ' x x₁ sppG') =
    Sseq-exchange G Γ Γ' Δ Δ' x x₁ (addFirst G sppG')
  addFirst G (Shseq-exchange G₁ G' x sppG') =
    Shseq-exchange (unionHSeq G G₁) (unionHSeq G G') (unionHSeqKeepExchange (idHE {G}) x) (addFirst G sppG')


  getStructuralLeaf :
    {G : HSeq} ->
    (sppG : StructuralPreproof G) ->
    HSeq
  getStructuralLeaf (structuralLeaf G) =
    G
  getStructuralLeaf (SW G Γ1 Γ2 Δ1 Δ2 sppG) =
    getStructuralLeaf sppG
  getStructuralLeaf (SC G Γ Δ sppG) = 
    getStructuralLeaf sppG
  getStructuralLeaf (SS G Γ1 Γ2 Δ1 Δ2 sppG) = 
    getStructuralLeaf sppG
  getStructuralLeaf (SW-head Γ1 Γ2 Δ1 Δ2 sppG) = 
    getStructuralLeaf sppG
  getStructuralLeaf (SC-head Γ Δ sppG) = 
    getStructuralLeaf sppG
  getStructuralLeaf (SS-head Γ1 Γ2 Δ1 Δ2 sppG) = 
    getStructuralLeaf sppG
  getStructuralLeaf (Sseq-exchange G Γ Γ' Δ Δ' x x₁ sppG) = 
    getStructuralLeaf sppG
  getStructuralLeaf (Sseq-exchange-head Γ Γ' Δ Δ' x x₁ sppG) = 
    getStructuralLeaf sppG
  getStructuralLeaf (Shseq-exchange G G' x sppG) = 
    getStructuralLeaf sppG

  keepLast :
    (G : HSeq) ->
    (H : Seq) ->
    StructuralPreproof (G ∣ H)
  keepLast (head (T , D)) (T₁ , D₁) =
    Shseq-exchange
      (head (T₁ , D₁) ∣ (T , D))
      (head (T , D) ∣ (T₁ , D₁))
      exHE-head
      (SW-head
        T₁
        T
        D₁
        D
        (structuralLeaf (head (T₁ , D₁))))
  keepLast (G ∣ (T , D)) (T' , D') =
    Shseq-exchange
      (G ∣ (T' , D') ∣ (T , D))
      (G ∣ (T , D) ∣ (T' , D'))
      (exHE
        (idHE {G}))
      (SW
        G
        T'
        T
        D'
        D
        (keepLast G (T' , D')))

  addFirstLeaf :
    {G : HSeq} ->
    (SPP : StructuralPreproof G) ->
    (G' : HSeq) ->
    getStructuralLeaf (addFirst (G') SPP) ≡ unionHSeq (G') (getStructuralLeaf SPP)
  addFirstLeaf (structuralLeaf G) G' =
    refl
  addFirstLeaf (SW G Γ1 Γ2 Δ1 Δ2 SPP) G' = 
    addFirstLeaf SPP G'
  addFirstLeaf (SC G Γ Δ SPP) G' = 
    addFirstLeaf SPP G'
  addFirstLeaf (SS G Γ1 Γ2 Δ1 Δ2 SPP) G' = 
    addFirstLeaf SPP G'
  addFirstLeaf (SW-head Γ1 Γ2 Δ1 Δ2 SPP) G' = 
    addFirstLeaf SPP G'
  addFirstLeaf (SC-head Γ Δ SPP) G' = 
    addFirstLeaf SPP G'
  addFirstLeaf (SS-head Γ1 Γ2 Δ1 Δ2 SPP) G' = 
    addFirstLeaf SPP G'
  addFirstLeaf (Sseq-exchange G Γ Γ' Δ Δ' x x₁ SPP) G' = 
    addFirstLeaf SPP G'
  addFirstLeaf (Sseq-exchange-head Γ Γ' Δ Δ' x x₁ SPP) G' = 
    addFirstLeaf SPP G'
  addFirstLeaf (Shseq-exchange G G'' x SPP) G' = 
    addFirstLeaf SPP G'

  keepLastLeaf :
    (G : HSeq) ->
    (H : Seq) ->
    getStructuralLeaf (keepLast G H) ≡ head H
  keepLastLeaf (head (T , D)) (T₁ , D₁) =
    refl
  keepLastLeaf (G ∣ (T , D)) (T₁ , D₁) =
    keepLastLeaf G (T₁ , D₁)

  continueStructuralPreproof :
    {G : HSeq} ->
    (SPP : StructuralPreproof G) ->
    (nextSPP : StructuralPreproof (getStructuralLeaf SPP)) ->
    StructuralPreproof G
  continueStructuralPreproof {.G} (structuralLeaf G) nextSPP =
    nextSPP
  continueStructuralPreproof {.(G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2))} (SW G Γ1 Γ2 Δ1 Δ2 SPP) nextSPP =
    SW G Γ1 Γ2 Δ1 Δ2 (continueStructuralPreproof SPP nextSPP)
  continueStructuralPreproof {.(G ∣ (Γ , Δ))} (SC G Γ Δ SPP) nextSPP = 
    SC G Γ Δ (continueStructuralPreproof SPP nextSPP)
  continueStructuralPreproof {.(G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2))} (SS G Γ1 Γ2 Δ1 Δ2 SPP) nextSPP = 
    SS G Γ1 Γ2 Δ1 Δ2 (continueStructuralPreproof SPP nextSPP)
  continueStructuralPreproof {.(head (Γ1 , Δ1) ∣ (Γ2 , Δ2))} (SW-head Γ1 Γ2 Δ1 Δ2 SPP) nextSPP = 
    SW-head Γ1 Γ2 Δ1 Δ2 (continueStructuralPreproof SPP nextSPP)
  continueStructuralPreproof {.(head (Γ , Δ))} (SC-head Γ Δ SPP) nextSPP =
    SC-head Γ Δ (continueStructuralPreproof SPP nextSPP)
  continueStructuralPreproof {.(head (Γ1 , Δ1) ∣ (Γ2 , Δ2))} (SS-head Γ1 Γ2 Δ1 Δ2 SPP) nextSPP = 
    SS-head Γ1 Γ2 Δ1 Δ2 (continueStructuralPreproof SPP nextSPP)
  continueStructuralPreproof {.(G ∣ (Γ' , Δ'))} (Sseq-exchange G Γ Γ' Δ Δ' x x₁ SPP) nextSPP = 
    Sseq-exchange G Γ Γ' Δ Δ' x x₁ (continueStructuralPreproof SPP nextSPP)
  continueStructuralPreproof {.(head (Γ' , Δ'))} (Sseq-exchange-head Γ Γ' Δ Δ' x x₁ SPP) nextSPP = 
    Sseq-exchange-head Γ Γ' Δ Δ' x x₁ (continueStructuralPreproof SPP nextSPP)
  continueStructuralPreproof {.G'} (Shseq-exchange G G' x SPP) nextSPP =
    Shseq-exchange G G' x (continueStructuralPreproof SPP nextSPP)

  getLeafContinuedProof :
    {G : HSeq} ->
    (SPP : StructuralPreproof G) ->
    (nextSPP : StructuralPreproof (getStructuralLeaf SPP)) ->
    getStructuralLeaf (continueStructuralPreproof SPP nextSPP) ≡ getStructuralLeaf nextSPP
  getLeafContinuedProof (structuralLeaf G) nextSPP =
    refl
  getLeafContinuedProof (SW G Γ1 Γ2 Δ1 Δ2 SPP) nextSPP = 
    getLeafContinuedProof SPP nextSPP
  getLeafContinuedProof (SC G Γ Δ SPP) nextSPP = 
    getLeafContinuedProof SPP nextSPP
  getLeafContinuedProof (SS G Γ1 Γ2 Δ1 Δ2 SPP) nextSPP = 
    getLeafContinuedProof SPP nextSPP
  getLeafContinuedProof (SW-head Γ1 Γ2 Δ1 Δ2 SPP) nextSPP = 
    getLeafContinuedProof SPP nextSPP
  getLeafContinuedProof (SC-head Γ Δ SPP) nextSPP = 
    getLeafContinuedProof SPP nextSPP
  getLeafContinuedProof (SS-head Γ1 Γ2 Δ1 Δ2 SPP) nextSPP = 
    getLeafContinuedProof SPP nextSPP
  getLeafContinuedProof (Sseq-exchange G Γ Γ' Δ Δ' x x₁ SPP) nextSPP = 
    getLeafContinuedProof SPP nextSPP
  getLeafContinuedProof (Sseq-exchange-head Γ Γ' Δ Δ' x x₁ SPP) nextSPP = 
    getLeafContinuedProof SPP nextSPP
  getLeafContinuedProof (Shseq-exchange G G' x SPP) nextSPP = 
    getLeafContinuedProof SPP nextSPP

  leafDecreaseOp :
    {G : HSeq} ->
    (SPP : StructuralPreproof G) ->
    (maxG=0 : maxOp G ≡ 0) ->
    maxOp (getStructuralLeaf SPP) ≡ 0
  leafDecreaseOp {.G} (structuralLeaf G) maxG=0 = 
    maxG=0
  leafDecreaseOp {.(G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2))} (SW G Γ1 Γ2 Δ1 Δ2 SPP) maxG=0 = 
    leafDecreaseOp
      SPP
      (a⊔b⊔c=0=>a⊔b=0
        {maxOp G}
        maxG=0)
  leafDecreaseOp {.(G ∣ (Γ , Δ))} (SC G Γ Δ SPP) maxG=0 = 
    leafDecreaseOp
      SPP
      (a⊔b=0=>a⊔b⊔b=0
        {maxOp G}
        maxG=0)
  leafDecreaseOp {.(G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2))} (SS G Γ1 Γ2 Δ1 Δ2 SPP) maxG=0 = 
    leafDecreaseOp
      SPP
      (begin
        maxOp G ⊔ (nbOpListFor (union Γ1 Γ2) + nbOpListFor (union Δ1 Δ2))
          ≡⟨ cong
               (λ x -> maxOp G ⊔ x)
               (begin
                 (nbOpListFor (union Γ1 Γ2) + nbOpListFor (union Δ1 Δ2))
                   ≡⟨ cong₂
                        (λ x y -> x + y)
                        (unionOp Γ1 Γ2)
                        (unionOp Δ1 Δ2) ⟩
                 nbOpListFor Γ1 + nbOpListFor Γ2 + (nbOpListFor Δ1 + nbOpListFor Δ2)
                   ≡⟨ +-assoc (nbOpListFor Γ1) (nbOpListFor Γ2) (nbOpListFor Δ1 + nbOpListFor Δ2) ⟩
                 nbOpListFor Γ1 + (nbOpListFor Γ2 + (nbOpListFor Δ1 + nbOpListFor Δ2))
                   ≡⟨ cong
                        (λ x -> nbOpListFor Γ1 + x)
                        (+-comm (nbOpListFor Γ2) (nbOpListFor Δ1 + nbOpListFor Δ2)) ⟩
                 nbOpListFor Γ1 + (nbOpListFor Δ1 + nbOpListFor Δ2 + nbOpListFor Γ2)
                   ≡⟨ cong
                        (λ x -> nbOpListFor Γ1 + x)
                        (+-assoc (nbOpListFor Δ1) (nbOpListFor Δ2) (nbOpListFor Γ2)) ⟩
                 nbOpListFor Γ1 + (nbOpListFor Δ1 + (nbOpListFor Δ2 + nbOpListFor Γ2))
                   ≡⟨ sym (+-assoc (nbOpListFor Γ1) (nbOpListFor Δ1) (nbOpListFor Δ2 + nbOpListFor Γ2)) ⟩
                 nbOpListFor Γ1 + nbOpListFor Δ1 + (nbOpListFor Δ2 + nbOpListFor Γ2)
                   ≡⟨ cong
                        (λ x -> nbOpListFor Γ1 + nbOpListFor Δ1 + x)
                        (+-comm (nbOpListFor Δ2) (nbOpListFor Γ2)) ⟩
                 nbOpListFor Γ1 + nbOpListFor Δ1 + (nbOpListFor Γ2 + nbOpListFor Δ2) ∎) ⟩
        maxOp G ⊔ ((nbOpListFor Γ1 + nbOpListFor Δ1) + (nbOpListFor Γ2 + nbOpListFor Δ2))
          ≡⟨ a⊔b⊔c=0=>a⊔b+c=0
               {maxOp G}
               maxG=0 ⟩
        0 ∎)
  leafDecreaseOp {.(head (Γ1 , Δ1) ∣ (Γ2 , Δ2))} (SW-head Γ1 Γ2 Δ1 Δ2 SPP) maxG=0 = 
    leafDecreaseOp
      SPP
      (≤-antisym
        (cong-≤-r
          {nbOpListFor Γ1 + nbOpListFor Δ1 ⊔ (nbOpListFor Γ2 + nbOpListFor Δ2)}
          maxG=0
          ≤-⊔)
        z≤n)
  leafDecreaseOp {.(head (Γ , Δ))} (SC-head Γ Δ SPP) maxG=0 = 
    leafDecreaseOp
      SPP
      (cong
        (λ x -> x ⊔ x)
        maxG=0)
  leafDecreaseOp {.(head (Γ1 , Δ1) ∣ (Γ2 , Δ2))} (SS-head Γ1 Γ2 Δ1 Δ2 SPP) maxG=0 = 
    leafDecreaseOp
      SPP
      (begin
        (nbOpListFor (union Γ1 Γ2) + nbOpListFor (union Δ1 Δ2))
          ≡⟨ cong₂
               (λ x y -> x + y)
               (unionOp Γ1 Γ2)
               (unionOp Δ1 Δ2) ⟩
        nbOpListFor Γ1 + nbOpListFor Γ2 + (nbOpListFor Δ1 + nbOpListFor Δ2)
          ≡⟨ +-assoc (nbOpListFor Γ1) (nbOpListFor Γ2) (nbOpListFor Δ1 + nbOpListFor Δ2) ⟩
        nbOpListFor Γ1 + (nbOpListFor Γ2 + (nbOpListFor Δ1 + nbOpListFor Δ2))
          ≡⟨ cong
               (λ x -> nbOpListFor Γ1 + x)
               (+-comm (nbOpListFor Γ2) (nbOpListFor Δ1 + nbOpListFor Δ2)) ⟩
        nbOpListFor Γ1 + (nbOpListFor Δ1 + nbOpListFor Δ2 + nbOpListFor Γ2)
          ≡⟨ cong
               (λ x -> nbOpListFor Γ1 + x)
               (+-assoc (nbOpListFor Δ1) (nbOpListFor Δ2) (nbOpListFor Γ2)) ⟩
        nbOpListFor Γ1 + (nbOpListFor Δ1 + (nbOpListFor Δ2 + nbOpListFor Γ2))
          ≡⟨ sym (+-assoc (nbOpListFor Γ1) (nbOpListFor Δ1) (nbOpListFor Δ2 + nbOpListFor Γ2)) ⟩
        nbOpListFor Γ1 + nbOpListFor Δ1 + (nbOpListFor Δ2 + nbOpListFor Γ2)
          ≡⟨ cong
               (λ x -> nbOpListFor Γ1 + nbOpListFor Δ1 + x)
               (+-comm (nbOpListFor Δ2) (nbOpListFor Γ2)) ⟩
        nbOpListFor Γ1 + nbOpListFor Δ1 + (nbOpListFor Γ2 + nbOpListFor Δ2)
          ≡⟨ a⊔b=0=>a+b=0 {nbOpListFor Γ1 + nbOpListFor Δ1} maxG=0 ⟩
        0 ∎)
  leafDecreaseOp {.(G ∣ (Γ' , Δ'))} (Sseq-exchange G Γ Γ' Δ Δ' x x₁ SPP) maxG=0 = 
    leafDecreaseOp
      SPP
      (trans
        (cong
          (λ x -> maxOp G ⊔ x)
          (begin
            nbOpListFor Γ + nbOpListFor Δ
              ≡⟨ cong
                   (λ x -> nbOpListFor Γ + x)
                   (ListExchangeKeepOp
                     x₁) ⟩
            nbOpListFor Γ + nbOpListFor Δ'
              ≡⟨ cong
                   (λ x -> x + nbOpListFor Δ')
                   (ListExchangeKeepOp
                     x) ⟩
            nbOpListFor Γ' + nbOpListFor Δ' ∎))
        maxG=0)
  leafDecreaseOp {.(head (Γ' , Δ'))} (Sseq-exchange-head Γ Γ' Δ Δ' x x₁ SPP) maxG=0 = 
    leafDecreaseOp
      SPP
      (trans
        (begin
          nbOpListFor Γ + nbOpListFor Δ
            ≡⟨ cong
                 (λ x -> nbOpListFor Γ + x)
                 (ListExchangeKeepOp
                   x₁) ⟩
          nbOpListFor Γ + nbOpListFor Δ'
            ≡⟨ cong
                 (λ x -> x + nbOpListFor Δ')
                 (ListExchangeKeepOp
                   x) ⟩
          nbOpListFor Γ' + nbOpListFor Δ' ∎)
        maxG=0)
  leafDecreaseOp {.G'} (Shseq-exchange G G' x SPP) maxG=0 = 
    leafDecreaseOp
      SPP
      (trans
        (HSeqExchangeKeepOp x)
        maxG=0)
