module Syntax.Proof.Completeness where
  {- STDLIB -}
  open import Nat
  open import Equality
  open import Data.Empty
  open import Relation.Nullary
  open import Data.Product
  open import Function

  {- Syntax -}
  open import Syntax.Term
  open import Syntax.ListTerm
  open import Syntax.ListTerm.Canonic
  open import Syntax.ListTerm.Properties
  open import Syntax.Seq
  open import Syntax.Seq.Properties
  open import Syntax.HSeq
  open import Syntax.Proof
  open import Syntax.Proof.Invertibility
  open import Syntax.HSeqList
  open import Syntax.Preproof
  open import Syntax.Preproof.Leaf
  open import Syntax.Preproof.Create
  open import Syntax.StructuralPreproof

  {- Semantic -}
  open import Semantic.SemEquality
  open import Semantic.SemEquality.Properties
  open import Semantic.Interpretation
  open import Semantic.LinearComb

  postulate
    condAtomicValid :
      (G : HSeq) ->
      maxOp G ≡ 0 ->
      botAG ≤S ⟦ G ⟧ ->
      ∃[ LCG ] (valid-LC LCG × ⟦ toSeq {G} LCG ⟧S ≡ₛ botAG)

  Γ⊢Γ :
    (Γ : ListTerm) ->
    Proof (head (Γ , Γ))
  Γ⊢Γ [] =
    Δ-ax
  Γ⊢Γ (Γ ∷ A) =
    M-head
      Γ
      ([] ∷ A)
      Γ
      ([] ∷ A)
      (Γ⊢Γ Γ)
      (ax A)

  finishStructuralProof :
    (G : HSeq) ->
    (SPP : StructuralPreproof G) ->
    (proof : Proof (getStructuralLeaf SPP)) ->
    Proof G
  finishStructuralProof G (structuralLeaf .G) proof =
    proof
  finishStructuralProof .(G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2)) (SW G Γ1 Γ2 Δ1 Δ2 SPP) proof =
    W G Γ1 Γ2 Δ1 Δ2 (finishStructuralProof (G ∣ (Γ1 , Δ1)) SPP proof)
  finishStructuralProof .(G ∣ (Γ , Δ)) (SC G Γ Δ SPP) proof =
    C G Γ Δ (finishStructuralProof (G ∣ (Γ , Δ) ∣ (Γ , Δ)) SPP proof)
  finishStructuralProof .(G ∣ (Γ1 , Δ1) ∣ (Γ2 , Δ2)) (SS G Γ1 Γ2 Δ1 Δ2 SPP) proof =
    S G Γ1 Γ2 Δ1 Δ2 (finishStructuralProof (G ∣ (union Γ1 Γ2 , union Δ1 Δ2)) SPP proof)
  finishStructuralProof .(head (Γ1 , Δ1) ∣ (Γ2 , Δ2)) (SW-head Γ1 Γ2 Δ1 Δ2 SPP) proof =
    W-head Γ1 Γ2 Δ1 Δ2 (finishStructuralProof (head (Γ1 , Δ1)) SPP proof)
  finishStructuralProof .(head (Γ , Δ)) (SC-head Γ Δ SPP) proof =
    C-head Γ Δ (finishStructuralProof (head (Γ , Δ) ∣ (Γ , Δ)) SPP proof)
  finishStructuralProof .(head (Γ1 , Δ1) ∣ (Γ2 , Δ2)) (SS-head Γ1 Γ2 Δ1 Δ2 SPP) proof =
    S-head Γ1 Γ2 Δ1 Δ2 (finishStructuralProof (head (union Γ1 Γ2 , union Δ1 Δ2)) SPP proof)
  finishStructuralProof .(G ∣ (Γ' , Δ')) (Sseq-exchange G Γ Γ' Δ Δ' x x₁ SPP) proof =
    seq-exchange G Γ Γ' Δ Δ' x x₁ (finishStructuralProof (G ∣ (Γ , Δ)) SPP proof)
  finishStructuralProof .(head (Γ' , Δ')) (Sseq-exchange-head Γ Γ' Δ Δ' x x₁ SPP) proof =
    seq-exchange-head Γ Γ' Δ Δ' x x₁ (finishStructuralProof (head (Γ , Δ)) SPP proof)
  finishStructuralProof G (Shseq-exchange G₁ .G x SPP) proof =
    hseq-exchange G₁ G x (finishStructuralProof G₁ SPP proof)

  atomicValidLemma1 :
      (G : HSeq) ->
      (maxOp G ≡ 0) ->
      (LCG : LinearCombinaison G) ->
      (vLCG : valid-LC LCG) ->
      (T D : ListTerm) ->
      (toSeq (identityLC (getStructuralLeaf (createStructuralPreproof vLCG))) ≡ (T , D)) ->
      nbOpListFor T ≡ 0
  atomicValidLemma1 G maxG LCG vLCG T D eq =
    ≤-antisym
      (≤-trans
        {j = nbOpListFor T + nbOpListFor D}
        a≤a+b
        (cong-≤-l
          {nbOpSeq (toSeq (identityLC (getStructuralLeaf (createStructuralPreproof vLCG))))}
          (cong
            nbOpSeq
            eq)
          (cong-≤-l
            (sym
              (identityLCKeepOp
                (getStructuralLeaf (createStructuralPreproof vLCG))
                (leafDecreaseOp (createStructuralPreproof vLCG) maxG)))
            ≤-refl)))
      z≤n

  atomicValidLemma2 :
      (G : HSeq) ->
      (maxOp G ≡ 0) ->
      (LCG : LinearCombinaison G) ->
      (vLCG : valid-LC LCG) ->
      (T D : ListTerm) ->
      (toSeq (identityLC (getStructuralLeaf (createStructuralPreproof vLCG))) ≡ (T , D)) ->
      nbOpListFor D ≡ 0
  atomicValidLemma2 G maxG LCG vLCG T D eq = 
    ≤-antisym
      (≤-trans
        {j = nbOpListFor T + nbOpListFor D}
        (a≤b=>c≤d=>a+c≤b+d
          (z≤n {nbOpListFor T})
          (≤-refl {nbOpListFor D}))
        (cong-≤-l
          {nbOpSeq (toSeq (identityLC (getStructuralLeaf (createStructuralPreproof vLCG))))}
          (cong
            nbOpSeq
            eq)
          (cong-≤-l
            (sym
              (identityLCKeepOp
                (getStructuralLeaf (createStructuralPreproof vLCG))
                (leafDecreaseOp (createStructuralPreproof vLCG) maxG)))
            ≤-refl)))
      z≤n

  atomicValidLemma3 :
      (G : HSeq) ->
      (maxG : maxOp G ≡ 0) ->
      (LCG : LinearCombinaison G) ->
      (vLCG : valid-LC LCG) ->
      ⟦ toSeq LCG ⟧S ≡ₛ botAG ->
      (T D : ListTerm) ->
      (eq : toSeq (identityLC (getStructuralLeaf (createStructuralPreproof vLCG))) ≡ (T , D)) ->
      toCanonic T (atomicValidLemma1 G maxG LCG vLCG T D eq) ≡ toCanonic D (atomicValidLemma2 G maxG LCG vLCG T D eq)
  atomicValidLemma3 G maxG LCG vLCG LCG=0 T D eq  =
    sameVar=>sameCanonic
      (toCanonic T (atomicValidLemma1 G maxG LCG vLCG T D eq))
      (toCanonic D (atomicValidLemma2 G maxG LCG vLCG T D eq))
      (toCanonicIsCanonic T (atomicValidLemma1 G maxG LCG vLCG T D eq))
      (toCanonicIsCanonic D (atomicValidLemma2 G maxG LCG vLCG T D eq))
      λ k ->
        (⟦T⟧=⟦D⟧=>sameVar
          (toCanonic T (atomicValidLemma1 G maxG LCG vLCG T D eq))
          (toCanonic D (atomicValidLemma2 G maxG LCG vLCG T D eq))
          (⟦T,D⟧=0=>⟦T⟧=⟦D⟧
            (toCanonic T (atomicValidLemma1 G maxG LCG vLCG T D eq))
            (toCanonic D (atomicValidLemma2 G maxG LCG vLCG T D eq))
            (beginₛ
              ⟦ toCanonic D (atomicValidLemma2 G maxG LCG vLCG T D eq) ⟧L -S ⟦ toCanonic T (atomicValidLemma1 G maxG LCG vLCG T D eq) ⟧L
                ≡ₛ⟨ ctxtₛ
                      (● -C (CC (⟦ toCanonic T (atomicValidLemma1 G maxG LCG vLCG T D eq) ⟧L)))
                      (ListExchangeSem
                        (ListExchangeSym
                          (toCanonicDoExchange D (atomicValidLemma2 G maxG LCG vLCG T D eq)))) ⟩
              ⟦ D ⟧L -S ⟦ toCanonic T (atomicValidLemma1 G maxG LCG vLCG T D eq) ⟧L
                ≡ₛ⟨ ctxtₛ
                      ((CC ⟦ D ⟧L) -C ●)
                      (ListExchangeSem
                        (ListExchangeSym
                          (toCanonicDoExchange T (atomicValidLemma1 G maxG LCG vLCG T D eq)))) ⟩
              ⟦ D ⟧L -S ⟦ T ⟧L
                ≡ₛ⟨ congₛ
                      (cong
                        ⟦_⟧S
                        (sym eq)) ⟩
              ⟦ toSeq (identityLC (getStructuralLeaf (createStructuralPreproof vLCG))) ⟧S
                ≡ₛ⟨ congₛ
                      (cong
                        (⟦_⟧S ∘ HSeqToSeq)
                        (sym (finalStructuralPreproofCorrect vLCG))) ⟩
              ⟦ HSeqToSeq (getStructuralLeaf (finalStructuralPreproof vLCG)) ⟧S
                ≡ₛ⟨ finalStructuralPreproofCorrectLemma
                      vLCG
                      LCG=0 ⟩
              botAG ∎ₛ))
          k
          (canonicNoOp (toCanonicIsCanonic T (atomicValidLemma1 G maxG LCG vLCG T D eq)))
          (canonicNoOp (toCanonicIsCanonic D (atomicValidLemma2 G maxG LCG vLCG T D eq))))
  
  atomicValid :
    (G : HSeq) ->
    (maxOp G ≡ 0) ->
    (LCG : LinearCombinaison G) ->
    (vLCG : valid-LC LCG) ->
    ⟦ toSeq LCG ⟧S ≡ₛ botAG ->
    Proof G
  atomicValid G maxG=0 LCG vLCG LCG=0 with toSeq (identityLC (getStructuralLeaf (createStructuralPreproof vLCG))) | inspect toSeq (identityLC (getStructuralLeaf (createStructuralPreproof vLCG)))
  atomicValid G maxG=0 LCG vLCG LCG=0 | (T , D) | [ eq ] =
    finishStructuralProof
      G
      (finalStructuralPreproof vLCG)
      (ProofCong
        (ProofCong
          (seq-exchange-head
            (toCanonic T (atomicValidLemma1 G maxG=0 LCG vLCG T D eq))
            T
            (toCanonic D (atomicValidLemma2 G maxG=0 LCG vLCG T D eq))
            D
            (ListExchangeSym
              (toCanonicDoExchange
                T
                (atomicValidLemma1 G maxG=0 LCG vLCG T D eq)))
            (ListExchangeSym
              (toCanonicDoExchange
                D
                (atomicValidLemma2 G maxG=0 LCG vLCG T D eq)))
            (ProofCong
              (Γ⊢Γ
                (toCanonic T (atomicValidLemma1 G maxG=0 LCG vLCG T D eq)))
              (cong
                (λ x -> head (toCanonic T (atomicValidLemma1 G maxG=0 LCG vLCG T D eq) , x))
                (atomicValidLemma3 G maxG=0 LCG vLCG LCG=0 T D eq))))
          (sym
            (cong
              head
              eq)))
        (sym
          (finalStructuralPreproofCorrect vLCG)))

  findProofValidAtomic :
    (l : HSeqList) ->
    AtomicHSeqList l ->
    validHSeqList l ->
    Prooflist l
  findProofValidAtomic []H atomicL validL =
    []P
  findProofValidAtomic (x ∷H l) (atomicConsH atomicL x₁) (∷HValid .x validL {LCH} vLCH x₂) =
    consP
      (findProofValidAtomic l atomicL validL)
      (atomicValid x x₁ LCH vLCH x₂)

  keepPos :
    {G : HSeq} ->
    (PPG : Preproof G) ->
    (posG : botAG ≤S ⟦ G ⟧) ->
    PosList (getLeaf PPG)
  keepPos {.G} (leaf G) validG =
    pos∷H
      pos[]H
      validG
  keepPos {.(G ∣ ((Γ ∷ botAG) , Δ))} (PreZ-L G Γ Δ PPG) validG =
    keepPos
      PPG
      (Z-L-invert G Γ Δ validG)
  keepPos {.(G ∣ (Γ , (Δ ∷ botAG)))} (PreZ-R G Γ Δ PPG) validG =
    keepPos
      PPG
      (Z-R-invert G Γ Δ validG)
  keepPos {.(G ∣ ((Γ ∷ (-S A)) , Δ))} (Preminus-L G Γ Δ A PPG) validG =
    keepPos
      PPG
      (minus-L-invert G Γ Δ A validG)
  keepPos {.(G ∣ (Γ , (Δ ∷ (-S A))))} (Preminus-R G Γ Δ A PPG) validG =
    keepPos
      PPG
      (minus-R-invert G Γ Δ A validG)
  keepPos {.(G ∣ ((Γ ∷ (A +S B)) , Δ))} (Preplus-L G Γ Δ A B PPG) validG =
    keepPos
      PPG
      (plus-L-invert G Γ Δ A B validG)
  keepPos {.(G ∣ (Γ , (Δ ∷ (A +S B))))} (Preplus-R G Γ Δ A B PPG) validG =
    keepPos
      PPG
      (plus-R-invert G Γ Δ A B validG)
  keepPos {.(G ∣ ((Γ ∷ (A ⊔S B)) , Δ))} (Premax-L G Γ Δ A B PPG PPG₁) validG =
    unionPosIsPos
      (keepPos
        PPG
        (max-L-invert-1 G Γ Δ A B validG) )
      (keepPos
        PPG₁
        (max-L-invert-2 G Γ Δ A B validG))
  keepPos {.(G ∣ (Γ , (Δ ∷ (A ⊔S B))))} (Premax-R G Γ Δ A B PPG) validG =
    keepPos
      PPG
      (max-R-invert G Γ Δ A B validG)
  keepPos {.(G ∣ ((Γ ∷ (A ⊓S B)) , Δ))} (Premin-L G Γ Δ A B PPG) validG =
    keepPos
      PPG
      (min-L-invert G Γ Δ A B validG)
  keepPos {.(G ∣ (Γ , (Δ ∷ (A ⊓S B))))} (Premin-R G Γ Δ A B PPG PPG₁) validG =
    unionPosIsPos
      (keepPos
        PPG
        (min-R-invert-1 G Γ Δ A B validG))
      (keepPos
        PPG₁
        (min-R-invert-2 G Γ Δ A B validG))
  keepPos {.(head ((Γ ∷ botAG) , Δ))} (PreZ-L-head Γ Δ PPG) validG =
    keepPos
      PPG
      (Z-L-head-invert Γ Δ validG)
  keepPos {.(head (Γ , (Δ ∷ botAG)))} (PreZ-R-head Γ Δ PPG) validG =
    keepPos
      PPG
      (Z-R-head-invert Γ Δ validG)
  keepPos {.(head ((Γ ∷ (-S A)) , Δ))} (Preminus-L-head Γ Δ A PPG) validG =
    keepPos
      PPG
      (minus-L-head-invert Γ Δ A validG)
  keepPos {.(head (Γ , (Δ ∷ (-S A))))} (Preminus-R-head Γ Δ A PPG) validG =
    keepPos
      PPG
      (minus-R-head-invert Γ Δ A validG)
  keepPos {.(head ((Γ ∷ (A +S B)) , Δ))} (Preplus-L-head Γ Δ A B PPG) validG =
    keepPos
      PPG
      (plus-L-head-invert Γ Δ A B validG)
  keepPos {.(head (Γ , (Δ ∷ (A +S B))))} (Preplus-R-head Γ Δ A B PPG) validG =
    keepPos
      PPG
      (plus-R-head-invert Γ Δ A B validG)
  keepPos {.(head ((Γ ∷ (A ⊔S B)) , Δ))} (Premax-L-head Γ Δ A B PPG PPG₁) validG =
    unionPosIsPos
      (keepPos
        PPG
        (max-L-head-invert-1 Γ Δ A B validG))
      (keepPos
        PPG₁
        (max-L-head-invert-2 Γ Δ A B validG))
  keepPos {.(head (Γ , (Δ ∷ (A ⊔S B))))} (Premax-R-head Γ Δ A B PPG) validG =
    keepPos
      PPG
      (max-R-head-invert Γ Δ A B validG)
  keepPos {.(head ((Γ ∷ (A ⊓S B)) , Δ))} (Premin-L-head Γ Δ A B PPG) validG =
    keepPos
      PPG
      (min-L-head-invert Γ Δ A B validG)
  keepPos {.(head (Γ , (Δ ∷ (A ⊓S B))))} (Premin-R-head Γ Δ A B PPG PPG₁) validG =
    unionPosIsPos
      (keepPos
        PPG
        (min-R-head-invert-1 Γ Δ A B validG))
      (keepPos
        PPG₁
        (min-R-head-invert-2 Γ Δ A B validG))
  keepPos {.(G ∣ (Γ' , Δ'))} (Preseq-exchange G Γ Γ' Δ Δ' x x₁ PPG) validG =
    keepPos
      PPG
      (seq-exchange-invert G Γ Γ' Δ Δ' x x₁ validG)
  keepPos {.(head (Γ' , Δ'))} (Preseq-exchange-head Γ Γ' Δ Δ' x x₁ PPG) validG =
    keepPos
      PPG
      (seq-exchange-head-invert Γ Γ' Δ Δ' x x₁ validG)
  keepPos {.G'} (Prehseq-exchange G G' x PPG) validG =
    keepPos
      PPG
      (hseq-exchange-invert G G' x validG)

  posAtomic=>Valid :
    {l : HSeqList} ->
    AtomicHSeqList l ->
    PosList l ->
    validHSeqList l
  posAtomic=>Valid atomic[]H pos[]H =
    []HValid
  posAtomic=>Valid {G ∷H l} (atomicConsH atomicL x) (pos∷H posL x₁) with condAtomicValid G x x₁
  posAtomic=>Valid {G ∷H l} (atomicConsH atomicL x) (pos∷H posL x₁) | LCG , (vLCG , LCG=0) =
    ∷HValid
      G
      (posAtomic=>Valid atomicL posL)
      {LCG}
      vLCG
      LCG=0

  completeness :
    (G : HSeq) ->
    botAG ≤S ⟦ G ⟧ ->
    Proof G
  completeness G validG =
    finishProof
      (createPreproof G)
      (findProofValidAtomic
        (getLeaf (createPreproof G))
        (cPpGiveAtomicLeaves G)
        (posAtomic=>Valid
          (cPpGiveAtomicLeaves G)
          (keepPos (createPreproof G) validG)))
