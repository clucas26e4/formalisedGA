module Syntax.HSeq.LinearComb where

  {- STDLIB -}
  open import Nat
  open import Equality
  open import Data.Empty
  open import Data.Product
  open import Data.Maybe
  open import Relation.Nullary
  open import Induction.WellFounded
  open import Function using (_∘_)

  {- SYNTAX -}
  open import Syntax.Term
  open import Syntax.ListTerm
  open import Syntax.ListTerm.Properties
  open import Syntax.Seq
  open import Syntax.Seq.Properties
  open import Syntax.HSeq
  open import Syntax.HSeq.Properties
  open import Syntax.ListSeq
  open import Syntax.HSeqList
  open import Syntax.StructuralPreproof

  {- SEMANTIC -}
  open import Semantic.SemEquality
  open import Semantic.SemEquality.Properties
  open import Semantic.Interpretation

  data LinearCombinaison : HSeq -> Set where
    headLC :
      (H : Seq) ->
      ℕ ->
      LinearCombinaison (head H)
    consLC :
      {G : HSeq} ->
      (LCG : LinearCombinaison G) ->
      (H : Seq) ->
      ℕ ->
      LinearCombinaison (G ∣ H)

  identityLC :
    (G : HSeq) ->
    LinearCombinaison G
--{{{
  identityLC (head H) =
    headLC H 1
  identityLC (G ∣ H) =
    consLC (identityLC G) H 1
--}}}

  data valid-LC : {G : HSeq} -> LinearCombinaison G -> Set where
    valid-headLC :
      (H : Seq) ->
      (k : ℕ) ->
      valid-LC (headLC H (suc k))
    valid-consLC-now :
      {G : HSeq} ->
      (H : Seq) ->
      (k : ℕ) ->
      (LCG : LinearCombinaison G) ->
      valid-LC (consLC LCG H (suc k))
    valid-consLC-before :
      {G : HSeq} ->
      {LCG : LinearCombinaison G} ->
      valid-LC LCG ->
      (H : Seq) ->
      (k : ℕ) ->
      valid-LC (consLC LCG H k)

  identityLCisValid :
    (G : HSeq) ->
    valid-LC (identityLC G)
--{{{
  identityLCisValid (head H) =
    valid-headLC H 0
  identityLCisValid (G ∣ H) =
    valid-consLC-now H 0 (identityLC G)
--}}}

  toSeq :
    {G : HSeq} ->
    (LCG : LinearCombinaison G) ->
    Seq
--{{{
  toSeq {.(head H)} (headLC H zero) =
    [] , []
  toSeq {.(head H)} (headLC H 1) =
    H
  toSeq {.(head H)} (headLC H (suc (suc x))) with toSeq (headLC H (suc x))
  toSeq {.(head (T , D))} (headLC (T , D) (suc (suc x))) | T' , D' =
    union T' T , union D' D
  toSeq {G ∣ .H} (consLC LCG H zero) =
    toSeq LCG
  toSeq {G ∣ .H} (consLC LCG H 1) with toSeq LCG
  toSeq {G ∣ .(T , D)} (consLC LCG (T , D) (suc zero)) | T' , D' =
    union T' T , union D' D
  toSeq {G ∣ .H} (consLC LCG H (suc (suc x))) with toSeq (consLC LCG H (suc x))
  toSeq {G ∣ .(T , D)} (consLC LCG (T , D) (suc (suc x))) | T' , D' =
    union T' T , union D' D
--}}}

  unfoldToSeqIdentity :
    (G : HSeq) ->
    (T T' D D' : ListTerm) ->
    (toSeq (identityLC (G ∣ (T , D) ∣ (T' , D'))) ≡ toSeq (identityLC (G ∣ (union T T' , union D D'))))
--{{{
  unfoldToSeqIdentity G T T' D D' with toSeq (identityLC G)
  unfoldToSeqIdentity G T T' D D' | T₁ , D₁ =
    cong₂
      (λ x y -> x , y)
      (unionAsso T₁ T T')
      (unionAsso D₁ D D')
--}}}

  data validHSeqList : HSeqList -> Set where
    []HValid :
      validHSeqList []H
    ∷HValid :
      (H : HSeq) ->
      {l : HSeqList} ->
      (lIsValid : validHSeqList l) ->
      {LCH : LinearCombinaison H} ->
      (vLCH : valid-LC LCH) ->
      ⟦ toSeq LCH ⟧S ≡ₛ botAG ->
      validHSeqList (H ∷H l)

  HSeqToSeq :
    (G : HSeq) ->
    Seq
--{{{
  HSeqToSeq (head H) =
    H
  HSeqToSeq (G ∣ H) with HSeqToSeq G
  HSeqToSeq (G ∣ (T , D)) | T' , D' =
    union T T' , union D D'
--}}}

  unfoldHSeqToSeqSem :
    (G : HSeq) ->
    (H : Seq) ->
    ⟦ HSeqToSeq (G ∣ H) ⟧S ≡ₛ ⟦ HSeqToSeq G ⟧S +S ⟦ H ⟧S
--{{{
  unfoldHSeqToSeqSem G H with HSeqToSeq G
  unfoldHSeqToSeqSem G (T₁ , D₁) | T , D =
    symₛ
      (beginₛ
        ⟦ T , D ⟧S +S ⟦ T₁ , D₁ ⟧S
          ≡ₛ⟨ reflₛ ⟩
        (⟦ D ⟧L -S ⟦ T ⟧L) +S (⟦ D₁ ⟧L -S ⟦ T₁ ⟧L)
          ≡ₛ⟨ symₛ asso-+S ⟩
        ⟦ D ⟧L +S ((-S ⟦ T ⟧L) +S (⟦ D₁ ⟧L -S ⟦ T₁ ⟧L))
          ≡ₛ⟨ ctxtₛ
                ((CC (⟦ D ⟧L)) +C ●)
                commu-+S ⟩
        ⟦ D ⟧L +S ((⟦ D₁ ⟧L -S ⟦ T₁ ⟧L) -S ⟦ T ⟧L)
          ≡ₛ⟨ ctxtₛ
                ((CC (⟦ D ⟧L)) +C ●)
                (symₛ asso-+S) ⟩
        ⟦ D ⟧L +S (⟦ D₁ ⟧L +S ((-S ⟦ T₁ ⟧L) -S ⟦ T ⟧L))
          ≡ₛ⟨ asso-+S ⟩
        (⟦ D ⟧L +S ⟦ D₁ ⟧L) +S ((-S ⟦ T₁ ⟧L) -S ⟦ T ⟧L)
          ≡ₛ⟨ ctxtₛ
                ((CC (⟦ D ⟧L +S ⟦ D₁ ⟧L)) +C ●)
                (symₛ -S-distri) ⟩
        (⟦ D ⟧L +S ⟦ D₁ ⟧L) -S (⟦ T₁ ⟧L +S ⟦ T ⟧L)
          ≡ₛ⟨ ctxtₛ
                (● -C (CC (⟦ T₁ ⟧L +S ⟦ T ⟧L)))
                commu-+S ⟩
        (⟦ D₁ ⟧L +S ⟦ D ⟧L) -S (⟦ T₁ ⟧L +S ⟦ T ⟧L)
          ≡ₛ⟨ ctxtₛ
                (● -C (CC (⟦ T₁ ⟧L +S ⟦ T ⟧L)))
                (symₛ sem-union-eq-plus) ⟩
        ⟦ union D₁ D ⟧L -S (⟦ T₁ ⟧L +S ⟦ T ⟧L)
          ≡ₛ⟨ ctxtₛ
                ((CC (⟦ union D₁ D ⟧L)) -C ●)
                (symₛ sem-union-eq-plus) ⟩
        ⟦ union D₁ D ⟧L -S (⟦ union T₁ T ⟧L) ∎ₛ)

  semHSeqToSeqUnion :
    (G G' : HSeq) ->
    ⟦ HSeqToSeq (unionHSeq G G') ⟧S ≡ₛ ⟦ HSeqToSeq G ⟧S +S ⟦ HSeqToSeq G' ⟧S
  semHSeqToSeqUnion G (head H) =
    unfoldHSeqToSeqSem G H
  semHSeqToSeqUnion G (G' ∣ H) =
    beginₛ
      ⟦ HSeqToSeq ((unionHSeq G G') ∣ H) ⟧S
        ≡ₛ⟨ unfoldHSeqToSeqSem (unionHSeq G G') H ⟩
      ⟦ HSeqToSeq (unionHSeq G G') ⟧S +S ⟦ H ⟧S
        ≡ₛ⟨ ctxtₛ
              (● +C (CC (⟦ H ⟧S)))
              (semHSeqToSeqUnion G G') ⟩
      (⟦ HSeqToSeq G ⟧S +S ⟦ HSeqToSeq G' ⟧S) +S ⟦ H ⟧S
        ≡ₛ⟨ symₛ asso-+S ⟩
      ⟦ HSeqToSeq G ⟧S +S (⟦ HSeqToSeq G' ⟧S +S ⟦ H ⟧S)
        ≡ₛ⟨ ctxtₛ
              ((CC (⟦ HSeqToSeq G ⟧S)) +C ●)
              (symₛ
                (unfoldHSeqToSeqSem G' H)) ⟩
      ⟦ HSeqToSeq G ⟧S +S ⟦ HSeqToSeq (G' ∣ H) ⟧S ∎ₛ
--}}}

  applyS-RuleFun :
    (G : HSeq) ->
    Acc _<_ (size G) ->
    StructuralPreproof G
--{{{
  applyS-RuleFun (head H) (acc rs) =
    structuralLeaf (head H)
  applyS-RuleFun (head (T , D) ∣ (T₁ , D₁)) (acc rs) =
    SS-head T T₁ D D₁ (structuralLeaf (head (union T T₁ , union D D₁)))
  applyS-RuleFun (G ∣ (T , D) ∣ (T₁ , D₁)) (acc rs) =
    SS G T T₁ D D₁ (applyS-RuleFun (G ∣ (union T T₁ , union D D₁)) (rs (suc (size G)) ≤-refl))
--}}}
    
  applyS-Rule :
    (G : HSeq) ->
    StructuralPreproof G
--{{{
  applyS-Rule G = applyS-RuleFun G (ℕ-acc (size G))
--}}}

  applyS-RuleGiveSeqFun :
    (G : HSeq) ->
    (accSG : Acc _<_ (size G)) ->
    (getStructuralLeaf (applyS-RuleFun G accSG) ≡ head (toSeq (identityLC G)))
--{{{
  applyS-RuleGiveSeqFun (head H) (acc rs) =
    refl
  applyS-RuleGiveSeqFun (head (T , D) ∣ (T₁ , D₁)) (acc rs) =
    refl
  applyS-RuleGiveSeqFun (G ∣ (T , D) ∣ (T₁ , D₁)) (acc rs) =
    trans
      (applyS-RuleGiveSeqFun (G ∣ (union T T₁ , union D D₁)) (rs (suc (size G)) ≤-refl))
      (cong head (sym (unfoldToSeqIdentity G T T₁ D D₁)))
--}}}

  applyS-RuleGiveSeq :
    (G : HSeq) ->
    (getStructuralLeaf (applyS-Rule G) ≡ head (toSeq (identityLC G)))
--{{{
  applyS-RuleGiveSeq G =
    applyS-RuleGiveSeqFun G (ℕ-acc (size G))
--}}}

  createStructuralPreproofFun :
    {G : HSeq} ->
    (LCG : LinearCombinaison G) ->
    Maybe (StructuralPreproof G)
--{{{
  createStructuralPreproofFun {.(head H)} (headLC H zero) =
    nothing
  createStructuralPreproofFun {.(head H)} (headLC H (suc x)) with createStructuralPreproofFun (headLC H x)
  createStructuralPreproofFun {.(head (_ , _))} (headLC (T , D) (suc x)) | just sppG =
    just (SC-head
           T
           D
           (addFirst (head (T , D)) sppG))
  createStructuralPreproofFun {.(head (_ , _))} (headLC (T , D) (suc x)) | nothing =
    just (structuralLeaf (head (T , D)))
  createStructuralPreproofFun {head (T₁ , D₁) ∣ (T , D)} (consLC LCG .(T , D) zero) with createStructuralPreproofFun LCG
  createStructuralPreproofFun {head (T₁ , D₁) ∣ (T , D)} (consLC LCG .(T , D) zero) | just sppG =
    just (SW-head
             T₁
             T
             D₁
             D
             sppG)
  createStructuralPreproofFun {head (T₁ , D₁) ∣ (T , D)} (consLC LCG .(T , D) zero) | nothing =
    nothing
  createStructuralPreproofFun {G ∣ (T₁ , D₁) ∣ (T , D)} (consLC LCG .(T , D) zero) with createStructuralPreproofFun LCG
  createStructuralPreproofFun {G ∣ (T₁ , D₁) ∣ (T , D)} (consLC LCG .(T , D) zero) | just sppG =
    just (SW
             G
             T₁
             T
             D₁
             D
             sppG)
  createStructuralPreproofFun {G ∣ (T₁ , D₁) ∣ (T , D)} (consLC LCG .(T , D) zero) | nothing =
    nothing
  createStructuralPreproofFun {G ∣ (T , D)} (consLC LCG .(T , D) (suc x)) with createStructuralPreproofFun (consLC LCG (T , D) x)
  createStructuralPreproofFun {G ∣ (T , D)} (consLC LCG .(T , D) (suc x)) | just sppG =
    just
      (SC
        G
        T
        D
        (Shseq-exchange
          (unionHSeq (head (T , D)) (G ∣ (T , D)))
          (G ∣ (T , D) ∣ (T , D))
          (unionHSeqSymEx (head (T , D)) (G ∣ (T , D)))
          (addFirst
            (head (T , D))
            sppG)))
  createStructuralPreproofFun {G ∣ (T , D)} (consLC LCG .(T , D) (suc x)) | nothing =
    just
      (keepLast
        G
        (T , D))
--}}}

  createStructuralPreproofVLCGNoNothing :
    {G : HSeq} ->
    {LCG : LinearCombinaison G} ->
    (vLCG : valid-LC LCG) ->
    ¬ (createStructuralPreproofFun LCG ≡ nothing)
--{{{
  createStructuralPreproofVLCGNoNothing {.(head H)} {headLC H zero} ()
  createStructuralPreproofVLCGNoNothing {.(head H)} {headLC H (suc x)} vLCG with createStructuralPreproofFun (headLC H x)
  createStructuralPreproofVLCGNoNothing {.(head (T , D))} {headLC (T , D) (suc x)} vLCG | just x₁ =
    λ {()}
  createStructuralPreproofVLCGNoNothing {.(head (T , D))} {headLC (T , D) (suc x)} vLCG | nothing =
    λ {()}
  createStructuralPreproofVLCGNoNothing {head (T₁ , D₁) ∣ .(T , D)} {consLC LCG (T , D) zero} (valid-consLC-before vLCG .(T , D) .0) with createStructuralPreproofFun LCG | inspect createStructuralPreproofFun LCG | createStructuralPreproofVLCGNoNothing vLCG
  createStructuralPreproofVLCGNoNothing {head (T₁ , D₁) ∣ .(T , D)} {consLC LCG (T , D) zero} (valid-consLC-before vLCG .(T , D) _) | just x | [ eq ] | ind =
    λ {()}
  createStructuralPreproofVLCGNoNothing {head (T₁ , D₁) ∣ .(T , D)} {consLC LCG (T , D) zero} (valid-consLC-before vLCG .(T , D) _) | nothing | [ eq ] | ind =
    λ x -> (ind refl)
  createStructuralPreproofVLCGNoNothing {G ∣ (T₁ , D₁) ∣ .(T , D)} {consLC LCG (T , D) zero} (valid-consLC-before vLCG .(T , D) .0) with createStructuralPreproofFun LCG | inspect createStructuralPreproofFun LCG | createStructuralPreproofVLCGNoNothing vLCG
  createStructuralPreproofVLCGNoNothing {G ∣ (T₁ , D₁) ∣ .(T , D)} {consLC LCG (T , D) zero} (valid-consLC-before vLCG .(T , D) _) | just x | [ eq ] | ind =
    λ {()}
  createStructuralPreproofVLCGNoNothing {G ∣ (T₁ , D₁) ∣ .(T , D)} {consLC LCG (T , D) zero} (valid-consLC-before vLCG .(T , D) _) | nothing | [ eq ] | ind =
    λ x -> (ind refl)
  createStructuralPreproofVLCGNoNothing {head (T₁ , D₁) ∣ .(T , D)} {consLC LCG (T , D) (suc x)} (valid-consLC-now .(T , D) .x .LCG) with createStructuralPreproofFun (consLC LCG (T , D) x)
  createStructuralPreproofVLCGNoNothing {head (T₁ , D₁) ∣ .(T , D)} {consLC LCG (T , D) (suc x)} (valid-consLC-now .(T , D) .x .LCG) | just x₁ =
    λ {()}
  createStructuralPreproofVLCGNoNothing {head (T₁ , D₁) ∣ .(T , D)} {consLC LCG (T , D) (suc x)} (valid-consLC-now .(T , D) .x .LCG) | nothing =
    λ {()}
  createStructuralPreproofVLCGNoNothing {head (T₁ , D₁) ∣ .(T , D)} {consLC LCG (T , D) (suc x)} (valid-consLC-before vLCG .(T , D) .(suc x)) with createStructuralPreproofFun (consLC LCG (T , D) x) | inspect createStructuralPreproofFun (consLC LCG (T , D) x)
  createStructuralPreproofVLCGNoNothing {head (T₁ , D₁) ∣ .(T , D)} {consLC LCG (T , D) (suc x)} (valid-consLC-before vLCG .(T , D) .(suc x)) | just x₁ | [ eq ] =
    λ {()}
  createStructuralPreproofVLCGNoNothing {head (T₁ , D₁) ∣ .(T , D)} {consLC LCG (T , D) (suc x)} (valid-consLC-before vLCG .(T , D) .(suc x)) | nothing | [ eq ] =
    λ {()}
  createStructuralPreproofVLCGNoNothing {G ∣ (T₁ , D₁) ∣ .(T , D)} {consLC LCG (T , D) (suc x)} vLCG with createStructuralPreproofFun (consLC LCG (T , D) x)
  createStructuralPreproofVLCGNoNothing {G ∣ (T₁ , D₁) ∣ .(T , D)} {consLC LCG (T , D) (suc x)} vLCG | just x₁ =
    λ {()}
  createStructuralPreproofVLCGNoNothing {G ∣ (T₁ , D₁) ∣ .(T , D)} {consLC LCG (T , D) (suc x)} vLCG | nothing =
    λ {()}
--}}}

  toSeqNothing :
    {G : HSeq} ->
    (LCG : LinearCombinaison G) ->
    createStructuralPreproofFun LCG ≡ nothing ->
    toSeq LCG ≡ ([] , [])
--{{{
  toSeqNothing {.(head H)} (headLC H zero) CPP=nothing =
    refl
  toSeqNothing {.(head H)} (headLC H (suc x)) CPP=nothing =
    ⊥-elim
      (createStructuralPreproofVLCGNoNothing
        {head H}
        {headLC H (suc x)}
        (valid-headLC H x)
        CPP=nothing)
  toSeqNothing {head (T₁ , D₁) ∣ .(T , D)} (consLC LCG (T , D) zero) CPP=nothing with createStructuralPreproofFun LCG | inspect createStructuralPreproofFun LCG
  toSeqNothing {head (T₁ , D₁) ∣ .(T , D)} (consLC LCG (T , D) zero) () | just x | [ eq ]
  toSeqNothing {head (T₁ , D₁) ∣ .(T , D)} (consLC LCG (T , D) zero) CPP=nothing | nothing | [ eq ] =
    toSeqNothing LCG eq
  toSeqNothing {G ∣ (T₁ , D₁) ∣ .(T , D)} (consLC LCG (T , D) zero) CPP=nothing with createStructuralPreproofFun LCG | inspect createStructuralPreproofFun LCG
  toSeqNothing {G ∣ (T₁ , D₁) ∣ .(T , D)} (consLC LCG (T , D) zero) () | just x | [ eq ]
  toSeqNothing {G ∣ (T₁ , D₁) ∣ .(T , D)} (consLC LCG (T , D) zero) CPP=nothing | nothing | [ eq ] =
    toSeqNothing LCG eq
  toSeqNothing {head (T₁ , D₁) ∣ .(T , D)} (consLC LCG (T , D) (suc x)) CPP=nothing with createStructuralPreproofFun (consLC LCG (T , D) x) | inspect createStructuralPreproofFun (consLC LCG (T , D) x)
  toSeqNothing {head (T₁ , D₁) ∣ .(T , D)} (consLC LCG (T , D) (suc x)) () | just x₁ | [ eq ]
  toSeqNothing {head (T₁ , D₁) ∣ .(T , D)} (consLC LCG (T , D) (suc zero)) () | nothing | [ eq ]
  toSeqNothing {head (T₁ , D₁) ∣ .(T , D)} (consLC LCG (T , D) (suc (suc x))) () | nothing | [ eq ]
  toSeqNothing {G ∣ (T₁ , D₁) ∣ .(T , D)} (consLC LCG (T , D) (suc x)) CPP=nothing with createStructuralPreproofFun (consLC LCG (T , D) x) | inspect createStructuralPreproofFun (consLC LCG (T , D) x)
  toSeqNothing {G ∣ (T₁ , D₁) ∣ .(T , D)} (consLC LCG (T , D) (suc x)) () | just x₁ | [ eq ]
  toSeqNothing {G ∣ (T₁ , D₁) ∣ .(T , D)} (consLC LCG (T , D) (suc x)) () | nothing | [ eq ]
--}}}

  createStructuralPreproof :
    {G : HSeq} ->
    {LCG : LinearCombinaison G} ->
    (vLCG : valid-LC LCG) ->
    StructuralPreproof G
--{{{
  createStructuralPreproof {G} {LCG} vLCG with createStructuralPreproofFun LCG | inspect createStructuralPreproofFun LCG
  createStructuralPreproof {G} {LCG} vLCG | just x | [ eq ] =
    x
  createStructuralPreproof {G} {LCG} vLCG | nothing  | [ eq ] =
    ⊥-elim
      (createStructuralPreproofVLCGNoNothing vLCG eq)
--}}}

  createStructuralPreproofFunCorrect :
    {G : HSeq} ->
    (LCG : LinearCombinaison G) ->
    (SPP : StructuralPreproof G) ->
    (createStructuralPreproofFun LCG ≡ just SPP) ->
    ⟦ HSeqToSeq (getStructuralLeaf SPP) ⟧S ≡ₛ ⟦ toSeq LCG ⟧S
--{{{
  createStructuralPreproofFunCorrect {.(head H)} (headLC H zero) SPP ()
  createStructuralPreproofFunCorrect {.(head (T , D))} (headLC (T , D) (suc zero)) SPP CPP=SPP =
    congₛ
      (cong
        (λ x -> ⟦ x ⟧S)
        (begin
          HSeqToSeq (getStructuralLeaf SPP)
            ≡⟨ cong
                 (HSeqToSeq ∘ getStructuralLeaf)
                 (sym (just-injective CPP=SPP)) ⟩
          HSeqToSeq (getStructuralLeaf (structuralLeaf (head (T , D))))
            ≡⟨ refl ⟩
          (T , D) ∎))
  createStructuralPreproofFunCorrect {.(head (T , D))} (headLC (T , D) (suc (suc x))) SPP CPP=SPP with createStructuralPreproofFun (headLC (T , D) (suc x)) | inspect createStructuralPreproofFun (headLC (T , D) (suc x))
  createStructuralPreproofFunCorrect {.(head (T , D))} (headLC (T , D) (suc (suc x))) SPP CPP=SPP | just indSPP | [ eq ] with toSeq (headLC (T , D) (suc x)) | inspect toSeq (headLC (T , D) (suc x))
  createStructuralPreproofFunCorrect {.(head (T , D))} (headLC (T , D) (suc (suc x))) SPP CPP=SPP | just indSPP | [ eq ] | T₁ , D₁ | [ eq₁ ] =
    beginₛ
      ⟦ HSeqToSeq (getStructuralLeaf SPP) ⟧S
        ≡ₛ⟨ congₛ
              (cong
                (⟦_⟧S ∘ HSeqToSeq ∘ getStructuralLeaf)
                (sym (just-injective CPP=SPP))) ⟩
      ⟦ HSeqToSeq (getStructuralLeaf (SC-head T D (addFirst (head (T , D)) indSPP))) ⟧S
        ≡ₛ⟨ congₛ
              (cong
                (⟦_⟧S ∘ HSeqToSeq)
                (refl {x = getStructuralLeaf (SC-head T D (addFirst (head (T , D)) indSPP))})) ⟩
      ⟦ HSeqToSeq (getStructuralLeaf (addFirst (head (T , D)) indSPP)) ⟧S
        ≡ₛ⟨ congₛ
              (cong
                (⟦_⟧S ∘ HSeqToSeq)
                (addFirstLeaf indSPP (head (T , D)))) ⟩
      ⟦ HSeqToSeq (unionHSeq (head (T , D)) (getStructuralLeaf indSPP)) ⟧S
        ≡ₛ⟨ semHSeqToSeqUnion (head (T , D)) (getStructuralLeaf indSPP) ⟩
      ⟦ HSeqToSeq (head (T , D)) ⟧S +S ⟦ HSeqToSeq (getStructuralLeaf indSPP) ⟧S
        ≡ₛ⟨ reflₛ ⟩
      ⟦ T , D ⟧S +S ⟦ HSeqToSeq (getStructuralLeaf indSPP) ⟧S
        ≡ₛ⟨ ctxtₛ
              ((CC (⟦ T , D ⟧S)) +C ●)
              (createStructuralPreproofFunCorrect
                (headLC (T , D) (suc x))
                indSPP
                eq) ⟩
      ⟦ T , D ⟧S +S ⟦ toSeq (headLC (T , D) (suc x)) ⟧S
        ≡ₛ⟨ ctxtₛ
              ((CC (⟦ T , D ⟧S)) +C ●)
              (congₛ
                (cong
                  ⟦_⟧S
                  eq₁)) ⟩
      ⟦ T , D ⟧S +S ⟦ T₁ , D₁ ⟧S
        ≡ₛ⟨ reflₛ ⟩
      (⟦ D ⟧L -S ⟦ T ⟧L) +S (⟦ D₁ ⟧L -S ⟦ T₁ ⟧L)
        ≡ₛ⟨ symₛ asso-+S ⟩
      ⟦ D ⟧L +S ((-S ⟦ T ⟧L) +S (⟦ D₁ ⟧L -S ⟦ T₁ ⟧L))
        ≡ₛ⟨ ctxtₛ
              ((CC (⟦ D ⟧L)) +C ●)
              commu-+S ⟩
      ⟦ D ⟧L +S ((⟦ D₁ ⟧L -S ⟦ T₁ ⟧L) -S ⟦ T ⟧L)
        ≡ₛ⟨ ctxtₛ
              ((CC (⟦ D ⟧L)) +C ●)
              (symₛ asso-+S) ⟩
      ⟦ D ⟧L +S (⟦ D₁ ⟧L +S ((-S ⟦ T₁ ⟧L) -S ⟦ T ⟧L))
        ≡ₛ⟨ asso-+S ⟩
      (⟦ D ⟧L +S ⟦ D₁ ⟧L) +S ((-S ⟦ T₁ ⟧L) -S ⟦ T ⟧L)
        ≡ₛ⟨ ctxtₛ
             ((CC (⟦ D ⟧L +S ⟦ D₁ ⟧L)) +C ●)
             (symₛ -S-distri) ⟩
      (⟦ D ⟧L +S ⟦ D₁ ⟧L) -S (⟦ T₁ ⟧L +S ⟦ T ⟧L)
        ≡ₛ⟨ ctxtₛ
              (● -C (CC (⟦ T₁ ⟧L +S ⟦ T ⟧L)))
              commu-+S ⟩
      (⟦ D₁ ⟧L +S ⟦ D ⟧L) -S (⟦ T₁ ⟧L +S ⟦ T ⟧L)
        ≡ₛ⟨ ctxtₛ
              (● -C (CC (⟦ T₁ ⟧L +S ⟦ T ⟧L)))
              (symₛ sem-union-eq-plus) ⟩
      ⟦ union D₁ D ⟧L -S (⟦ T₁ ⟧L +S ⟦ T ⟧L)
        ≡ₛ⟨ ctxtₛ
              ((CC (⟦ union D₁ D ⟧L)) -C ●)
              (symₛ sem-union-eq-plus) ⟩
      ⟦ union D₁ D ⟧L -S (⟦ union T₁ T ⟧L)
        ≡ₛ⟨ reflₛ ⟩
      ⟦ (union T₁ T) , (union D₁ D) ⟧S ∎ₛ
  createStructuralPreproofFunCorrect {.(head (T , D))} (headLC (T , D) (suc (suc x))) SPP CPP=SPP | nothing | [ eq ] =
    ⊥-elim
      (createStructuralPreproofVLCGNoNothing
        {head (T , D)}
        {headLC (T , D) (suc x)}
        (valid-headLC (T , D) x)
        eq)
  createStructuralPreproofFunCorrect {head (T , D) ∣ .(T₁ , D₁)} (consLC LCG (T₁ , D₁) zero) SPP CPP=SPP with createStructuralPreproofFun LCG | inspect createStructuralPreproofFun LCG
  createStructuralPreproofFunCorrect {head (T , D) ∣ .(T₁ , D₁)} (consLC LCG (T₁ , D₁) zero) SPP CPP=SPP | just indSPP | [ eq ] =
    beginₛ
      ⟦ HSeqToSeq (getStructuralLeaf SPP) ⟧S
        ≡ₛ⟨ congₛ
              (cong
                (⟦_⟧S ∘ HSeqToSeq ∘ getStructuralLeaf)
                (just-injective (sym CPP=SPP))) ⟩
      ⟦ HSeqToSeq (getStructuralLeaf (SW-head T T₁ D D₁ indSPP)) ⟧S
        ≡ₛ⟨ reflₛ ⟩
      ⟦ HSeqToSeq (getStructuralLeaf indSPP) ⟧S
        ≡ₛ⟨ createStructuralPreproofFunCorrect LCG indSPP eq ⟩
      ⟦ toSeq LCG ⟧S ∎ₛ
  createStructuralPreproofFunCorrect {head (T , D) ∣ .(T₁ , D₁)} (consLC LCG (T₁ , D₁) zero) SPP () | nothing | [ eq ]
  createStructuralPreproofFunCorrect {head (T , D) ∣ .(T₁ , D₁)} (consLC LCG (T₁ , D₁) (suc x)) SPP CPP=SPP with createStructuralPreproofFun (consLC LCG (T₁ , D₁) x) | inspect createStructuralPreproofFun (consLC LCG (T₁ , D₁) x)
  createStructuralPreproofFunCorrect {head (T , D) ∣ .(T₁ , D₁)} (consLC LCG (T₁ , D₁) (suc zero)) SPP CPP=SPP | just indSPP | [ eq ] with toSeq LCG | inspect toSeq LCG
  createStructuralPreproofFunCorrect {head (T , D) ∣ .(T₁ , D₁)} (consLC LCG (T₁ , D₁) (suc zero)) SPP CPP=SPP | just indSPP | [ eq ] | T₂ , D₂ | [ eq₁ ] =
    beginₛ
      ⟦ HSeqToSeq (getStructuralLeaf SPP) ⟧S
        ≡ₛ⟨ congₛ
              (cong
                (⟦_⟧S ∘ HSeqToSeq ∘ getStructuralLeaf)
                (just-injective (sym CPP=SPP))) ⟩
      ⟦ HSeqToSeq (getStructuralLeaf (addFirst (head (T₁ , D₁)) indSPP)) ⟧S
        ≡ₛ⟨ congₛ
              (cong
                (⟦_⟧S ∘ HSeqToSeq)
                (addFirstLeaf indSPP (head (T₁ , D₁)))) ⟩
      ⟦ HSeqToSeq (unionHSeq (head (T₁ , D₁)) (getStructuralLeaf indSPP)) ⟧S
        ≡ₛ⟨ semHSeqToSeqUnion (head (T₁ , D₁)) (getStructuralLeaf indSPP) ⟩
      ⟦ HSeqToSeq (head (T₁ , D₁)) ⟧S +S ⟦ HSeqToSeq (getStructuralLeaf indSPP) ⟧S
        ≡ₛ⟨ reflₛ ⟩
      ⟦ T₁ , D₁ ⟧S +S ⟦ HSeqToSeq (getStructuralLeaf indSPP) ⟧S
        ≡ₛ⟨ ctxtₛ
              ((CC (⟦ T₁ , D₁ ⟧S)) +C ●)
              (createStructuralPreproofFunCorrect
                (consLC LCG (T₁ , D₁) 0)
                indSPP
                eq) ⟩
      ⟦ T₁ , D₁ ⟧S +S ⟦ toSeq (consLC LCG (T₁ , D₁) 0) ⟧S
        ≡ₛ⟨ reflₛ ⟩
      ⟦ T₁ , D₁ ⟧S +S ⟦ toSeq LCG ⟧S
        ≡ₛ⟨ congₛ
              (cong
                (λ x -> ⟦ T₁ , D₁ ⟧S +S ⟦ x ⟧S)
                eq₁) ⟩
      ⟦ T₁ , D₁ ⟧S +S ⟦ T₂ , D₂ ⟧S
        ≡ₛ⟨ reflₛ ⟩
      (⟦ D₁ ⟧L -S ⟦ T₁ ⟧L) +S (⟦ D₂ ⟧L -S ⟦ T₂ ⟧L)
        ≡ₛ⟨ symₛ asso-+S ⟩
      ⟦ D₁ ⟧L +S ((-S ⟦ T₁ ⟧L) +S (⟦ D₂ ⟧L -S ⟦ T₂ ⟧L))
        ≡ₛ⟨ ctxtₛ
              ((CC (⟦ D₁ ⟧L)) +C ●)
              commu-+S ⟩
      ⟦ D₁ ⟧L +S ((⟦ D₂ ⟧L -S ⟦ T₂ ⟧L) -S ⟦ T₁ ⟧L)
        ≡ₛ⟨ ctxtₛ
              ((CC (⟦ D₁ ⟧L)) +C ●)
              (symₛ asso-+S) ⟩
      ⟦ D₁ ⟧L +S (⟦ D₂ ⟧L +S ((-S ⟦ T₂ ⟧L) -S ⟦ T₁ ⟧L))
        ≡ₛ⟨ asso-+S ⟩
      (⟦ D₁ ⟧L +S ⟦ D₂ ⟧L) +S ((-S ⟦ T₂ ⟧L) -S ⟦ T₁ ⟧L)
        ≡ₛ⟨ ctxtₛ
             ((CC (⟦ D₁ ⟧L +S ⟦ D₂ ⟧L)) +C ●)
             (symₛ -S-distri) ⟩
      (⟦ D₁ ⟧L +S ⟦ D₂ ⟧L) -S (⟦ T₂ ⟧L +S ⟦ T₁ ⟧L)
        ≡ₛ⟨ ctxtₛ
              (● -C (CC (⟦ T₂ ⟧L +S ⟦ T₁ ⟧L)))
              commu-+S ⟩
      (⟦ D₂ ⟧L +S ⟦ D₁ ⟧L) -S (⟦ T₂ ⟧L +S ⟦ T₁ ⟧L)
        ≡ₛ⟨ ctxtₛ
              (● -C (CC (⟦ T₂ ⟧L +S ⟦ T₁ ⟧L)))
              (symₛ sem-union-eq-plus) ⟩
      ⟦ union D₂ D₁ ⟧L -S (⟦ T₂ ⟧L +S ⟦ T₁ ⟧L)
        ≡ₛ⟨ ctxtₛ
              ((CC (⟦ union D₂ D₁ ⟧L)) -C ●)
              (symₛ sem-union-eq-plus) ⟩
      ⟦ union D₂ D₁ ⟧L -S (⟦ union T₂ T₁ ⟧L)
        ≡ₛ⟨ reflₛ ⟩
      ⟦ (union T₂ T₁) , (union D₂ D₁) ⟧S ∎ₛ
  createStructuralPreproofFunCorrect {head (T , D) ∣ .(T₁ , D₁)} (consLC LCG (T₁ , D₁) (suc (suc x))) SPP CPP=SPP | just indSPP | [ eq ] with toSeq (consLC LCG (T₁ , D₁) (suc x)) | inspect toSeq (consLC LCG (T₁ , D₁) (suc x))
  createStructuralPreproofFunCorrect {head (T , D) ∣ .(T₁ , D₁)} (consLC LCG (T₁ , D₁) (suc (suc x))) SPP CPP=SPP | just indSPP | [ eq ] | T₂ , D₂ | [ eq₁ ] = 
    beginₛ
      ⟦ HSeqToSeq (getStructuralLeaf SPP) ⟧S
        ≡ₛ⟨ congₛ
              (cong
                (⟦_⟧S ∘ HSeqToSeq ∘ getStructuralLeaf)
                (just-injective (sym CPP=SPP))) ⟩
      ⟦ HSeqToSeq (getStructuralLeaf (addFirst (head (T₁ , D₁)) indSPP)) ⟧S
        ≡ₛ⟨ congₛ
              (cong
                (⟦_⟧S ∘ HSeqToSeq)
                (addFirstLeaf indSPP (head (T₁ , D₁)))) ⟩
      ⟦ HSeqToSeq (unionHSeq (head (T₁ , D₁)) (getStructuralLeaf indSPP)) ⟧S
        ≡ₛ⟨ semHSeqToSeqUnion (head (T₁ , D₁)) (getStructuralLeaf indSPP) ⟩
      ⟦ HSeqToSeq (head (T₁ , D₁)) ⟧S +S ⟦ HSeqToSeq (getStructuralLeaf indSPP) ⟧S
        ≡ₛ⟨ reflₛ ⟩
      ⟦ T₁ , D₁ ⟧S +S ⟦ HSeqToSeq (getStructuralLeaf indSPP) ⟧S
        ≡ₛ⟨ ctxtₛ
              ((CC (⟦ T₁ , D₁ ⟧S)) +C ●)
              (createStructuralPreproofFunCorrect
                (consLC LCG (T₁ , D₁) (suc x))
                indSPP
                eq) ⟩
      ⟦ T₁ , D₁ ⟧S +S ⟦ toSeq (consLC LCG (T₁ , D₁) (suc x)) ⟧S
        ≡ₛ⟨ congₛ
              (cong
                (λ x -> ⟦ T₁ , D₁ ⟧S +S ⟦ x ⟧S)
                eq₁) ⟩
      ⟦ T₁ , D₁ ⟧S +S ⟦ T₂ , D₂ ⟧S
        ≡ₛ⟨ reflₛ ⟩
      (⟦ D₁ ⟧L -S ⟦ T₁ ⟧L) +S (⟦ D₂ ⟧L -S ⟦ T₂ ⟧L)
        ≡ₛ⟨ symₛ asso-+S ⟩
      ⟦ D₁ ⟧L +S ((-S ⟦ T₁ ⟧L) +S (⟦ D₂ ⟧L -S ⟦ T₂ ⟧L))
        ≡ₛ⟨ ctxtₛ
              ((CC (⟦ D₁ ⟧L)) +C ●)
              commu-+S ⟩
      ⟦ D₁ ⟧L +S ((⟦ D₂ ⟧L -S ⟦ T₂ ⟧L) -S ⟦ T₁ ⟧L)
        ≡ₛ⟨ ctxtₛ
              ((CC (⟦ D₁ ⟧L)) +C ●)
              (symₛ asso-+S) ⟩
      ⟦ D₁ ⟧L +S (⟦ D₂ ⟧L +S ((-S ⟦ T₂ ⟧L) -S ⟦ T₁ ⟧L))
        ≡ₛ⟨ asso-+S ⟩
      (⟦ D₁ ⟧L +S ⟦ D₂ ⟧L) +S ((-S ⟦ T₂ ⟧L) -S ⟦ T₁ ⟧L)
        ≡ₛ⟨ ctxtₛ
             ((CC (⟦ D₁ ⟧L +S ⟦ D₂ ⟧L)) +C ●)
             (symₛ -S-distri) ⟩
      (⟦ D₁ ⟧L +S ⟦ D₂ ⟧L) -S (⟦ T₂ ⟧L +S ⟦ T₁ ⟧L)
        ≡ₛ⟨ ctxtₛ
              (● -C (CC (⟦ T₂ ⟧L +S ⟦ T₁ ⟧L)))
              commu-+S ⟩
      (⟦ D₂ ⟧L +S ⟦ D₁ ⟧L) -S (⟦ T₂ ⟧L +S ⟦ T₁ ⟧L)
        ≡ₛ⟨ ctxtₛ
              (● -C (CC (⟦ T₂ ⟧L +S ⟦ T₁ ⟧L)))
              (symₛ sem-union-eq-plus) ⟩
      ⟦ union D₂ D₁ ⟧L -S (⟦ T₂ ⟧L +S ⟦ T₁ ⟧L)
        ≡ₛ⟨ ctxtₛ
              ((CC (⟦ union D₂ D₁ ⟧L)) -C ●)
              (symₛ sem-union-eq-plus) ⟩
      ⟦ union D₂ D₁ ⟧L -S (⟦ union T₂ T₁ ⟧L)
        ≡ₛ⟨ reflₛ ⟩
      ⟦ (union T₂ T₁) , (union D₂ D₁) ⟧S ∎ₛ
  createStructuralPreproofFunCorrect {head (T , D) ∣ .(T₁ , D₁)} (consLC LCG (T₁ , D₁) (suc zero)) SPP CPP=SPP | nothing | [ eq ] with toSeq LCG | inspect toSeq LCG
  createStructuralPreproofFunCorrect {head (T , D) ∣ .(T₁ , D₁)} (consLC (headLC .(T , D) zero) (T₁ , D₁) (suc zero)) SPP CPP=SPP | nothing | [ eq ] | .[] , .[] | [ refl ] = 
    beginₛ
      ⟦ HSeqToSeq (getStructuralLeaf SPP) ⟧S
        ≡ₛ⟨ congₛ
              (cong
                (⟦_⟧S ∘ HSeqToSeq ∘ getStructuralLeaf)
                (just-injective (sym CPP=SPP))) ⟩
      ⟦ T₁ , D₁ ⟧S
        ≡ₛ⟨ congₛ
              (sym
                (cong₂
                  (λ x y -> ⟦ x , y ⟧S)
                  (union[]T=T T₁)
                  (union[]T=T D₁))) ⟩
      ⟦ (union [] T₁) , (union [] D₁) ⟧S ∎ₛ
  createStructuralPreproofFunCorrect {head (T , D) ∣ .(T₁ , D₁)} (consLC (headLC .(T , D) (suc x)) (T₁ , D₁) (suc zero)) SPP CPP=SPP | nothing | [ eq ] | T₂ , D₂ | [ eq₁ ] =
    ⊥-elim
      (createStructuralPreproofVLCGNoNothing
        {head (T , D) ∣ (T₁ , D₁)}
        {consLC (headLC (T , D) (suc x)) (T₁ , D₁) zero}
        (valid-consLC-before (valid-headLC (T , D) x) (T₁ , D₁) 0)
        eq) 
  createStructuralPreproofFunCorrect {head (T , D) ∣ .(T₁ , D₁)} (consLC LCG (T₁ , D₁) (suc (suc x))) SPP CPP=SPP | nothing | [ eq ] =
    ⊥-elim
      (createStructuralPreproofVLCGNoNothing
        {LCG = (consLC LCG (T₁ , D₁) (suc x))}
        (valid-consLC-now (T₁ , D₁) x LCG)
        eq)
  createStructuralPreproofFunCorrect {G ∣ (T , D) ∣ .(T₁ , D₁)} (consLC LCG (T₁ , D₁) zero) SPP CPP=SPP with createStructuralPreproofFun LCG | inspect createStructuralPreproofFun LCG
  createStructuralPreproofFunCorrect {G ∣ (T , D) ∣ .(T₁ , D₁)} (consLC LCG (T₁ , D₁) zero) SPP CPP=SPP | just indSPP | [ eq ] =
    beginₛ
      ⟦ HSeqToSeq (getStructuralLeaf SPP) ⟧S
        ≡ₛ⟨ congₛ
              (cong
                (⟦_⟧S ∘ HSeqToSeq ∘ getStructuralLeaf)
                (just-injective (sym CPP=SPP))) ⟩
      ⟦ HSeqToSeq (getStructuralLeaf indSPP) ⟧S
        ≡ₛ⟨ createStructuralPreproofFunCorrect
              LCG
              indSPP
              eq ⟩
      ⟦ toSeq LCG ⟧S ∎ₛ
  createStructuralPreproofFunCorrect {G ∣ (T , D) ∣ .(T₁ , D₁)} (consLC LCG (T₁ , D₁) zero) SPP () | nothing | [ eq ]
  createStructuralPreproofFunCorrect {G ∣ (T , D) ∣ .(T₁ , D₁)} (consLC LCG (T₁ , D₁) (suc zero)) SPP CPP=SPP with createStructuralPreproofFun (consLC LCG (T₁ , D₁) 0) | inspect createStructuralPreproofFun (consLC LCG (T₁ , D₁) 0)
  createStructuralPreproofFunCorrect {G ∣ (T , D) ∣ .(T₁ , D₁)} (consLC LCG (T₁ , D₁) (suc zero)) SPP CPP=SPP | just indSPP | [ eq ] with toSeq LCG | inspect toSeq LCG
  createStructuralPreproofFunCorrect {G ∣ (T , D) ∣ .(T₁ , D₁)} (consLC LCG (T₁ , D₁) (suc zero)) SPP CPP=SPP | just indSPP | [ eq ] | T₂ , D₂ | [ eq₁ ] = 
    beginₛ
      ⟦ HSeqToSeq (getStructuralLeaf SPP) ⟧S
        ≡ₛ⟨ congₛ
              (cong
                (⟦_⟧S ∘ HSeqToSeq ∘ getStructuralLeaf)
                (just-injective (sym CPP=SPP))) ⟩
      ⟦ HSeqToSeq (getStructuralLeaf (addFirst (head (T₁ , D₁)) indSPP)) ⟧S
        ≡ₛ⟨ congₛ
              (cong
                (⟦_⟧S ∘ HSeqToSeq)
                (addFirstLeaf indSPP (head (T₁ , D₁)))) ⟩
      ⟦ HSeqToSeq (unionHSeq (head (T₁ , D₁)) (getStructuralLeaf indSPP)) ⟧S
        ≡ₛ⟨ semHSeqToSeqUnion (head (T₁ , D₁)) (getStructuralLeaf indSPP) ⟩
      ⟦ HSeqToSeq (head (T₁ , D₁)) ⟧S +S ⟦ HSeqToSeq (getStructuralLeaf indSPP) ⟧S
        ≡ₛ⟨ reflₛ ⟩
      ⟦ T₁ , D₁ ⟧S +S ⟦ HSeqToSeq (getStructuralLeaf indSPP) ⟧S
        ≡ₛ⟨ ctxtₛ
              ((CC (⟦ T₁ , D₁ ⟧S)) +C ●)
              (createStructuralPreproofFunCorrect
                (consLC LCG (T₁ , D₁) 0)
                indSPP
                eq) ⟩
      ⟦ T₁ , D₁ ⟧S +S ⟦ toSeq (consLC LCG (T₁ , D₁) 0) ⟧S
        ≡ₛ⟨ congₛ
              (cong
                (λ x -> ⟦ T₁ , D₁ ⟧S +S ⟦ x ⟧S)
                eq₁) ⟩
      ⟦ T₁ , D₁ ⟧S +S ⟦ T₂ , D₂ ⟧S
        ≡ₛ⟨ reflₛ ⟩
      (⟦ D₁ ⟧L -S ⟦ T₁ ⟧L) +S (⟦ D₂ ⟧L -S ⟦ T₂ ⟧L)
        ≡ₛ⟨ symₛ asso-+S ⟩
      ⟦ D₁ ⟧L +S ((-S ⟦ T₁ ⟧L) +S (⟦ D₂ ⟧L -S ⟦ T₂ ⟧L))
        ≡ₛ⟨ ctxtₛ
              ((CC (⟦ D₁ ⟧L)) +C ●)
              commu-+S ⟩
      ⟦ D₁ ⟧L +S ((⟦ D₂ ⟧L -S ⟦ T₂ ⟧L) -S ⟦ T₁ ⟧L)
        ≡ₛ⟨ ctxtₛ
              ((CC (⟦ D₁ ⟧L)) +C ●)
              (symₛ asso-+S) ⟩
      ⟦ D₁ ⟧L +S (⟦ D₂ ⟧L +S ((-S ⟦ T₂ ⟧L) -S ⟦ T₁ ⟧L))
        ≡ₛ⟨ asso-+S ⟩
      (⟦ D₁ ⟧L +S ⟦ D₂ ⟧L) +S ((-S ⟦ T₂ ⟧L) -S ⟦ T₁ ⟧L)
        ≡ₛ⟨ ctxtₛ
             ((CC (⟦ D₁ ⟧L +S ⟦ D₂ ⟧L)) +C ●)
             (symₛ -S-distri) ⟩
      (⟦ D₁ ⟧L +S ⟦ D₂ ⟧L) -S (⟦ T₂ ⟧L +S ⟦ T₁ ⟧L)
        ≡ₛ⟨ ctxtₛ
              (● -C (CC (⟦ T₂ ⟧L +S ⟦ T₁ ⟧L)))
              commu-+S ⟩
      (⟦ D₂ ⟧L +S ⟦ D₁ ⟧L) -S (⟦ T₂ ⟧L +S ⟦ T₁ ⟧L)
        ≡ₛ⟨ ctxtₛ
              (● -C (CC (⟦ T₂ ⟧L +S ⟦ T₁ ⟧L)))
              (symₛ sem-union-eq-plus) ⟩
      ⟦ union D₂ D₁ ⟧L -S (⟦ T₂ ⟧L +S ⟦ T₁ ⟧L)
        ≡ₛ⟨ ctxtₛ
              ((CC (⟦ union D₂ D₁ ⟧L)) -C ●)
              (symₛ sem-union-eq-plus) ⟩
      ⟦ union D₂ D₁ ⟧L -S (⟦ union T₂ T₁ ⟧L)
        ≡ₛ⟨ reflₛ ⟩
      ⟦ (union T₂ T₁) , (union D₂ D₁) ⟧S ∎ₛ
  createStructuralPreproofFunCorrect {G ∣ (T , D) ∣ .(T₁ , D₁)} (consLC (consLC LCG .(T , D) zero) (T₁ , D₁) (suc zero)) SPP CPP=SPP | nothing | [ eq ] with toSeq LCG | inspect toSeq LCG
  createStructuralPreproofFunCorrect {G ∣ (T , D) ∣ .(T₁ , D₁)} (consLC (consLC LCG .(T , D) zero) (T₁ , D₁) (suc zero)) SPP CPP=SPP | nothing | [ eq ] | T₂ , D₂ | [ eq₁ ] = 
    beginₛ
      ⟦ HSeqToSeq (getStructuralLeaf SPP) ⟧S
        ≡ₛ⟨ congₛ
              (cong
                (⟦_⟧S ∘ HSeqToSeq ∘ getStructuralLeaf)
                (just-injective (sym CPP=SPP))) ⟩
      ⟦ HSeqToSeq (getStructuralLeaf (keepLast G (T₁ , D₁))) ⟧S
        ≡ₛ⟨ congₛ
              (cong
                (⟦_⟧S ∘ HSeqToSeq)
                (keepLastLeaf G (T₁ , D₁))) ⟩
      ⟦ HSeqToSeq (head (T₁ , D₁)) ⟧S
        ≡ₛ⟨ reflₛ ⟩
      ⟦ T₁ , D₁ ⟧S
        ≡ₛ⟨ symₛ
              (congₛ
                (cong
                  ⟦_⟧S
                  (unionSeqNeutral (T₁ , D₁)))) ⟩
      ⟦ unionSeq ([] , []) (T₁ , D₁) ⟧S
        ≡ₛ⟨ congₛ
              (cong
                (λ x -> ⟦ unionSeq x (T₁ , D₁) ⟧S)
                (sym
                  (begin
                    (T₂ , D₂)
                      ≡⟨ sym eq₁ ⟩
                    toSeq LCG
                      ≡⟨ refl ⟩
                    toSeq (consLC (consLC LCG (T , D) 0) (T₁ , D₁) zero)
                      ≡⟨ toSeqNothing
                           (consLC (consLC LCG (T , D) 0) (T₁ , D₁) zero)
                           eq ⟩
                    [] , [] ∎))) ⟩
      ⟦ unionSeq (T₂ , D₂) (T₁ , D₁) ⟧S ∎ₛ
  createStructuralPreproofFunCorrect {G ∣ (T , D) ∣ .(T₁ , D₁)} (consLC (consLC LCG .(T , D) (suc x)) (T₁ , D₁) (suc zero)) SPP CPP=SPP | nothing | [ eq ] =
    ⊥-elim
      (createStructuralPreproofVLCGNoNothing
        {LCG = consLC (consLC LCG (T , D) (suc x)) (T₁ , D₁) 0}
        (valid-consLC-before (valid-consLC-now (T , D) x LCG) (T₁ , D₁) 0)
        eq)
  createStructuralPreproofFunCorrect {G ∣ (T , D) ∣ .(T₁ , D₁)} (consLC LCG (T₁ , D₁) (suc (suc x))) SPP CPP=SPP with toSeq (consLC LCG (T₁ , D₁) (suc x)) | inspect toSeq (consLC LCG (T₁ , D₁) (suc x))
  createStructuralPreproofFunCorrect {G ∣ (T , D) ∣ .(T₁ , D₁)} (consLC LCG (T₁ , D₁) (suc (suc x))) SPP CPP=SPP | T₂ , D₂ | [ eq ] with createStructuralPreproofFun (consLC LCG (T₁ , D₁) (suc x)) | inspect createStructuralPreproofFun (consLC LCG (T₁ , D₁) (suc x))
  createStructuralPreproofFunCorrect {G ∣ (T , D) ∣ .(T₁ , D₁)} (consLC LCG (T₁ , D₁) (suc (suc x))) SPP CPP=SPP | T₂ , D₂ | [ eq ] | just indSPP | [ eq₁ ] = 
    beginₛ
      ⟦ HSeqToSeq (getStructuralLeaf SPP) ⟧S
        ≡ₛ⟨ congₛ
              (cong
                (⟦_⟧S ∘ HSeqToSeq ∘ getStructuralLeaf)
                (just-injective (sym CPP=SPP))) ⟩
      ⟦ HSeqToSeq (getStructuralLeaf (addFirst (head (T₁ , D₁)) indSPP)) ⟧S
        ≡ₛ⟨ congₛ
              (cong
                (⟦_⟧S ∘ HSeqToSeq)
                (addFirstLeaf indSPP (head (T₁ , D₁)))) ⟩
      ⟦ HSeqToSeq (unionHSeq (head (T₁ , D₁)) (getStructuralLeaf indSPP)) ⟧S
        ≡ₛ⟨ semHSeqToSeqUnion (head (T₁ , D₁)) (getStructuralLeaf indSPP) ⟩
      ⟦ HSeqToSeq (head (T₁ , D₁)) ⟧S +S ⟦ HSeqToSeq (getStructuralLeaf indSPP) ⟧S
        ≡ₛ⟨ reflₛ ⟩
      ⟦ T₁ , D₁ ⟧S +S ⟦ HSeqToSeq (getStructuralLeaf indSPP) ⟧S
        ≡ₛ⟨ ctxtₛ
              ((CC (⟦ T₁ , D₁ ⟧S)) +C ●)
              (createStructuralPreproofFunCorrect
                (consLC LCG (T₁ , D₁) (suc x))
                indSPP
                eq₁) ⟩
      ⟦ T₁ , D₁ ⟧S +S ⟦ toSeq (consLC LCG (T₁ , D₁) (suc x)) ⟧S
        ≡ₛ⟨ congₛ
              (cong
                (λ x -> ⟦ T₁ , D₁ ⟧S +S ⟦ x ⟧S)
                eq) ⟩
      ⟦ T₁ , D₁ ⟧S +S ⟦ T₂ , D₂ ⟧S
        ≡ₛ⟨ reflₛ ⟩
      (⟦ D₁ ⟧L -S ⟦ T₁ ⟧L) +S (⟦ D₂ ⟧L -S ⟦ T₂ ⟧L)
        ≡ₛ⟨ symₛ asso-+S ⟩
      ⟦ D₁ ⟧L +S ((-S ⟦ T₁ ⟧L) +S (⟦ D₂ ⟧L -S ⟦ T₂ ⟧L))
        ≡ₛ⟨ ctxtₛ
              ((CC (⟦ D₁ ⟧L)) +C ●)
              commu-+S ⟩
      ⟦ D₁ ⟧L +S ((⟦ D₂ ⟧L -S ⟦ T₂ ⟧L) -S ⟦ T₁ ⟧L)
        ≡ₛ⟨ ctxtₛ
              ((CC (⟦ D₁ ⟧L)) +C ●)
              (symₛ asso-+S) ⟩
      ⟦ D₁ ⟧L +S (⟦ D₂ ⟧L +S ((-S ⟦ T₂ ⟧L) -S ⟦ T₁ ⟧L))
        ≡ₛ⟨ asso-+S ⟩
      (⟦ D₁ ⟧L +S ⟦ D₂ ⟧L) +S ((-S ⟦ T₂ ⟧L) -S ⟦ T₁ ⟧L)
        ≡ₛ⟨ ctxtₛ
             ((CC (⟦ D₁ ⟧L +S ⟦ D₂ ⟧L)) +C ●)
             (symₛ -S-distri) ⟩
      (⟦ D₁ ⟧L +S ⟦ D₂ ⟧L) -S (⟦ T₂ ⟧L +S ⟦ T₁ ⟧L)
        ≡ₛ⟨ ctxtₛ
              (● -C (CC (⟦ T₂ ⟧L +S ⟦ T₁ ⟧L)))
              commu-+S ⟩
      (⟦ D₂ ⟧L +S ⟦ D₁ ⟧L) -S (⟦ T₂ ⟧L +S ⟦ T₁ ⟧L)
        ≡ₛ⟨ ctxtₛ
              (● -C (CC (⟦ T₂ ⟧L +S ⟦ T₁ ⟧L)))
              (symₛ sem-union-eq-plus) ⟩
      ⟦ union D₂ D₁ ⟧L -S (⟦ T₂ ⟧L +S ⟦ T₁ ⟧L)
        ≡ₛ⟨ ctxtₛ
              ((CC (⟦ union D₂ D₁ ⟧L)) -C ●)
              (symₛ sem-union-eq-plus) ⟩
      ⟦ union D₂ D₁ ⟧L -S (⟦ union T₂ T₁ ⟧L)
        ≡ₛ⟨ reflₛ ⟩
      ⟦ (union T₂ T₁) , (union D₂ D₁) ⟧S ∎ₛ
  createStructuralPreproofFunCorrect {G ∣ (T , D) ∣ .(T₁ , D₁)} (consLC LCG (T₁ , D₁) (suc (suc x))) SPP CPP=SPP | T₂ , D₂ | [ eq ] | nothing | [ eq₁ ] =
    ⊥-elim
      (createStructuralPreproofVLCGNoNothing
        {LCG = consLC LCG (T₁ , D₁) (suc x)}
        (valid-consLC-now (T₁ , D₁) x LCG)
        eq₁)
--}}}

  createStructuralPreproofCorrect :
    {G : HSeq} ->
    {LCG : LinearCombinaison G} ->
    (vLCG : valid-LC LCG) ->
    ⟦ HSeqToSeq (getStructuralLeaf (createStructuralPreproof vLCG)) ⟧S ≡ₛ ⟦ toSeq LCG ⟧S
--{{{
  createStructuralPreproofCorrect {G} {LCG} vLCG with createStructuralPreproofFun LCG | inspect createStructuralPreproofFun LCG
  createStructuralPreproofCorrect {G} {LCG} vLCG | just SPP | [ eq ] =
    createStructuralPreproofFunCorrect LCG SPP eq
  createStructuralPreproofCorrect {G} {LCG} vLCG | nothing | [ eq ] =
    ⊥-elim (createStructuralPreproofVLCGNoNothing vLCG eq)
--}}}

  finalStructuralPreproof :
    {G : HSeq} ->
    {LCG : LinearCombinaison G} ->
    (vLCG : valid-LC LCG) ->
    StructuralPreproof G
--{{{
  finalStructuralPreproof vLCG =
    continueStructuralPreproof
      (createStructuralPreproof vLCG)
      (applyS-Rule (getStructuralLeaf (createStructuralPreproof vLCG)))
--}}}

  unfoldHSeqToSeq :
    (G : HSeq) ->
    (H : Seq) ->
    HSeqToSeq (G ∣ H) ≡ unionSeq H (HSeqToSeq G)
--{{{
  unfoldHSeqToSeq G (T , D) with HSeqToSeq G
  unfoldHSeqToSeq G (T , D) | T₁ , D₁ =
    refl
--}}}

  applyS-RuleFun-correct :
    (G : HSeq) ->
    (accSG : Acc _<_ (size G)) ->
    ⟦ HSeqToSeq G ⟧S ≡ₛ ⟦ HSeqToSeq (getStructuralLeaf (applyS-RuleFun G accSG)) ⟧S
--{{{
  applyS-RuleFun-correct (head H) (acc rs) =
    reflₛ
  applyS-RuleFun-correct (head (T , D) ∣ (T₁ , D₁)) (acc rs) =
    beginₛ
      ⟦ union D₁ D ⟧L -S ⟦ union T₁ T ⟧L
        ≡ₛ⟨ ctxtₛ
              (● -C (CC (⟦ union T₁ T ⟧L)))
              sem-union-eq-plus ⟩
      (⟦ D₁ ⟧L +S ⟦ D ⟧L) -S ⟦ union T₁ T ⟧L
        ≡ₛ⟨ ctxtₛ
              (● -C (CC (⟦ union T₁ T ⟧L)))
              commu-+S ⟩
      (⟦ D ⟧L +S ⟦ D₁ ⟧L) -S ⟦ union T₁ T ⟧L
        ≡ₛ⟨ ctxtₛ
              (● -C (CC (⟦ union T₁ T ⟧L)))
              (symₛ sem-union-eq-plus) ⟩
      ⟦ union D D₁ ⟧L -S ⟦ union T₁ T ⟧L
        ≡ₛ⟨ ctxtₛ
              ((CC (⟦ union D D₁ ⟧L)) -C ●)
              sem-union-eq-plus ⟩
      ⟦ union D D₁ ⟧L -S (⟦ T₁ ⟧L +S ⟦ T ⟧L)
        ≡ₛ⟨ ctxtₛ
              ((CC (⟦ union D D₁ ⟧L)) -C ●)
              commu-+S ⟩
      ⟦ union D D₁ ⟧L -S (⟦ T ⟧L +S ⟦ T₁ ⟧L)
        ≡ₛ⟨ ctxtₛ
              ((CC (⟦ union D D₁ ⟧L)) -C ●)
              (symₛ sem-union-eq-plus) ⟩
      ⟦ union D D₁ ⟧L -S ⟦ union T T₁ ⟧L ∎ₛ
  applyS-RuleFun-correct (G ∣ (T , D) ∣ (T₁ , D₁)) (acc rs) with HSeqToSeq G | inspect HSeqToSeq G
  applyS-RuleFun-correct (G ∣ (T , D) ∣ (T₁ , D₁)) (acc rs) | T₂ , D₂ | [ eq ] =
    beginₛ
      ⟦ union T₁ (union T T₂) , union D₁ (union D D₂) ⟧S
        ≡ₛ⟨ congₛ
              (cong
                (λ x -> ⟦ x , union D₁ (union D D₂) ⟧S)
                (sym (unionAsso T₁ T T₂))) ⟩
      ⟦ union (union T₁ T) T₂ , union D₁ (union D D₂) ⟧S
        ≡ₛ⟨ ctxtₛ
              ((CC ⟦ union D₁ (union D D₂) ⟧L) -C ●)
              (ListExchangeSem
                (unionKeepListExchange
                  (unionSymExchange T₁ T)
                  (idLE {T₂}))) ⟩
      ⟦ union (union T T₁) T₂ , union D₁ (union D D₂) ⟧S
        ≡ₛ⟨ congₛ
              (cong
                (λ x -> ⟦ union (union T T₁) T₂ , x ⟧S)
                (sym (unionAsso D₁ D D₂))) ⟩
      ⟦ union (union T T₁) T₂ , union (union D₁ D) D₂ ⟧S
        ≡ₛ⟨ ctxtₛ
              (● -C (CC ⟦ union (union T T₁) T₂ ⟧L))
              (ListExchangeSem
                {union (union D₁ D) D₂}
                {union (union D D₁) D₂}
                (unionKeepListExchange
                  (unionSymExchange D₁ D)
                  (idLE {D₂}))) ⟩
      ⟦ unionSeq (union T T₁ , union D D₁) (T₂ , D₂) ⟧S
        ≡ₛ⟨ congₛ
              (cong
                (λ x -> ⟦ unionSeq (union T T₁ , union D D₁) x ⟧S)
                (sym eq)) ⟩
      ⟦ unionSeq (union T T₁ , union D D₁) (HSeqToSeq G)  ⟧S
        ≡ₛ⟨ congₛ
              (cong
                ⟦_⟧S
                (sym (unfoldHSeqToSeq G (union T T₁ , union D D₁)))) ⟩
      ⟦ HSeqToSeq (G ∣ (union T T₁ , union D D₁)) ⟧S
        ≡ₛ⟨ applyS-RuleFun-correct
              (G ∣ (union T T₁ , union D D₁))
              (rs (suc (size G)) (s≤s (s≤s (≤-reflexive refl)))) ⟩
      ⟦ HSeqToSeq  (getStructuralLeaf (applyS-RuleFun (G ∣ (union T T₁ , union D D₁)) (rs (suc (size G)) (s≤s (s≤s (≤-reflexive refl)))))) ⟧S ∎ₛ
--}}}

  finalStructuralPreproofCorrectLemma :
    {G : HSeq} ->
    {LCG : LinearCombinaison G} ->
    (vLCG : valid-LC LCG) ->
    ⟦ toSeq LCG ⟧S ≡ₛ botAG ->
    ⟦ HSeqToSeq (getStructuralLeaf (finalStructuralPreproof vLCG)) ⟧S ≡ₛ botAG
--{{{
  finalStructuralPreproofCorrectLemma {G} {LCG} vLCG eq =
    beginₛ
      ⟦ HSeqToSeq (getStructuralLeaf (finalStructuralPreproof vLCG)) ⟧S
        ≡ₛ⟨ congₛ
              (cong
                (⟦_⟧S ∘ HSeqToSeq)
                (getLeafContinuedProof (createStructuralPreproof vLCG) (applyS-Rule (getStructuralLeaf (createStructuralPreproof vLCG))))) ⟩
      ⟦ HSeqToSeq (getStructuralLeaf (applyS-Rule (getStructuralLeaf (createStructuralPreproof vLCG)))) ⟧S
        ≡ₛ⟨ symₛ
              (applyS-RuleFun-correct
                (getStructuralLeaf (createStructuralPreproof vLCG))
                (ℕ-acc (size (getStructuralLeaf (createStructuralPreproof vLCG))))) ⟩
      ⟦ HSeqToSeq (getStructuralLeaf (createStructuralPreproof vLCG)) ⟧S
        ≡ₛ⟨ createStructuralPreproofCorrect vLCG ⟩
      ⟦ toSeq LCG ⟧S
        ≡ₛ⟨ eq ⟩
      botAG ∎ₛ
--}}}

  finalStructuralPreproofCorrect :
    {G : HSeq} ->
    {LCG : LinearCombinaison G} ->
    (vLCG : valid-LC LCG) ->
    getStructuralLeaf (finalStructuralPreproof vLCG) ≡ head (toSeq (identityLC (getStructuralLeaf (createStructuralPreproof vLCG))))
  finalStructuralPreproofCorrect {G} {LCG} vLCG =
    trans
      (getLeafContinuedProof
        (createStructuralPreproof vLCG)
        (applyS-Rule (getStructuralLeaf (createStructuralPreproof vLCG))))
      (applyS-RuleGiveSeq (getStructuralLeaf (createStructuralPreproof vLCG)))

  identityLCKeepOp :
    (G : HSeq) ->
    (maxG=0 : maxOp G ≡ 0) ->
    nbOpSeq (toSeq (identityLC G)) ≡ 0
  identityLCKeepOp (head H) maxG=0 =
    maxG=0
  identityLCKeepOp (G ∣ H) maxG=0 with toSeq (identityLC G) | inspect toSeq (identityLC G)
  identityLCKeepOp (G ∣ (T , D)) maxG=0 | T₁ , D₁ | [ eq ] = 
    begin
      nbOpListFor (union T₁ T) + nbOpListFor (union D₁ D)
        ≡⟨ cong
             (λ x -> x + nbOpListFor (union D₁ D))
             (unionOp T₁ T) ⟩
      (nbOpListFor T₁ + nbOpListFor T) + (nbOpListFor (union D₁ D))
        ≡⟨ cong
             (λ x -> (nbOpListFor T₁ + nbOpListFor T) + x)
             (unionOp D₁ D) ⟩
      (nbOpListFor T₁ + nbOpListFor T) + (nbOpListFor D₁ + nbOpListFor D)
        ≡⟨ cong
             (λ x -> (x + nbOpListFor T) + (nbOpListFor D₁ + nbOpListFor D))
             {nbOpListFor T₁}
             {0}
             (≤-antisym
               (cong-≤-r
                 {nbOpListFor T₁ + nbOpListFor D₁}
                 (begin
                   nbOpListFor T₁ + nbOpListFor D₁
                     ≡⟨ cong
                          nbOpSeq
                          (sym eq) ⟩
                   nbOpSeq (toSeq (identityLC G))
                     ≡⟨ identityLCKeepOp
                          G
                          (≤-antisym
                            (≤-trans
                              ≤-⊔
                              (cong-≤-l
                                (sym maxG=0)
                                ≤-refl))
                            z≤n) ⟩
                   0 ∎)
                 a≤a+b)
               z≤n) ⟩
      nbOpListFor T + (nbOpListFor D₁ + nbOpListFor D)
        ≡⟨ cong
             (λ x -> x + (nbOpListFor D₁ + nbOpListFor D))
             {nbOpListFor T}
             {0}
             (≤-antisym
               (≤-trans
                 {j = nbOpListFor T + nbOpListFor D}
                 a≤a+b
                 (≤-trans
                   ≤-⊔
                   (cong-≤-l
                     (⊔-comm (maxOp G) (nbOpListFor T + nbOpListFor D))
                     (cong-≤-l
                       (sym maxG=0)
                       ≤-refl))))
               z≤n) ⟩
      nbOpListFor D₁ + nbOpListFor D
        ≡⟨ cong
             (λ x -> x + nbOpListFor D)
             {nbOpListFor D₁}
             {0}
             (≤-antisym
               (cong-≤-r
                 {nbOpListFor T₁ + nbOpListFor D₁}
                 (begin
                   nbOpListFor T₁ + nbOpListFor D₁
                     ≡⟨ cong
                          nbOpSeq
                          (sym eq) ⟩
                   nbOpSeq (toSeq (identityLC G))
                     ≡⟨ identityLCKeepOp
                          G
                          (≤-antisym
                            (≤-trans
                              ≤-⊔
                              (cong-≤-l
                                (sym maxG=0)
                                ≤-refl))
                            z≤n) ⟩
                   0 ∎)
                 (cong-≤-r
                   (+-comm (nbOpListFor D₁) (nbOpListFor T₁))
                   a≤a+b))
               z≤n) ⟩
      nbOpListFor D
        ≡⟨ (≤-antisym
             (≤-trans
               {j = nbOpListFor T + nbOpListFor D}
               (cong-≤-r
                 (+-comm (nbOpListFor D) (nbOpListFor T))
                 a≤a+b)
               (≤-trans
                 ≤-⊔
                 (cong-≤-l
                   (⊔-comm (maxOp G) (nbOpListFor T + nbOpListFor D))
                   (cong-≤-l
                     (sym maxG=0)
                     ≤-refl))))
             z≤n) ⟩
      0 ∎
