module Syntax.CutProof.Invertibility where
  {- STDLIB -}
  open import Nat
  open import Equality
  open import Data.Empty
  open import Relation.Nullary

  {- Syntax -}
  open import Syntax.Term
  open import Syntax.ListTerm
  open import Syntax.ListTerm.Properties
  open import Syntax.Seq
  open import Syntax.HSeq
  open import Syntax.CutProof
  open import Syntax.CutProof.Soundness

  {- Semantic -}
  open import Semantic.SemEquality
  open import Semantic.SemEquality.Properties
  open import Semantic.Interpretation

  Z-L-invert :
    (G : HSeq) ->
    (Γ Δ : ListTerm) ->
    botAG ≤S ⟦ G ∣ (Γ ∷ botAG , Δ) ⟧ ->
    botAG ≤S ⟦ G ∣ (Γ , Δ) ⟧
  Z-L-invert G Γ Δ hyp =
    ≤S-cong-r
      (ctxtₛ
        ((CC ⟦ G ⟧) ⊔C ((CC ⟦ Δ ⟧L) -C ●))
        neutral-+S)
      hyp

  Z-L-head-invert :
    (Γ Δ : ListTerm) ->
    botAG ≤S ⟦ head (Γ ∷ botAG , Δ) ⟧ ->
    botAG ≤S ⟦ head (Γ , Δ) ⟧
  Z-L-head-invert Γ Δ hyp =
    ≤S-cong-r
      (ctxtₛ
        (((CC ⟦ Δ ⟧L) -C ●))
        neutral-+S)
      hyp

  Z-R-invert :
    (G : HSeq) ->
    (Γ Δ : ListTerm) ->
    botAG ≤S ⟦ G ∣ (Γ , Δ ∷ botAG) ⟧ ->
    botAG ≤S ⟦ G ∣ (Γ , Δ) ⟧
  Z-R-invert G Γ Δ hyp =
    ≤S-cong-r
      (ctxtₛ
        ((CC ⟦ G ⟧) ⊔C ((● -C CC ⟦ Γ ⟧L)))
        neutral-+S)
      hyp

  Z-R-head-invert :
    (Γ Δ : ListTerm) ->
    botAG ≤S ⟦ head (Γ , Δ ∷ botAG) ⟧ ->
    botAG ≤S ⟦ head (Γ , Δ) ⟧
  Z-R-head-invert Γ Δ hyp =
    ≤S-cong-r
      (ctxtₛ
        ((● -C (CC ⟦ Γ ⟧L)))
        neutral-+S)
      hyp

  minus-L-invert :
    (G : HSeq) ->
    (Γ Δ : ListTerm) ->
    (A : Term) ->
    botAG ≤S ⟦ G ∣ (Γ ∷ (-S A) , Δ) ⟧ ->
    botAG ≤S ⟦ G ∣ (Γ , Δ ∷ A) ⟧
  minus-L-invert G Γ Δ A hyp =
    ≤S-cong-r
      (ctxtₛ
        ((CC (⟦ G ⟧)) ⊔C ●)
        (beginₛ
          ⟦ Δ ⟧L +S (-S (⟦ Γ ⟧L +S (-S A)))
            ≡ₛ⟨ ctxtₛ
                  ((CC ⟦ Δ ⟧L) +C ●)
                  -S-distri ⟩
          ⟦ Δ ⟧L +S ((-S (⟦ Γ ⟧L)) +S (-S (-S A)))
            ≡ₛ⟨ ctxtₛ
                  ((CC ⟦ Δ ⟧L) +C ((CC (-S  (⟦ Γ ⟧L))) +C ●))
                  -S--S ⟩
          ⟦ Δ ⟧L +S ((-S (⟦ Γ ⟧L)) +S A)
            ≡ₛ⟨ ctxtₛ
                  ((CC ⟦ Δ ⟧L) +C ●)
                  commu-+S ⟩
          ⟦ Δ ⟧L +S (A +S (-S (⟦ Γ ⟧L)))
            ≡ₛ⟨ asso-+S ⟩
          (⟦ Δ ⟧L +S A) +S (-S ⟦ Γ ⟧L) ∎ₛ))
      hyp

  minus-L-head-invert :
    (Γ Δ : ListTerm) ->
    (A : Term) ->
    botAG ≤S ⟦ head (Γ ∷ (-S A) , Δ) ⟧ ->
    botAG ≤S ⟦ head (Γ , Δ ∷ A) ⟧
  minus-L-head-invert Γ Δ A hyp =
    ≤S-cong-r
      (beginₛ
        ⟦ Δ ⟧L +S (-S (⟦ Γ ⟧L +S (-S A)))
          ≡ₛ⟨ ctxtₛ
                ((CC ⟦ Δ ⟧L) +C ●)
                -S-distri ⟩
        ⟦ Δ ⟧L +S ((-S (⟦ Γ ⟧L)) +S (-S (-S A)))
          ≡ₛ⟨ ctxtₛ
                ((CC ⟦ Δ ⟧L) +C ((CC (-S  (⟦ Γ ⟧L))) +C ●))
                -S--S ⟩
        ⟦ Δ ⟧L +S ((-S (⟦ Γ ⟧L)) +S A)
          ≡ₛ⟨ ctxtₛ
                ((CC ⟦ Δ ⟧L) +C ●)
                commu-+S ⟩
        ⟦ Δ ⟧L +S (A +S (-S (⟦ Γ ⟧L)))
          ≡ₛ⟨ asso-+S ⟩
        (⟦ Δ ⟧L +S A) +S (-S ⟦ Γ ⟧L) ∎ₛ)
      hyp

  minus-R-invert :
    (G : HSeq) ->
    (Γ Δ : ListTerm) ->
    (A : Term) ->
    botAG ≤S ⟦ G ∣ (Γ , Δ ∷ (-S A)) ⟧ ->
    botAG ≤S ⟦ G ∣ (Γ ∷ A , Δ) ⟧
  minus-R-invert G Γ Δ A hyp =
    ≤S-cong-r
      (ctxtₛ
        ((CC (⟦ G ⟧)) ⊔C ●)
        (beginₛ
          (⟦ Δ ⟧L -S A) -S (⟦ Γ ⟧L)
            ≡ₛ⟨ symₛ asso-+S ⟩
          ⟦ Δ ⟧L +S ((-S A) -S (⟦ Γ ⟧L))
            ≡ₛ⟨ ctxtₛ
                  ((CC ⟦ Δ ⟧L) +C ●)
                  commu-+S ⟩
          ⟦ Δ ⟧L +S ((-S (⟦ Γ ⟧L)) -S A)
            ≡ₛ⟨ ctxtₛ
                  ((CC ⟦ Δ ⟧L) +C ●)
                  (symₛ -S-distri) ⟩
          (⟦ Δ ⟧L) -S (⟦ Γ ⟧L +S A) ∎ₛ))
      hyp

  minus-R-head-invert :
    (Γ Δ : ListTerm) ->
    (A : Term) ->
    botAG ≤S ⟦ head (Γ , Δ ∷ (-S A)) ⟧ ->
    botAG ≤S ⟦ head (Γ ∷ A , Δ) ⟧
  minus-R-head-invert Γ Δ A hyp =
    ≤S-cong-r
      (beginₛ
        (⟦ Δ ⟧L -S A) -S (⟦ Γ ⟧L)
          ≡ₛ⟨ symₛ asso-+S ⟩
        ⟦ Δ ⟧L +S ((-S A) -S (⟦ Γ ⟧L))
          ≡ₛ⟨ ctxtₛ
                ((CC ⟦ Δ ⟧L) +C ●)
                commu-+S ⟩
        ⟦ Δ ⟧L +S ((-S (⟦ Γ ⟧L)) -S A)
          ≡ₛ⟨ ctxtₛ
                ((CC ⟦ Δ ⟧L) +C ●)
                (symₛ -S-distri) ⟩
        (⟦ Δ ⟧L) -S (⟦ Γ ⟧L +S A) ∎ₛ)
      hyp

  plus-L-invert :
    (G : HSeq) ->
    (Γ Δ : ListTerm) ->
    (A B : Term) ->
    botAG ≤S ⟦ G ∣ (Γ ∷ (A +S B), Δ) ⟧ ->
    botAG ≤S ⟦ G ∣ (Γ ∷ A ∷ B , Δ) ⟧
  plus-L-invert G Γ Δ A B hyp =
    ≤S-cong-r
      (ctxtₛ
        ((CC ⟦ G ⟧) ⊔C ●)
        (ctxtₛ
          ((CC ⟦ Δ ⟧L) +C (-C ●))
          asso-+S))
      hyp

  plus-L-head-invert :
    (Γ Δ : ListTerm) ->
    (A B : Term) ->
    botAG ≤S ⟦ head (Γ ∷ (A +S B), Δ) ⟧ ->
    botAG ≤S ⟦ head (Γ ∷ A ∷ B , Δ) ⟧
  plus-L-head-invert Γ Δ A B hyp =
    ≤S-cong-r
      (ctxtₛ
        ((CC ⟦ Δ ⟧L) +C (-C ●))
        asso-+S)
      hyp

  plus-R-invert :
    (G : HSeq) ->
    (Γ Δ : ListTerm) ->
    (A B : Term) ->
    botAG ≤S ⟦ G ∣ (Γ , Δ ∷ (A +S B)) ⟧ ->
    botAG ≤S ⟦ G ∣ (Γ , Δ ∷ A ∷ B) ⟧
  plus-R-invert G Γ Δ A B hyp =
    ≤S-cong-r
      (ctxtₛ
        ((CC ⟦ G ⟧) ⊔C ●)
        (ctxtₛ
          (● +C (-C (CC ⟦ Γ ⟧L)))
          asso-+S))
      hyp

  plus-R-head-invert :
    (Γ Δ : ListTerm) ->
    (A B : Term) ->
    botAG ≤S ⟦ head (Γ , Δ ∷ (A +S B)) ⟧ ->
    botAG ≤S ⟦ head (Γ , Δ ∷ A ∷ B) ⟧
  plus-R-head-invert Γ Δ A B hyp =
    ≤S-cong-r
      (ctxtₛ
        (● -C (CC ⟦ Γ ⟧L))
        asso-+S)
      hyp

  max-L-invert-1 :
    (G : HSeq) ->
    (Γ Δ : ListTerm) ->
    (A B : Term) ->
    botAG ≤S ⟦ G ∣(Γ ∷ (A ⊔S B), Δ) ⟧ ->
    botAG ≤S ⟦ G ∣(Γ ∷ A , Δ) ⟧
  max-L-invert-1 G Γ Δ A B hyp =
    ≤S-trans
      hyp
      (⊔S-≤S
        ≤S-⊔S
        (≤S-trans
          {B = (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S A))}
          (≤S-cong-r
            commu-+S
            (≤S-cong-l
              commu-+S
              (≤S-+S
                (≤S--S
                  (≤S-cong-l
                    commu-+S
                    (≤S-cong-r
                      commu-+S
                      (≤S-+S
                        ≤S-⊔S)))))))
          (≤S-cong-r
            commu-⊔S
            ≤S-⊔S)))

  max-L-invert-2 :
    (G : HSeq) ->
    (Γ Δ : ListTerm) ->
    (A B : Term) ->
    botAG ≤S ⟦ G ∣(Γ ∷ (A ⊔S B), Δ) ⟧ ->
    botAG ≤S ⟦ G ∣(Γ ∷ B , Δ) ⟧
  max-L-invert-2 G Γ Δ A B hyp =
    ≤S-trans
      hyp
      (⊔S-≤S
        ≤S-⊔S
        (≤S-trans
          {B = (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S B))}
          (≤S-cong-r
            commu-+S
            (≤S-cong-l
              commu-+S
              (≤S-+S
                (≤S--S
                  (≤S-cong-l
                    commu-+S
                    (≤S-cong-r
                      commu-+S
                      (≤S-+S
                        (≤S-cong-r
                          commu-⊔S
                          ≤S-⊔S))))))))
          (≤S-cong-r
            commu-⊔S
            ≤S-⊔S)))

  max-L-head-invert-1 :
    (Γ Δ : ListTerm) ->
    (A B : Term) ->
    botAG ≤S ⟦ head (Γ ∷ (A ⊔S B), Δ) ⟧ ->
    botAG ≤S ⟦ head (Γ ∷ A , Δ) ⟧
  max-L-head-invert-1 Γ Δ A B hyp =
    ≤S-trans
      hyp
      (≤S-cong-r
        commu-+S
          (≤S-cong-l
            commu-+S
            (≤S-+S
              (≤S--S
                (≤S-cong-l
                  commu-+S
                  (≤S-cong-r
                    commu-+S
                    (≤S-+S
                      ≤S-⊔S)))))))

  max-L-head-invert-2 :
    (Γ Δ : ListTerm) ->
    (A B : Term) ->
    botAG ≤S ⟦ head (Γ ∷ (A ⊔S B), Δ) ⟧ ->
    botAG ≤S ⟦ head (Γ ∷ B , Δ) ⟧
  max-L-head-invert-2 Γ Δ A B hyp =
    ≤S-trans
      hyp
      (≤S-cong-r
        commu-+S
          (≤S-cong-l
            commu-+S
            (≤S-+S
              (≤S--S
                (≤S-cong-l
                  commu-+S
                  (≤S-cong-r
                    commu-+S
                    (≤S-+S
                      (≤S-cong-r
                        commu-⊔S
                        ≤S-⊔S))))))))

  max-R-invert :
    (G : HSeq) ->
    (Γ Δ : ListTerm) ->
    (A B : Term) ->
    botAG ≤S ⟦ G ∣(Γ , Δ ∷ (A ⊔S B)) ⟧ ->
    botAG ≤S ⟦ G ∣(Γ , Δ ∷ A)∣(Γ , Δ ∷ B) ⟧
  max-R-invert G Γ Δ A B hyp =
    ≤S-cong-r
      (symₛ
        (transₛ
          (symₛ asso-⊔S)
          (ctxtₛ
            ((CC ⟦ G ⟧) ⊔C ●)
            (beginₛ
              ((⟦ Δ ⟧L +S A) -S ⟦ Γ ⟧L) ⊔S ((⟦ Δ ⟧L +S B) -S ⟦ Γ ⟧L)
                ≡ₛ⟨ symₛ ⊔S-+S ⟩
              ((⟦ Δ ⟧L +S A) ⊔S (⟦ Δ ⟧L +S B)) -S ⟦ Γ ⟧L
                ≡ₛ⟨ ctxtₛ
                      ((● ⊔C (CC (⟦ Δ ⟧L +S B))) -C (CC (⟦ Γ ⟧L)))
                      commu-+S ⟩
              ((A +S ⟦ Δ ⟧L) ⊔S (⟦ Δ ⟧L +S B)) -S ⟦ Γ ⟧L
                ≡ₛ⟨ ctxtₛ
                      (((CC (A +S ⟦ Δ ⟧L)) ⊔C ●) -C (CC ⟦ Γ ⟧L))
                      commu-+S ⟩
              ((A +S ⟦ Δ ⟧L) ⊔S (B +S ⟦ Δ ⟧L)) -S ⟦ Γ ⟧L
                ≡ₛ⟨ ctxtₛ
                      (● -C (CC ⟦ Γ ⟧L))
                      (symₛ ⊔S-+S) ⟩
              ((A ⊔S B) +S ⟦ Δ ⟧L) -S ⟦ Γ ⟧L
                ≡ₛ⟨ ctxtₛ
                      (● -C (CC ⟦ Γ ⟧L))
                      commu-+S ⟩
              (⟦ Δ ⟧L +S (A ⊔S B)) -S ⟦ Γ ⟧L ∎ₛ))))
      hyp

  max-R-head-invert :
    (Γ Δ : ListTerm) ->
    (A B : Term) ->
    botAG ≤S ⟦ head (Γ , Δ ∷ (A ⊔S B)) ⟧ ->
    botAG ≤S ⟦ head (Γ , Δ ∷ A)∣(Γ , Δ ∷ B) ⟧
  max-R-head-invert Γ Δ A B hyp =
    ≤S-cong-r
      (symₛ
        (beginₛ
          ((⟦ Δ ⟧L +S A) -S ⟦ Γ ⟧L) ⊔S ((⟦ Δ ⟧L +S B) -S ⟦ Γ ⟧L)
            ≡ₛ⟨ symₛ ⊔S-+S ⟩
          ((⟦ Δ ⟧L +S A) ⊔S (⟦ Δ ⟧L +S B)) -S ⟦ Γ ⟧L
            ≡ₛ⟨ ctxtₛ
                  ((● ⊔C (CC (⟦ Δ ⟧L +S B))) -C (CC (⟦ Γ ⟧L)))
                  commu-+S ⟩
          ((A +S ⟦ Δ ⟧L) ⊔S (⟦ Δ ⟧L +S B)) -S ⟦ Γ ⟧L
            ≡ₛ⟨ ctxtₛ
                  (((CC (A +S ⟦ Δ ⟧L)) ⊔C ●) -C (CC ⟦ Γ ⟧L))
                  commu-+S ⟩
          ((A +S ⟦ Δ ⟧L) ⊔S (B +S ⟦ Δ ⟧L)) -S ⟦ Γ ⟧L
            ≡ₛ⟨ ctxtₛ
                  (● -C (CC ⟦ Γ ⟧L))
                  (symₛ ⊔S-+S) ⟩
          ((A ⊔S B) +S ⟦ Δ ⟧L) -S ⟦ Γ ⟧L
            ≡ₛ⟨ ctxtₛ
                  (● -C (CC ⟦ Γ ⟧L))
                  commu-+S ⟩
          (⟦ Δ ⟧L +S (A ⊔S B)) -S ⟦ Γ ⟧L ∎ₛ))
      hyp

  min-L-invert :
    (G : HSeq) ->
    (Γ Δ : ListTerm) ->
    (A B : Term) ->
    botAG ≤S ⟦ G ∣ (Γ ∷ (A ⊓S B), Δ) ⟧ ->
    botAG ≤S ⟦ G ∣ (Γ ∷ A , Δ) ∣ (Γ ∷ B , Δ) ⟧
  min-L-invert G Γ Δ A B hyp =
    ≤S-cong-r
      (symₛ
        (transₛ
          (ctxtₛ
            (((CC ⟦ G ⟧) ⊔C ●) ⊔C (CC (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S B))))
            (beginₛ
              ⟦ Δ ⟧L +S (-S (⟦ Γ ⟧L +S A))
                ≡ₛ⟨ ctxtₛ
                      ((CC ⟦ Δ ⟧L) +C ●)
                      -S-distri ⟩
              ⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) +S (-S A))
                ≡ₛ⟨ ctxtₛ
                      ((CC ⟦ Δ ⟧L) +C ●)
                      commu-+S ⟩
              ⟦ Δ ⟧L +S ((-S A) +S (-S ⟦ Γ ⟧L))
                ≡ₛ⟨ asso-+S ⟩
              (⟦ Δ ⟧L +S (-S A)) +S (-S ⟦ Γ ⟧L) ∎ₛ))
          (ctxtₛ
            (((CC ⟦ G ⟧) ⊔C (CC ((⟦ Δ ⟧L +S (-S A)) -S ⟦ Γ ⟧L))) ⊔C ●)
            (beginₛ
              ⟦ Δ ⟧L +S (-S (⟦ Γ ⟧L +S B))
                ≡ₛ⟨ ctxtₛ
                      ((CC ⟦ Δ ⟧L) +C ●)
                      -S-distri ⟩
              ⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) +S (-S B))
                ≡ₛ⟨ ctxtₛ
                      ((CC ⟦ Δ ⟧L) +C ●)
                      commu-+S ⟩
              ⟦ Δ ⟧L +S ((-S B) +S (-S ⟦ Γ ⟧L))
                ≡ₛ⟨ asso-+S ⟩
              (⟦ Δ ⟧L +S (-S B)) +S (-S ⟦ Γ ⟧L) ∎ₛ))))
      (max-R-invert
        G
        Γ
        Δ
        (-S A)
        (-S B)
        (≤S-cong-r
          (symₛ
            (ctxtₛ
            ((CC ⟦ G ⟧) ⊔C ●)
            (beginₛ
              (⟦ Δ ⟧L +S (-S A) ⊔S (-S B)) +S (-S ⟦ Γ ⟧L)
                ≡ₛ⟨ ctxtₛ
                      (((CC ⟦ Δ ⟧L) +C ●) +C (CC (-S ⟦ Γ ⟧L)))
                      (symₛ -S-⊓S-⊔S) ⟩
              (⟦ Δ ⟧L -S (A ⊓S B)) +S (-S ⟦ Γ ⟧L)
                ≡ₛ⟨ symₛ asso-+S ⟩
              ⟦ Δ ⟧L +S ((-S (A ⊓S B)) +S (-S ⟦ Γ ⟧L))
                ≡ₛ⟨ ctxtₛ
                      ((CC ⟦ Δ ⟧L) +C ●)
                      commu-+S ⟩
              ⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) +S (-S (A ⊓S B)))
                ≡ₛ⟨ ctxtₛ
                      ((CC ⟦ Δ ⟧L) +C ●)
                      (symₛ -S-distri) ⟩
              ⟦ Δ ⟧L +S (-S (⟦ Γ ⟧L +S (A ⊓S B))) ∎ₛ)))
          hyp))

  min-L-head-invert :
    (Γ Δ : ListTerm) ->
    (A B : Term) ->
    botAG ≤S ⟦ head (Γ ∷ (A ⊓S B), Δ) ⟧ ->
    botAG ≤S ⟦ head (Γ ∷ A , Δ) ∣ (Γ ∷ B , Δ) ⟧
  min-L-head-invert Γ Δ A B hyp =
    ≤S-cong-r
      (symₛ
        (transₛ
          (ctxtₛ
            (● ⊔C (CC (⟦ Δ ⟧L -S (⟦ Γ ⟧L +S B))))
            (beginₛ
              ⟦ Δ ⟧L +S (-S (⟦ Γ ⟧L +S A))
                ≡ₛ⟨ ctxtₛ
                      ((CC ⟦ Δ ⟧L) +C ●)
                      -S-distri ⟩
              ⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) +S (-S A))
                ≡ₛ⟨ ctxtₛ
                      ((CC ⟦ Δ ⟧L) +C ●)
                      commu-+S ⟩
              ⟦ Δ ⟧L +S ((-S A) +S (-S ⟦ Γ ⟧L))
                ≡ₛ⟨ asso-+S ⟩
              (⟦ Δ ⟧L +S (-S A)) +S (-S ⟦ Γ ⟧L) ∎ₛ))
          (ctxtₛ
            ((CC ((⟦ Δ ⟧L +S (-S A)) -S ⟦ Γ ⟧L)) ⊔C ●)
            (beginₛ
              ⟦ Δ ⟧L +S (-S (⟦ Γ ⟧L +S B))
                ≡ₛ⟨ ctxtₛ
                      ((CC ⟦ Δ ⟧L) +C ●)
                      -S-distri ⟩
              ⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) +S (-S B))
                ≡ₛ⟨ ctxtₛ
                      ((CC ⟦ Δ ⟧L) +C ●)
                      commu-+S ⟩
              ⟦ Δ ⟧L +S ((-S B) +S (-S ⟦ Γ ⟧L))
                ≡ₛ⟨ asso-+S ⟩
              (⟦ Δ ⟧L +S (-S B)) +S (-S ⟦ Γ ⟧L) ∎ₛ))))
      (max-R-head-invert
        Γ
        Δ
        (-S A)
        (-S B)
        (≤S-cong-r
          (symₛ
            (beginₛ
              (⟦ Δ ⟧L +S (-S A) ⊔S (-S B)) +S (-S ⟦ Γ ⟧L)
                ≡ₛ⟨ ctxtₛ
                      (((CC ⟦ Δ ⟧L) +C ●) +C (CC (-S ⟦ Γ ⟧L)))
                      (symₛ -S-⊓S-⊔S) ⟩
              (⟦ Δ ⟧L -S (A ⊓S B)) +S (-S ⟦ Γ ⟧L)
                ≡ₛ⟨ symₛ asso-+S ⟩
              ⟦ Δ ⟧L +S ((-S (A ⊓S B)) +S (-S ⟦ Γ ⟧L))
                ≡ₛ⟨ ctxtₛ
                      ((CC ⟦ Δ ⟧L) +C ●)
                      commu-+S ⟩
              ⟦ Δ ⟧L +S ((-S ⟦ Γ ⟧L) +S (-S (A ⊓S B)))
                ≡ₛ⟨ ctxtₛ
                      ((CC ⟦ Δ ⟧L) +C ●)
                      (symₛ -S-distri) ⟩
              ⟦ Δ ⟧L +S (-S (⟦ Γ ⟧L +S (A ⊓S B))) ∎ₛ))
          hyp))

  min-R-invert-1 :
    (G : HSeq) ->
    (Γ Δ : ListTerm) ->
    (A B : Term) ->
    botAG ≤S ⟦ G ∣ (Γ , Δ ∷ (A ⊓S B)) ⟧ ->
    botAG ≤S ⟦ G ∣ (Γ , Δ ∷ A) ⟧
  min-R-invert-1 G Γ Δ A B hyp =
    ≤S-trans
      hyp
      (⊔S-≤S
        ≤S-⊔S
        (≤S-trans
          (≤S-+S
            (≤S-cong-r
              commu-+S
              (≤S-cong-l
                commu-+S
                (≤S-+S
                  ⊓S-≤S))))
          (≤S-cong-r
            commu-⊔S
            ≤S-⊔S)))

  min-R-invert-2 :
    (G : HSeq) ->
    (Γ Δ : ListTerm) ->
    (A B : Term) ->
    botAG ≤S ⟦ G ∣ (Γ , Δ ∷ (A ⊓S B)) ⟧ ->
    botAG ≤S ⟦ G ∣ (Γ , Δ ∷ B) ⟧
  min-R-invert-2 G Γ Δ A B hyp =
    ≤S-trans
      hyp
      (⊔S-≤S
        ≤S-⊔S
        (≤S-trans
          (≤S-+S
            (≤S-cong-r
              commu-+S
              (≤S-cong-l
                commu-+S
                (≤S-+S
                  (≤S-cong-l
                    commu-⊓S
                    ⊓S-≤S)))))
          (≤S-cong-r
            commu-⊔S
            ≤S-⊔S)))

  min-R-head-invert-1 :
    (Γ Δ : ListTerm) ->
    (A B : Term) ->
    botAG ≤S ⟦ head (Γ , Δ ∷ (A ⊓S B)) ⟧ ->
    botAG ≤S ⟦ head (Γ , Δ ∷ A) ⟧
  min-R-head-invert-1 Γ Δ A B hyp =
    ≤S-trans
      hyp
      (≤S-+S
        (≤S-cong-l
          commu-+S
          (≤S-cong-r
            commu-+S
            (≤S-+S
              ⊓S-≤S))))

  min-R-head-invert-2 :
    (Γ Δ : ListTerm) ->
    (A B : Term) ->
    botAG ≤S ⟦ head (Γ , Δ ∷ (A ⊓S B)) ⟧ ->
    botAG ≤S ⟦ head (Γ , Δ ∷ B) ⟧
  min-R-head-invert-2 Γ Δ A B hyp =
    ≤S-trans
      hyp
      (≤S-+S
        (≤S-cong-l
          commu-+S
          (≤S-cong-r
            commu-+S
            (≤S-+S
              (≤S-cong-l
                commu-⊓S
                ⊓S-≤S)))))
                
  seq-exchange-invert :
    (G : HSeq) ->
    (Γ Γ' Δ Δ' : ListTerm) ->
    ListExchange Γ Γ' ->
    ListExchange Δ Δ' ->
    botAG ≤S ⟦ G ∣ (Γ' , Δ') ⟧ ->
    botAG ≤S ⟦ G ∣ (Γ , Δ) ⟧
  seq-exchange-invert G Γ Γ' Δ Δ' Γ=Γ' Δ=Δ' hyp =
    seq-exchange-sound
      G
      Γ'
      Γ
      Δ'
      Δ
      (ListExchangeSym Γ=Γ')
      (ListExchangeSym Δ=Δ')
      hyp
                
  seq-exchange-head-invert :
    (Γ Γ' Δ Δ' : ListTerm) ->
    ListExchange Γ Γ' ->
    ListExchange Δ Δ' ->
    botAG ≤S ⟦ head (Γ' , Δ') ⟧ ->
    botAG ≤S ⟦ head (Γ , Δ) ⟧
  seq-exchange-head-invert Γ Γ' Δ Δ' Γ=Γ' Δ=Δ' hyp =
    seq-exchange-head-sound
      Γ'
      Γ
      Δ'
      Δ
      (ListExchangeSym Γ=Γ')
      (ListExchangeSym Δ=Δ')
      hyp

  hseq-exchange-invert :
    (G G' : HSeq) ->
    HSeqExchange G G' ->
    botAG ≤S ⟦ G' ⟧ ->
    botAG ≤S ⟦ G ⟧
  hseq-exchange-invert G G' G=G' hyp =
    hseq-exchange-sound G' G (HSeqExchangeSym G=G') hyp
