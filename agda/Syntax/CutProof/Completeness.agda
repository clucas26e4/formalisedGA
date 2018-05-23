module Syntax.CutProof.Completeness where
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

  {- Semantic -}
  open import Semantic.SemEquality
  open import Semantic.SemEquality.Properties
  open import Semantic.Interpretation

  mutual
    completeness1 :
      {A B : Term} ->
      A ≡ₛ B ->
      CutProof (head ([] ∷ A , [] ∷ B))
    completeness1 {A} reflₛ =
      ax A
    completeness1 (transₛ {A} {B} {B'} A=B B=B') =
      cut [] ([] ∷ A) ([] ∷ B') [] B
        (completeness1 B=B')
        (completeness1 A=B)
    completeness1 (symₛ A=B) =
      completeness2 A=B
    completeness1 (ctxtₛ ● A=B) =
      completeness1 A=B
    completeness1 (ctxtₛ (CC x) A=B) =
      ax x
    completeness1 (ctxtₛ (varC x) A=B) =
      ax (varAG x)
    completeness1 (ctxtₛ botC A=B) =
      ax botAG
    completeness1 (ctxtₛ {A} {B} (Ctxt ⊔C Ctxt₁) A=B) =
      max-L-head
        []
        ([] ∷ ((_[_] Ctxt B) ⊔S (_[_] Ctxt₁ B)))
        (_[_] Ctxt A)
        (_[_] Ctxt₁ A)
        (max-R-head
          ([] ∷ (_[_] Ctxt A))
          []
          (_[_] Ctxt B)
          (_[_] Ctxt₁ B)
          (W-head
            ([] ∷ _[_] Ctxt A)
            ([] ∷ _[_] Ctxt A)
            ([] ∷ _[_] Ctxt B)
            ([] ∷ _[_] Ctxt₁ B)
            (completeness1 (ctxtₛ Ctxt A=B))))
        (max-R-head
          ([] ∷ (_[_] Ctxt₁ A))
          []
          (_[_] Ctxt B)
          (_[_] Ctxt₁ B)
          (hseq-exchange
            (head (([] ∷ _[_] Ctxt₁ A) , [] ∷ _[_] Ctxt₁ B) ∣ ([] ∷ _[_] Ctxt₁ A , [] ∷ _[_] Ctxt B))
            (head (([] ∷ (_[_] Ctxt₁ A)) , ([] ∷ (_[_] Ctxt B))) ∣ (([] ∷ (_[_] Ctxt₁ A)) , ([] ∷ (_[_] Ctxt₁ B))))
            exHE-head
            (W-head
              ([] ∷ _[_] Ctxt₁ A)
              ([] ∷ _[_] Ctxt₁ A)
              ([] ∷ _[_] Ctxt₁ B)
              ([] ∷ _[_] Ctxt B)
              (completeness1 (ctxtₛ Ctxt₁ A=B)))))
    completeness1 (ctxtₛ {A} {B} (Ctxt +C Ctxt₁) A=B) =
      plus-R-head
        ([] ∷ ((_[_] Ctxt A) +S (_[_] Ctxt₁ A)))
        []
        (_[_] Ctxt B)
        (_[_] Ctxt₁ B)
        (plus-L-head
          []
          ([] ∷ _[_] Ctxt B ∷ _[_] Ctxt₁ B)
          (_[_] Ctxt A)
          (_[_] Ctxt₁ A)
          (M-head
            ([] ∷ _[_] Ctxt A)
            ([] ∷ _[_] Ctxt₁ A)
            ([] ∷ _[_] Ctxt B)
            ([] ∷ _[_] Ctxt₁ B)
            (completeness1 (ctxtₛ Ctxt A=B))
            (completeness1 (ctxtₛ Ctxt₁ A=B))))
    completeness1 (ctxtₛ {A} {B} (Ctxt ⊓C Ctxt₁) A=B) = 
      min-R-head
        ([] ∷ ((_[_] Ctxt A) ⊓S (_[_] Ctxt₁ A)))
        []
        (_[_] Ctxt B)
        (_[_] Ctxt₁ B)
        (min-L-head
          []
          ([] ∷ (_[_] Ctxt B))
          (_[_] Ctxt A)
          (_[_] Ctxt₁ A)
          (W-head
            ([] ∷ _[_] Ctxt A)
            ([] ∷ _[_] Ctxt₁ A)
            ([] ∷ _[_] Ctxt B)
            ([] ∷ _[_] Ctxt B)
            (completeness1 (ctxtₛ Ctxt A=B))))
        (min-L-head
          []
          ([] ∷ (_[_] Ctxt₁ B))
          (_[_] Ctxt A)
          (_[_] Ctxt₁ A)
          (hseq-exchange
            (head (([] ∷ _[_] Ctxt₁ A) , [] ∷ _[_] Ctxt₁ B) ∣ ([] ∷ _[_] Ctxt A , [] ∷ _[_] Ctxt₁ B))
            (head (([] ∷ (_[_] Ctxt A)) , ([] ∷ (_[_] Ctxt₁ B))) ∣ (([] ∷ (_[_] Ctxt₁ A)) , ([] ∷ (_[_] Ctxt₁ B))))
            exHE-head
            (W-head
              ([] ∷ _[_] Ctxt₁ A)
              ([] ∷ _[_] Ctxt A)
              ([] ∷ _[_] Ctxt₁ B)
              ([] ∷ _[_] Ctxt₁ B)
              (completeness1 (ctxtₛ Ctxt₁ A=B)))))
    completeness1 (ctxtₛ {A} {B} (-C Ctxt) A=B) = 
      minus-L-head
        []
        ([] ∷ (-S (_[_] Ctxt B)))
        (_[_] Ctxt A)
        (seq-exchange-head
          []
          []
          ([] ∷ (_[_] Ctxt A) ∷ (-S (_[_] Ctxt B)))
          ([] ∷ (-S (_[_] Ctxt B)) ∷ (_[_] Ctxt A))
          idLE
          (exLE
            (idLE {[]}))
          (minus-R-head
            []
            ([] ∷ (_[_] Ctxt A))
            (_[_] Ctxt B)
            (completeness2 (ctxtₛ Ctxt A=B))))
    completeness1 (substₛ {varAG zero} {k = zero} A=B) =
      completeness1 A=B
    completeness1 (substₛ {varAG zero} {k = suc k} A=B) =
      ax (varAG zero)
    completeness1 (substₛ {varAG (suc x)} {k = zero} A=B) =
      ax (varAG (suc x))
    completeness1 (substₛ {varAG (suc x)} {k = suc k} A=B) =
      completeness1 (substₛ {varAG x} {k = k} A=B)
    completeness1 (substₛ {botAG} A=B) =
      ax botAG
    completeness1 (substₛ {A ⊔S A₁} {B} {B'} {k} A=B) =
      max-L-head
        []
        ([] ∷ ((A [ B' / k ]) ⊔S (A₁ [ B' / k ])))
        (A [ B / k ])
        (A₁ [ B / k ])
        (max-R-head
          ([] ∷ (A [ B / k ]))
          []
          (A [ B' / k ])
          (A₁ [ B' / k ])
          (W-head
            ([] ∷ (A [ B / k ]))
            ([] ∷ (A [ B / k ]))
            ([] ∷ (A [ B' / k ]))
            ([] ∷ (A₁ [ B' / k ]))
            (completeness1 (substₛ {A} A=B))))
        (max-R-head
          ([] ∷ (A₁ [ B / k ]))
          []
          (A [ B' / k ])
          (A₁ [ B' / k ])
          (hseq-exchange
            (head (([] ∷ (A₁ [ B / k ])) , ([] ∷ (A₁ [ B' / k ]))) ∣ (([] ∷ (A₁ [ B / k ])) , ([] ∷ (A [ B' / k ]))))
            (head (([] ∷ (A₁ [ B / k ])) , ([] ∷ (A [ B' / k ]))) ∣ (([] ∷ (A₁ [ B / k ])) , ([] ∷ (A₁ [ B' / k ]))))
            exHE-head
            (W-head
              ([] ∷ (A₁ [ B / k ]))
              ([] ∷ (A₁ [ B / k ]))
              ([] ∷ (A₁ [ B' / k ]))
              ([] ∷ (A [ B' / k ]))
              (completeness1 (substₛ {A₁} A=B)))))
    completeness1 (substₛ {A +S A₁} A=B) = {!!}
    completeness1 (substₛ {A ⊓S A₁} A=B) = {!!}
    completeness1 (substₛ { -S A} A=B) = {!!}
    completeness1 (asso-+S {A} {B} {B'}) =
      plus-R-head
        ([] ∷ (A +S (B +S B')))
        []
        (A +S B)
        B'
        (plus-L-head
          []
          ([] ∷ (A +S B) ∷ B')
          A
          (B +S B')
          (plus-L-head
            ([] ∷ A)
            ([] ∷ (A +S B) ∷ B')
            B
            B'
            (M-head
              ([] ∷ A ∷ B)
              ([] ∷ B')
              ([] ∷ (A +S B))
              ([] ∷ B')
              (plus-R-head
                ([] ∷ A ∷ B)
                []
                A
                B
                (M-head
                  ([] ∷ A)
                  ([] ∷ B)
                  ([] ∷ A)
                  ([] ∷ B)
                  (ax A)
                  (ax B)))
              (ax B'))))
    completeness1 (commu-+S {A} {B}) =
      plus-R-head
        ([] ∷ (A +S B))
        []
        B
        A
        (plus-L-head
          []
          ([] ∷ B ∷ A)
          A
          B
          (seq-exchange-head
            ([] ∷ A ∷ B)
            ([] ∷ A ∷ B)
            ([] ∷ A ∷ B)
            ([] ∷ B ∷ A)
            idLE
            (exLE idLE)
            (M-head
              ([] ∷ A)
              ([] ∷ B)
              ([] ∷ A)
              ([] ∷ B)
              (ax A)
              (ax B))))
    completeness1 (neutral-+S {A}) =
      plus-L-head
        []
        ([] ∷ A)
        A
        botAG
        (Z-L-head
          ([] ∷ A)
          ([] ∷ A)
          (ax A))
    completeness1 (opp-+S {A}) =
      Z-R-head
        ([] ∷ (A -S A))
        []
        (plus-L-head
          []
          []
          A
          (-S A)
          (minus-L-head
            ([] ∷ A)
            []
            A
            (ax A)))
    completeness1 (asso-⊔S {A} {B} {B'}) =
      max-L-head
        []
        ([] ∷ ((A ⊔S B) ⊔S B'))
        A
        (B ⊔S B')
        (max-R-head
          ([] ∷ A)
          []
          (A ⊔S B)
          B'
          (W-head
            ([] ∷ A)
            ([] ∷ A)
            ([] ∷ (A ⊔S B))
            ([] ∷ B')
            (max-R-head
              ([] ∷ A)
              []
              A
              B
              (W-head
                ([] ∷ A)
                ([] ∷ A)
                ([] ∷ A)
                ([] ∷ B)
                (ax A)))))
        (max-L-head
          []
          ([] ∷ ((A ⊔S B) ⊔S B'))
          B
          B'
          (max-R-head
            ([] ∷ B)
            []
            (A ⊔S B)
            B'
            (W-head
              ([] ∷ B)
              ([] ∷ B)
              ([] ∷ (A ⊔S B))
              ([] ∷ B')
              (max-R-head
                ([] ∷ B)
                []
                A
                B
                (hseq-exchange
                  (head (([] ∷ B) , [] ∷ B) ∣ ([] ∷ B , [] ∷ A))
                  (head (([] ∷ B) , ([] ∷ A)) ∣ (([] ∷ B) , ([] ∷ B)))
                  exHE-head
                  (W-head
                    ([] ∷ B)
                    ([] ∷ B)
                    ([] ∷ B)
                    ([] ∷ A)
                    (ax B))))))
          (max-R-head
            ([] ∷ B')
            []
            (A ⊔S B)
            B'
            (hseq-exchange
              (head (([] ∷ B') , [] ∷ B') ∣ ([] ∷ B' , [] ∷ (A ⊔S B)))
              (head (([] ∷ B') , ([] ∷ (A ⊔S B))) ∣ (([] ∷ B') , ([] ∷ B')))
              exHE-head
              (W-head
                ([] ∷ B')
                ([] ∷ B')
                ([] ∷ B')
                ([] ∷ (A ⊔S B))
                (ax B')))))
    completeness1 (commu-⊔S {A} {B}) =
      max-L-head
        []
        ([] ∷ (B ⊔S A))
        A
        B
        (max-R-head
          ([] ∷ A)
          []
          B
          A
          (hseq-exchange
            (head ([] ∷ A , [] ∷ A) ∣ ([] ∷ A , [] ∷ B))
            (head (([] ∷ A) , ([] ∷ B)) ∣ (([] ∷ A) , ([] ∷ A)))
            exHE-head
            (W-head
              ([] ∷ A)
              ([] ∷ A)
              ([] ∷ A)
              ([] ∷ B)
              (ax A))))
        (max-R-head
          ([] ∷ B)
          []
          B
          A
          (W-head
            ([] ∷ B)
            ([] ∷ B)
            ([] ∷ B)
            ([] ∷ A)
            (ax B)))
    completeness1 (abso-⊔S {A} {B}) =
      max-L-head
        []
        ([] ∷ A)
        A
        (A ⊓S B)
        (ax A)
        (min-L-head
          []
          ([] ∷ A)
          A
          B
          (W-head
            ([] ∷ A)
            ([] ∷ B)
            ([] ∷ A)
            ([] ∷ A)
            (ax A)))
    completeness1 (asso-⊓S {A} {B} {B'}) =
      min-R-head
        ([] ∷ (A ⊓S (B ⊓S B')))
        []
        (A ⊓S B)
        B'
        (min-R-head
          ([] ∷ (A ⊓S (B ⊓S B')))
          []
          A
          B
          (min-L-head
            []
            ([] ∷ A)
            A
            (B ⊓S B')
            (W-head
              ([] ∷ A)
              ([] ∷ (B ⊓S B'))
              ([] ∷ A)
              ([] ∷ A)
              (ax A)))
          (min-L-head
            []
            ([] ∷ B)
            A
            (B ⊓S B')
            (hseq-exchange
              (head ([] ∷ (B ⊓S B') , [] ∷ B) ∣ ([] ∷ A , [] ∷ B))
              (head (([] ∷ A) , ([] ∷ B)) ∣ (([] ∷ (B ⊓S B')) , ([] ∷ B)))
              exHE-head
              (W-head
                ([] ∷ (B ⊓S B'))
                ([] ∷ A)
                ([] ∷ B)
                ([] ∷ B)
                (min-L-head
                  []
                  ([] ∷ B)
                  B
                  B'
                  (W-head
                    ([] ∷ B)
                    ([] ∷ B')
                    ([] ∷ B)
                    ([] ∷ B)
                    (ax B)))))))
        (min-L-head
          []
          ([] ∷ B')
          A
          (B ⊓S B')
          (hseq-exchange
            (head ([] ∷ (B ⊓S B') , [] ∷ B') ∣ ([] ∷ A , [] ∷ B'))
            (head (([] ∷ A) , ([] ∷ B')) ∣ (([] ∷ (B ⊓S B')) , ([] ∷ B')))
            exHE-head
            (W-head
              ([] ∷ (B ⊓S B'))
              ([] ∷ A)
              ([] ∷ B')
              ([] ∷ B')
              (min-L-head
                []
                ([] ∷ B')
                B
                B'
                (hseq-exchange
                  (head ([] ∷ B' , [] ∷ B') ∣ ([] ∷ B , [] ∷ B'))
                  (head (([] ∷ B) , ([] ∷ B')) ∣ (([] ∷ B') , ([] ∷ B')))
                  exHE-head
                  (W-head
                    ([] ∷ B')
                    ([] ∷ B)
                    ([] ∷ B')
                    ([] ∷ B')
                    (ax B')))))))
    completeness1 (commu-⊓S {A} {B}) =
      min-R-head
        ([] ∷ (A ⊓S B))
        []
        B
        A
        (min-L-head
          []
          ([] ∷ B)
          A
          B
          (hseq-exchange
            (head ([] ∷ B , [] ∷ B) ∣ ([] ∷ A , [] ∷ B))
            (head ([] ∷ A , [] ∷ B) ∣ ([] ∷ B , [] ∷ B))
            exHE-head
            (W-head
              ([] ∷ B)
              ([] ∷ A)
              ([] ∷ B)
              ([] ∷ B)
              (ax B))))
        (min-L-head
          []
          ([] ∷ A)
          A
          B
          (W-head
            ([] ∷ A)
            ([] ∷ B)
            ([] ∷ A)
            ([] ∷ A)
            (ax A)))
    completeness1 (abso-⊓S {A} {B}) =
      min-L-head
        []
        ([] ∷ A)
        A
        (A ⊔S B)
        (W-head
          ([] ∷ A)
          ([] ∷ (A ⊔S B))
          ([] ∷ A)
          ([] ∷ A)
          (ax A))
    completeness1 (compa-+S {A} {B} {B'}) =
      min-L-head
        []
        ([] ∷ (A ⊓S B +S B'))
        (A ⊓S B +S B')
        (B +S B')
        (W-head
          ([] ∷ (A ⊓S B +S B'))
          ([] ∷ (B +S B'))
          ([] ∷ (A ⊓S B +S B'))
          ([] ∷ (A ⊓S B +S B'))
          (ax (A ⊓S B +S B')))

    completeness2 :
      {A B : Term} ->
      A ≡ₛ B ->
      CutProof (head ([] ∷ B , [] ∷ A))
    completeness2 (reflₛ {A}) =
      ax A
    completeness2 (transₛ {A} {B} {B'} A=B A=B₁) =
      cut
        []
        ([] ∷ B')
        ([] ∷ A)
        []
        B
        (completeness2 A=B)
        (completeness2 A=B₁)
    completeness2 (symₛ A=B) =
      completeness1 A=B
    completeness2 (ctxtₛ Ctxt A=B) = {!!}
    completeness2 (substₛ A=B) = {!!}
    completeness2 asso-+S = {!!}
    completeness2 commu-+S = {!!}
    completeness2 neutral-+S = {!!}
    completeness2 opp-+S = {!!}
    completeness2 asso-⊔S = {!!}
    completeness2 commu-⊔S = {!!}
    completeness2 abso-⊔S = {!!}
    completeness2 (asso-⊓S {A} {B} {B'}) = 
      min-R-head
        ([] ∷ ((A ⊓S B) ⊓S B'))
        []
        A
        (B ⊓S B')
        (min-L-head
          []
          ([] ∷ A)
          (A ⊓S B)
          B'
          (W-head
            ([] ∷ (A ⊓S B))
            ([] ∷ B')
            ([] ∷ A)
            ([] ∷ A)
            (min-L-head
              []
              ([] ∷ A)
              A
              B
              (W-head
                ([] ∷ A)
                ([] ∷ B)
                ([] ∷ A)
                ([] ∷ A)
                (ax A)))))
        (min-R-head
          ([] ∷ ((A ⊓S B) ⊓S B'))
          []
          B
          B'
          (min-L-head
            []
            ([] ∷ B)
            (A ⊓S B)
            B'
            (W-head
              ([] ∷ (A ⊓S B))
              ([] ∷ B')
              ([] ∷ B)
              ([] ∷ B)
              (min-L-head
                []
                ([] ∷ B)
                A
                B
                (hseq-exchange
                  (head ([] ∷ B , [] ∷ B) ∣ ([] ∷ A , [] ∷ B))
                  (head (([] ∷ A) , ([] ∷ B)) ∣ (([] ∷ B) , ([] ∷ B)))
                  exHE-head
                  (W-head
                    ([] ∷ B)
                    ([] ∷ A)
                    ([] ∷ B)
                    ([] ∷ B)
                    (ax B))))))
          (min-L-head
            []
            ([] ∷ B')
            (A ⊓S B)
            B'
            (hseq-exchange
              (head ([] ∷ B' , [] ∷ B') ∣ ([] ∷ (A ⊓S B) , [] ∷ B'))
              (head (([] ∷ (A ⊓S B)) , ([] ∷ B')) ∣ (([] ∷ B') , ([] ∷ B')))
              exHE-head
              (W-head
                ([] ∷ B')
                ([] ∷ (A ⊓S B))
                ([] ∷ B')
                ([] ∷ B')
                (ax B')))))
    completeness2 commu-⊓S = {!!}
    completeness2 abso-⊓S = {!!}
    completeness2 compa-+S = {!!}
