{-                                                          -
 -                                                          -
 - Module of definition of the complexity of a hypersequent -
 -                                                          -
 -                                                          -}

module Syntax.HSeq.Complexity where

  {- STDLIB -}
  open import Nat
  open import Equality
  open import Data.Empty
  open import Data.Product
  open import Relation.Nullary
  open import Induction.WellFounded

  {- SYNTAX -}
  open import Syntax.Term
  open import Syntax.ListTerm
  open import Syntax.ListTerm.Properties
  open import Syntax.Seq
  open import Syntax.HSeq
  open import Syntax.ListSeq
  open import Syntax.HSeq.Ordered

  {- SEMANTIC -}

  data _<L_ : (ℕ × ℕ) -> (ℕ × ℕ) -> Set where
    first :
      {a₁ a₂ b₁ b₂ : ℕ} ->
      a₁ < a₂ ->
      (a₁ , b₁) <L (a₂ , b₂)
    second :
      {a b₁ b₂ : ℕ} ->
      b₁ < b₂ ->
      (a , b₁) <L (a , b₂)

  AccessibleLFunFirst0 :
    (b : ℕ) ->
    Acc _<_ b ->
    Acc _<L_ (0 , b)
--{{{
  AccessibleLFunFirst0 b (acc rs) =
    acc λ { (a , b') (first ())
          ; (.0 , b') (second x) → AccessibleLFunFirst0 b' (rs b' x)}
--}}}

  AccessibleLFunFirstSuc :
    (a b : ℕ) ->
    Acc _<L_ (a , b) ->
    Acc _<L_ (suc a , b)
--{{{
  AccessibleLFunFirstSuc a b (acc rs) =
    acc λ { (zero , b') (first x) → AccessibleLFunFirst0 b' (ℕ-acc b')
          ; (suc a' , b') (first (s≤s x)) → AccessibleLFunFirstSuc a' b' (rs (a' , b') (first x))
          ; ( (suc .a) , b') (second x) → AccessibleLFunFirstSuc a b' (rs (a , b') (second x))}
--}}}

  AccessibleLFun :
    (a₁ b₁ a₂ b₂ : ℕ) ->
    (a₁ , b₁) <L (a₂ , b₂) ->
    Acc _<L_ (a₁ , b₁)
--{{{
  AccessibleLFun zero b₁ a₂ b₂ x =
    AccessibleLFunFirst0 b₁ (ℕ-acc b₁)
  AccessibleLFun (suc a₁) b₁ zero b₂ (first ())
  AccessibleLFun (suc a₁) zero (suc a₂) zero (first (s≤s x)) =
    acc λ { (a₃ , b₃) (first x₁) → AccessibleLFun a₃ b₃ a₂ zero (first (≤-trans x₁ x))
          ; (suc .a₁ , b₃) (second ())}
  AccessibleLFun (suc a₁) zero (suc .a₁) zero (second ())
  AccessibleLFun (suc a₁) zero (suc a₂) (suc b₂) (first (s≤s x)) =
    acc λ { (a₃ , b₃) (first x₁) → AccessibleLFun a₃ b₃ a₂ (suc b₂) (first (≤-trans x₁ x))
          ; (suc _ , b₃) (second ())}
  AccessibleLFun (suc a₁) zero (suc .a₁) (suc b₂) (second x) = 
    acc λ { (zero , b₃) (first x₁) → AccessibleLFunFirst0 b₃ (ℕ-acc b₃)
          ; (suc a₃ , b₃) (first (s≤s x₁)) → AccessibleLFunFirstSuc a₃ b₃ (AccessibleLFun a₃ b₃ a₁ (suc b₂) (first x₁))
          ; (.(suc _) , b₃) (second ())}
  AccessibleLFun (suc a₁) (suc b₁) (suc a₂) zero (first (s≤s x)) =
    acc λ { (.0 , b₃) (first (s≤s z≤n)) → AccessibleLFunFirst0 b₃ (ℕ-acc b₃)
          ; ((suc a₃) , b₃) (first (s≤s (s≤s x₁))) → AccessibleLFunFirstSuc a₃ b₃ (AccessibleLFun a₃ b₃ a₂ zero (first (≤-trans (s≤s x₁) (≤-trans k≤sk x))))
          ; ((suc a₁) , b₃) (second x₁) → AccessibleLFunFirstSuc a₁ b₃ (AccessibleLFun a₁ b₃ a₂ zero (first x))}
  AccessibleLFun (suc a₁) (suc b₁) (suc .a₁) zero (second ())
  AccessibleLFun (suc a₁) (suc b₁) (suc a₂) (suc b₂) (first (s≤s x)) =
    acc λ { (.0 , b₃) (first (s≤s z≤n)) → AccessibleLFunFirst0 b₃ (ℕ-acc b₃)
          ; ((suc a₃) , b₃) (first (s≤s (s≤s x₁))) → AccessibleLFunFirstSuc a₃ b₃ (AccessibleLFun a₃ b₃ a₂ (suc b₂) (first (≤-trans (s≤s x₁) (≤-trans k≤sk x))))
          ; ((suc a₁) , b₃) (second x₁) → AccessibleLFunFirstSuc a₁ b₃ (AccessibleLFun a₁ b₃ a₂ (suc b₂) (first x))}

  AccessibleLFun (suc a₁) (suc b₁) (suc .a₁) (suc b₂) (second (s≤s x)) = 
    acc λ { (.0 , b₃) (first (s≤s z≤n)) → AccessibleLFunFirst0 b₃ (ℕ-acc b₃)
          ; ((suc a₃) , b₃) (first (s≤s (s≤s x₁))) → AccessibleLFunFirstSuc a₃ b₃ (AccessibleLFun a₃ b₃ a₁ b₂ (first (s≤s x₁)))
          ; ((suc .a₁) , b₃) (second x₁) → AccessibleLFunFirstSuc a₁ b₃ (AccessibleLFun a₁ b₃ a₁ (suc b₂) (second (≤-trans x₁ (≤-trans x k≤sk))))}
--}}}

  AccessibleL :
    (a,b : ℕ × ℕ) ->
    Acc _<L_ a,b
--{{{
  AccessibleL (a , b) =
    acc λ {(a' , b') x → AccessibleLFun a' b' a b x}
--}}}

  nbSeqCompl :
    (G : HSeq) ->
    (k : ℕ) ->
    ℕ
--{{{
  nbSeqCompl (head H) k with nbOpSeq H ≡? k
  nbSeqCompl (head H) k | yes p = 1
  nbSeqCompl (head H) k | no ¬p = 0
  nbSeqCompl (G ∣ H) k with nbOpSeq H ≡? k
  nbSeqCompl (G ∣ H) k | yes p = suc (nbSeqCompl G k)
  nbSeqCompl (G ∣ H) k | no ¬p = nbSeqCompl G k
--}}}

  complexity :
    (G : HSeq) ->
    ℕ × ℕ
--{{{
  complexity G = (maxOp G , nbSeqCompl G (maxOp G))
--}}}

  unfoldComplexity :
    (G : HSeq) ->
    (H : Seq) ->
    (HSize : maxOp G ≤ nbOpSeq H) ->
    complexity (G ∣ H) ≡ ((maxOp G ⊔ nbOpSeq H) , suc (nbSeqCompl G (maxOp G ⊔ nbOpSeq H)))
--{{{
  unfoldComplexity G H Hsize with nbOpSeq H ≡? (maxOp (G ∣ H))
  unfoldComplexity G H Hsize | yes p = refl
  unfoldComplexity G H Hsize | no ¬p =
    ⊥-elim (¬p (sym (k≤k'=>k⊔k'=k' Hsize)))
--}}}

  ExchangeSameMaxOp :
    {G G' : HSeq} ->
    (G=G' : HSeqExchange G G') ->
    maxOp G ≡ maxOp G'
--{{{
  ExchangeSameMaxOp idHE =
    refl
  ExchangeSameMaxOp {G ∣ H ∣ H'} {G' ∣ .H' ∣ .H} (exHE G=G') =
    begin
      maxOp G ⊔ nbOpSeq H ⊔ nbOpSeq H'
        ≡⟨ ⊔-assoc (maxOp G) (nbOpSeq H) (nbOpSeq H') ⟩
      maxOp G ⊔ (nbOpSeq H ⊔ nbOpSeq H')
        ≡⟨ cong (λ x -> maxOp G ⊔ x) (⊔-comm (nbOpSeq H) (nbOpSeq H')) ⟩
      maxOp G ⊔ (nbOpSeq H' ⊔ nbOpSeq H)
        ≡⟨ cong (λ x -> x ⊔ (nbOpSeq H' ⊔ nbOpSeq H)) (ExchangeSameMaxOp G=G') ⟩
      maxOp G' ⊔ (nbOpSeq H' ⊔ nbOpSeq H)
        ≡⟨ sym (⊔-assoc (maxOp G') (nbOpSeq H') (nbOpSeq H)) ⟩
      maxOp G' ⊔ nbOpSeq H' ⊔ nbOpSeq H ∎
  ExchangeSameMaxOp {head H ∣ H'} exHE-head =
    ⊔-comm (nbOpSeq H) (nbOpSeq H')
  ExchangeSameMaxOp (transHE {G} {G'} {G''} G=G' G=G'') =
    trans (ExchangeSameMaxOp G=G') (ExchangeSameMaxOp G=G'')
  ExchangeSameMaxOp (indHE G G' {H} G=G') =
    cong (λ x -> x ⊔ (nbOpSeq H)) (ExchangeSameMaxOp G=G')
--}}}

  ExchangeKeepNbSeqWithCompl :
    {G G' : HSeq} ->
    (G=G' : HSeqExchange G G') ->
    (k : ℕ) ->
    nbSeqCompl G k ≡ nbSeqCompl G' k
--{{{
  ExchangeKeepNbSeqWithCompl idHE k =
    refl
  ExchangeKeepNbSeqWithCompl {G ∣ H ∣ H'} {G' ∣ .H' ∣ .H} (exHE G=G') k with nbOpSeq H' ≡? k
  ExchangeKeepNbSeqWithCompl {G ∣ H ∣ H'} {G' ∣ .H' ∣ .H} (exHE G=G') k | yes p with nbOpSeq H ≡? k
  ExchangeKeepNbSeqWithCompl {G ∣ H ∣ H'} {G' ∣ .H' ∣ .H} (exHE G=G') k | yes p | yes p₁ with nbOpSeq H' ≡? k
  ExchangeKeepNbSeqWithCompl {G ∣ H ∣ H'} {G' ∣ .H' ∣ .H} (exHE G=G') k | yes p | yes p₁ | yes p₂ =
    cong (λ x -> suc (suc x)) (ExchangeKeepNbSeqWithCompl G=G' k)
  ExchangeKeepNbSeqWithCompl {G ∣ H ∣ H'} {G' ∣ .H' ∣ .H} (exHE G=G') k | yes p | yes p₁ | no ¬p =
    ⊥-elim (¬p p)
  ExchangeKeepNbSeqWithCompl {G ∣ H ∣ H'} {G' ∣ .H' ∣ .H} (exHE G=G') k | yes p | no ¬p with nbOpSeq H' ≡? k
  ExchangeKeepNbSeqWithCompl {G ∣ H ∣ H'} {G' ∣ .H' ∣ .H} (exHE G=G') k | yes p | no ¬p | yes p₁ =
    cong suc (ExchangeKeepNbSeqWithCompl G=G' k)
  ExchangeKeepNbSeqWithCompl {G ∣ H ∣ H'} {G' ∣ .H' ∣ .H} (exHE G=G') k | yes p | no ¬p | no ¬p₁ =
    ⊥-elim (¬p₁ p)
  ExchangeKeepNbSeqWithCompl {G ∣ H ∣ H'} {G' ∣ .H' ∣ .H} (exHE G=G') k | no ¬p with nbOpSeq H ≡? k
  ExchangeKeepNbSeqWithCompl {G ∣ H ∣ H'} {G' ∣ .H' ∣ .H} (exHE G=G') k | no ¬p | yes p with nbOpSeq H' ≡? k
  ExchangeKeepNbSeqWithCompl {G ∣ H ∣ H'} {G' ∣ .H' ∣ .H} (exHE G=G') k | no ¬p | yes p | yes p₁ =
    ⊥-elim (¬p p₁)
  ExchangeKeepNbSeqWithCompl {G ∣ H ∣ H'} {G' ∣ .H' ∣ .H} (exHE G=G') k | no ¬p | yes p | no ¬p₁ =
    cong suc (ExchangeKeepNbSeqWithCompl G=G' k)
  ExchangeKeepNbSeqWithCompl {G ∣ H ∣ H'} {G' ∣ .H' ∣ .H} (exHE G=G') k | no ¬p | no ¬p₁ with nbOpSeq H' ≡? k
  ExchangeKeepNbSeqWithCompl {G ∣ H ∣ H'} {G' ∣ .H' ∣ .H} (exHE G=G') k | no ¬p | no ¬p₁ | yes p = 
    ⊥-elim (¬p p)
  ExchangeKeepNbSeqWithCompl {G ∣ H ∣ H'} {G' ∣ .H' ∣ .H} (exHE G=G') k | no ¬p | no ¬p₁ | no ¬p₂ =
    ExchangeKeepNbSeqWithCompl G=G' k
  ExchangeKeepNbSeqWithCompl {head H ∣ H'} {head .H' ∣ .H} exHE-head k with nbOpSeq H' ≡? k
  ExchangeKeepNbSeqWithCompl {head H ∣ H'} {head .H' ∣ .H} exHE-head k | yes p with nbOpSeq H ≡? k
  ExchangeKeepNbSeqWithCompl {head H ∣ H'} {head .H' ∣ .H} exHE-head k | yes p | yes p₁ with nbOpSeq H' ≡? k
  ExchangeKeepNbSeqWithCompl {head H ∣ H'} {head .H' ∣ .H} exHE-head k | yes p | yes p₁ | yes p₂ = 
    refl
  ExchangeKeepNbSeqWithCompl {head H ∣ H'} {head .H' ∣ .H} exHE-head k | yes p | yes p₁ | no ¬p =
    ⊥-elim (¬p p)
  ExchangeKeepNbSeqWithCompl {head H ∣ H'} {head .H' ∣ .H} exHE-head k | yes p | no ¬p with nbOpSeq H' ≡? k
  ExchangeKeepNbSeqWithCompl {head H ∣ H'} {head .H' ∣ .H} exHE-head k | yes p | no ¬p | yes p₁ = 
    refl
  ExchangeKeepNbSeqWithCompl {head H ∣ H'} {head .H' ∣ .H} exHE-head k | yes p | no ¬p | no ¬p₁ = 
    ⊥-elim (¬p₁ p)
  ExchangeKeepNbSeqWithCompl {head H ∣ H'} {head .H' ∣ .H} exHE-head k | no ¬p with nbOpSeq H ≡? k
  ExchangeKeepNbSeqWithCompl {head H ∣ H'} {head .H' ∣ .H} exHE-head k | no ¬p | yes p with nbOpSeq H' ≡? k
  ExchangeKeepNbSeqWithCompl {head H ∣ H'} {head .H' ∣ .H} exHE-head k | no ¬p | yes p | yes p₁ =
    ⊥-elim (¬p p₁)
  ExchangeKeepNbSeqWithCompl {head H ∣ H'} {head .H' ∣ .H} exHE-head k | no ¬p | yes p | no ¬p₁ =
    refl
  ExchangeKeepNbSeqWithCompl {head H ∣ H'} {head .H' ∣ .H} exHE-head k | no ¬p | no ¬p₁ with nbOpSeq H' ≡? k
  ExchangeKeepNbSeqWithCompl {head H ∣ H'} {head .H' ∣ .H} exHE-head k | no ¬p | no ¬p₁ | yes p =
    ⊥-elim (¬p p)
  ExchangeKeepNbSeqWithCompl {head H ∣ H'} {head .H' ∣ .H} exHE-head k | no ¬p | no ¬p₁ | no ¬p₂ =
    refl
  ExchangeKeepNbSeqWithCompl (transHE G=G' G=G'') k =
    trans (ExchangeKeepNbSeqWithCompl G=G' k) (ExchangeKeepNbSeqWithCompl G=G'' k) 
  ExchangeKeepNbSeqWithCompl (indHE G G' {H} G=G') k with nbOpSeq H ≡? k
  ExchangeKeepNbSeqWithCompl (indHE G G' {H} G=G') k | yes p =
    cong suc (ExchangeKeepNbSeqWithCompl G=G' k)
  ExchangeKeepNbSeqWithCompl (indHE G G' {H} G=G') k | no ¬p =
    ExchangeKeepNbSeqWithCompl G=G' k
--}}}

  ExchangeKeepComplexity :
    {G G' : HSeq} ->
    (G=G' : HSeqExchange G G') ->
    complexity G ≡ complexity G'
--{{{
  ExchangeKeepComplexity {G} {G'} G=G' =
    begin
      (maxOp G , nbSeqCompl G (maxOp G))
        ≡⟨ cong (λ x -> (x , nbSeqCompl G x)) (ExchangeSameMaxOp G=G') ⟩
      (maxOp G' , nbSeqCompl G (maxOp G'))
        ≡⟨ cong (λ x -> maxOp G' , x) (ExchangeKeepNbSeqWithCompl G=G' (maxOp G')) ⟩
      (maxOp G' , nbSeqCompl G' (maxOp G')) ∎
--}}}

  ListExchangeLKeepMaxOp :
    (G : HSeq) ->
    {Γ Γ' : ListTerm} ->
    (Δ : ListTerm) ->
    (Γ=Γ' : ListExchange Γ Γ') ->
    maxOp (G ∣ (Γ , Δ)) ≡ maxOp (G ∣ (Γ' , Δ))
--{{{
  ListExchangeLKeepMaxOp G {Γ} {Γ'} Δ Γ=Γ' =
    cong (λ x -> maxOp G ⊔ (x + nbOpListFor Δ)) (ListExchangeKeepOp Γ=Γ')
--}}}

  ListExchangeLKeepNbSeqCompl :
    (G : HSeq) ->
    {Γ Γ' : ListTerm} ->
    (Δ : ListTerm) ->
    (Γ=Γ' : ListExchange Γ Γ') ->
    (k : ℕ) ->
    nbSeqCompl (G ∣ (Γ , Δ)) k ≡ nbSeqCompl (G ∣ (Γ' , Δ)) k
--{{{
  ListExchangeLKeepNbSeqCompl G {Γ} {Γ'} Δ Γ=Γ' k with (nbOpListFor Γ + nbOpListFor Δ) ≡? k
  ListExchangeLKeepNbSeqCompl G {Γ} {Γ'} Δ Γ=Γ' k | yes p with (nbOpListFor Γ' + nbOpListFor Δ) ≡? k
  ListExchangeLKeepNbSeqCompl G {Γ} {Γ'} Δ Γ=Γ' k | yes p | yes p₁ = 
    refl
  ListExchangeLKeepNbSeqCompl G {Γ} {Γ'} Δ Γ=Γ' k | yes p | no ¬p =
    ⊥-elim (¬p (trans (cong (λ x -> x + nbOpListFor Δ) (ListExchangeKeepOp (ListExchangeSym Γ=Γ'))) p))
  ListExchangeLKeepNbSeqCompl G {Γ} {Γ'} Δ Γ=Γ' k | no ¬p with (nbOpListFor Γ' + nbOpListFor Δ) ≡? k
  ListExchangeLKeepNbSeqCompl G {Γ} {Γ'} Δ Γ=Γ' k | no ¬p | yes p =
    ⊥-elim (¬p (trans (cong (λ x -> x + nbOpListFor Δ) (ListExchangeKeepOp Γ=Γ')) p))
  ListExchangeLKeepNbSeqCompl G {Γ} {Γ'} Δ Γ=Γ' k | no ¬p | no ¬p₁ =
    refl
--}}}

  ListExchangeLKeepComplexity :
    (G : HSeq) ->
    (Γ Γ' : ListTerm) ->
    (Δ : ListTerm) ->
    (Γ=Γ' : ListExchange Γ Γ') ->
    complexity (G ∣ (Γ , Δ)) ≡ complexity (G ∣ (Γ' , Δ))
--{{{
  ListExchangeLKeepComplexity G Γ Γ' Δ Γ=Γ' =
    begin
      (maxOp (G ∣ (Γ , Δ)) , nbSeqCompl (G ∣ (Γ , Δ)) (maxOp (G ∣ (Γ , Δ))))
        ≡⟨ cong (λ x -> (x , nbSeqCompl (G ∣ (Γ , Δ)) x)) (ListExchangeLKeepMaxOp G Δ Γ=Γ') ⟩
      (maxOp (G ∣ (Γ' , Δ)) , nbSeqCompl (G ∣ (Γ , Δ)) (maxOp (G ∣ (Γ' , Δ))))
        ≡⟨ cong (λ x -> maxOp (G ∣ (Γ' , Δ)) , x) (ListExchangeLKeepNbSeqCompl G Δ Γ=Γ' (maxOp (G ∣ (Γ' , Δ)))) ⟩
      (maxOp (G ∣ (Γ' , Δ)) , nbSeqCompl (G ∣ (Γ' , Δ)) (maxOp (G ∣ (Γ' , Δ)))) ∎
--}}}

  ListExchangeRKeepMaxOp :
    (G : HSeq) ->
    (Γ : ListTerm) ->
    {Δ Δ' : ListTerm} ->
    (Δ=Δ' : ListExchange Δ Δ') ->
    maxOp (G ∣ (Γ , Δ)) ≡ maxOp (G ∣ (Γ , Δ'))
--{{{
  ListExchangeRKeepMaxOp G Γ {Δ} {Δ'} Δ=Δ' =
    cong (λ x -> maxOp G ⊔ (nbOpListFor Γ + x)) (ListExchangeKeepOp Δ=Δ')
--}}}

  ListExchangeRKeepNbSeqCompl :
    (G : HSeq) ->
    (Γ : ListTerm) ->
    {Δ Δ' : ListTerm} ->
    (Δ=Δ' : ListExchange Δ Δ') ->
    (k : ℕ) ->
    nbSeqCompl (G ∣ (Γ , Δ)) k ≡ nbSeqCompl (G ∣ (Γ , Δ')) k
--{{{
  ListExchangeRKeepNbSeqCompl G Γ {Δ} {Δ'} Δ=Δ' k with (nbOpListFor Γ + nbOpListFor Δ) ≡? k
  ListExchangeRKeepNbSeqCompl G Γ {Δ} {Δ'} Δ=Δ' k | yes p with (nbOpListFor Γ + nbOpListFor Δ') ≡? k
  ListExchangeRKeepNbSeqCompl G Γ {Δ} {Δ'} Δ=Δ' k | yes p | yes p₁ = 
    refl
  ListExchangeRKeepNbSeqCompl G Γ {Δ} {Δ'} Δ=Δ' k | yes p | no ¬p =
    ⊥-elim (¬p (trans (cong (λ x -> nbOpListFor Γ + x) (ListExchangeKeepOp (ListExchangeSym Δ=Δ'))) p))
  ListExchangeRKeepNbSeqCompl G Γ {Δ} {Δ'} Δ=Δ' k | no ¬p with (nbOpListFor Γ + nbOpListFor Δ') ≡? k
  ListExchangeRKeepNbSeqCompl G Γ {Δ} {Δ'} Δ=Δ' k | no ¬p | yes p =
    ⊥-elim (¬p (trans (cong (λ x -> nbOpListFor Γ + x) (ListExchangeKeepOp Δ=Δ')) p))
  ListExchangeRKeepNbSeqCompl G Γ {Δ} {Δ'} Δ=Δ' k | no ¬p | no ¬p₁ =
    refl
--}}}

  ListExchangeRKeepComplexity :
    (G : HSeq) ->
    (Γ : ListTerm) ->
    (Δ Δ' : ListTerm) ->
    (Δ=Δ' : ListExchange Δ Δ') ->
    complexity (G ∣ (Γ , Δ)) ≡ complexity (G ∣ (Γ , Δ'))
--{{{
  ListExchangeRKeepComplexity G Γ Δ Δ' Δ=Δ' =
    begin
      (maxOp (G ∣ (Γ , Δ)) , nbSeqCompl (G ∣ (Γ , Δ)) (maxOp (G ∣ (Γ , Δ))))
        ≡⟨ cong (λ x -> (x , nbSeqCompl (G ∣ (Γ , Δ)) x)) (ListExchangeRKeepMaxOp G Γ Δ=Δ') ⟩
      (maxOp (G ∣ (Γ , Δ')) , nbSeqCompl (G ∣ (Γ , Δ)) (maxOp (G ∣ (Γ , Δ'))))
        ≡⟨ cong (λ x -> maxOp (G ∣ (Γ , Δ')) , x) (ListExchangeRKeepNbSeqCompl G Γ Δ=Δ' (maxOp (G ∣ (Γ , Δ')))) ⟩
      (maxOp (G ∣ (Γ , Δ')) , nbSeqCompl (G ∣ (Γ , Δ')) (maxOp (G ∣ (Γ , Δ')))) ∎
--}}}

  complexityHead :
    (H : Seq) ->
    complexity (head H) ≡ (nbOpSeq H , 1)
--{{{
  complexityHead H with nbOpSeq H ≡? maxOp (head H)
  complexityHead H | yes p =
    refl
  complexityHead H | no ¬p =
    ⊥-elim (¬p refl)
--}}}

  cong-<L-r :
    {p p' p'' : ℕ × ℕ} ->
    (p=p' : p ≡ p') ->
    (p''<p : p'' <L p) ->
    p'' <L p'
--{{{
  cong-<L-r refl p''<p = p''<p
--}}}

  cong-<L-l :
    {p p' p'' : ℕ × ℕ} ->
    (p=p' : p ≡ p') ->
    (p<p'' : p <L p'') ->
    p' <L p''
--{{{
  cong-<L-l refl p<p'' = p<p''
--}}}

  complexityDecreasing :
    (G : HSeq) ->
    (H H' : Seq) ->
    nbOpSeq H < nbOpSeq H' ->
    maxOp G ≤ nbOpSeq H' ->
    complexity (G ∣ H) <L complexity (G ∣ H')
--{{{
  complexityDecreasing G H H' cH<cH' x with nbOpSeq H ≡? maxOp (G ∣ H)
  complexityDecreasing G H H' cH<cH' x | yes p with nbOpSeq H' ≡? maxOp (G ∣ H')
  complexityDecreasing G H H' cH<cH' x | yes p | yes p₁ =
    first (cong-≤-l (cong suc p) (cong-≤-r p₁ cH<cH'))
  complexityDecreasing G H H' cH<cH' x | yes p | no ¬p =
    ⊥-elim (¬p (sym (k≤k'=>k⊔k'=k' {maxOp G} {nbOpSeq H'} x)))
  complexityDecreasing G H H' cH<cH' x | no ¬p with nbOpSeq H' ≡? maxOp (G ∣ H')
  complexityDecreasing G H H' cH<cH' x | no ¬p | yes p with nbOpSeq H' ≡? maxOp G
  complexityDecreasing G H H' cH<cH' x | no ¬p | yes p | yes p₁ = 
    cong-<L-l
      {maxOp G , nbSeqCompl G (maxOp G)}
      (cong
        (λ x -> x , nbSeqCompl G x)
        (sym
          (trans
          (⊔-comm (maxOp G) (nbOpSeq H))
          (¬a⊔b=a=>a⊔b=b
            {nbOpSeq H}
            {maxOp G}
            (λ x₁ → ¬p (sym (trans (⊔-comm (maxOp G) (nbOpSeq H)) x₁)))))))
      (cong-<L-r
        {maxOp G , suc (nbSeqCompl G (maxOp G))}
        (cong
          (λ x -> x , suc (nbSeqCompl G x))
          (trans (sym p₁) p))
        (second ≤-refl))
  complexityDecreasing G H H' cH<cH' x | no ¬p | yes p | no ¬p₁ =
    first
      (cong-≤-l
        {suc (maxOp G)}
        (cong suc (sym (trans (⊔-comm (maxOp G) (nbOpSeq H)) (¬a⊔b=a=>a⊔b=b (λ x₁ → ¬p (sym (trans (⊔-comm (maxOp G) (nbOpSeq H)) x₁)))))))
        (cong-≤-r
          {nbOpSeq H'}
          p
          (a≤b=>¬a=b=>a<b x (λ x₁ → ¬p₁ (sym x₁)))))
  complexityDecreasing G H H' cH<cH' x | no ¬p | no ¬p₁ =
    ⊥-elim (¬p₁ (sym (k≤k'=>k⊔k'=k' {maxOp G} {nbOpSeq H'} x)))
--}}}

  unfoldNbSeqComplIfP :
    (G : HSeq) ->
    (H : Seq) ->
    (k : ℕ) ->
    nbOpSeq H ≡ k ->
    nbSeqCompl (G ∣ H) k ≡ suc (nbSeqCompl G k)
--{{{
  unfoldNbSeqComplIfP G H k p with nbOpSeq H ≡? k
  unfoldNbSeqComplIfP G H k p | yes p₁ =
    refl
  unfoldNbSeqComplIfP G H k p | no ¬p =
    ⊥-elim (¬p p)
--}}}

  unfoldNbSeqComplIf¬P :
    (G : HSeq) ->
    (H : Seq) ->
    (k : ℕ) ->
    ¬ (nbOpSeq H ≡ k) ->
    nbSeqCompl (G ∣ H) k ≡ (nbSeqCompl G k)
--{{{
  unfoldNbSeqComplIf¬P G H k ¬p with nbOpSeq H ≡? k
  unfoldNbSeqComplIf¬P G H k ¬p | yes p =
    ⊥-elim (¬p p)
  unfoldNbSeqComplIf¬P G H k ¬p | no ¬p' =
    refl
--}}}

  complexityDecMaxR :
    (G : HSeq) ->
    (T D : ListTerm) ->
    (A B : Term) ->
    maxOp G ≤ nbOpSeq (T , D ∷ (A ⊔S B)) ->
    complexity (G ∣ (T , D ∷ A) ∣ (T , D ∷ B)) <L complexity (G ∣ (T , D ∷ (A ⊔S B)))
--{{{
  complexityDecMaxR G T D A B maxOpG≤Seq with maxOp G ≡? nbOpSeq (T , D ∷ (A ⊔S B))
  complexityDecMaxR G T D A B maxOpG≤Seq | yes p =
    cong-<L-l
      {maxOp G , nbSeqCompl (G ∣ (T , D ∷ A) ∣ (T , (D ∷ B))) (maxOp G)}
      (cong
        (λ x -> x , nbSeqCompl (G ∣ (T , D ∷ A) ∣ (T , (D ∷ B))) x)
        {maxOp G}
        {maxOp G ⊔ (nbOpListFor T + (nbOpFor A + nbOpListFor D)) ⊔ (nbOpListFor T + (nbOpFor B + nbOpListFor D))}
        (sym
          (begin
            maxOp G ⊔ (nbOpListFor T + (nbOpFor A + nbOpListFor D)) ⊔ (nbOpListFor T + (nbOpFor B + nbOpListFor D))
              ≡⟨ cong
                   (λ x -> x ⊔ (nbOpListFor T + (nbOpFor B + nbOpListFor D)))
                   {maxOp G ⊔ (nbOpListFor T + (nbOpFor A + nbOpListFor D))}
                   {maxOp G}
                   (trans
                     (⊔-comm (maxOp G) (nbOpListFor T + (nbOpFor A + nbOpListFor D)))
                     (k≤k'=>k⊔k'=k'
                       {nbOpListFor T + (nbOpFor A + nbOpListFor D)}
                       {maxOp G}
                       (cong-≤-r
                         (sym p)
                         (cong-≤-r
                           {suc (nbOpListFor T + (nbOpFor A + nbOpFor B + nbOpListFor D))}
                           (sa+b=a+sb {nbOpListFor T} {nbOpFor A + nbOpFor B + nbOpListFor D})
                           (≤-trans
                             (a≤b=>c≤d=>a+c≤b+d
                               {nbOpListFor T}
                               {nbOpListFor T}
                               {nbOpFor A + nbOpListFor D}
                               {nbOpFor A + nbOpFor B + nbOpListFor D}
                               ≤-refl
                               (a≤b=>c≤d=>a+c≤b+d
                                 {nbOpFor A}
                                 {nbOpFor A + nbOpFor B}
                                 {nbOpListFor D}
                                 {nbOpListFor D}
                                 a≤a+b
                                 ≤-refl))
                             k≤sk))))) ⟩
            maxOp G ⊔ (nbOpListFor T + (nbOpFor B + nbOpListFor D))
              ≡⟨ trans
                     (⊔-comm (maxOp G) (nbOpListFor T + (nbOpFor B + nbOpListFor D)))
                     (k≤k'=>k⊔k'=k'
                       {nbOpListFor T + (nbOpFor B + nbOpListFor D)}
                       {maxOp G}
                       (cong-≤-r
                         (sym p)
                         (cong-≤-r
                           {suc (nbOpListFor T + (nbOpFor A + nbOpFor B + nbOpListFor D))}
                           (sa+b=a+sb {nbOpListFor T} {nbOpFor A + nbOpFor B + nbOpListFor D})
                           (≤-trans
                             (a≤b=>c≤d=>a+c≤b+d
                               {nbOpListFor T}
                               {nbOpListFor T}
                               {nbOpFor B + nbOpListFor D}
                               {nbOpFor A + nbOpFor B + nbOpListFor D}
                               ≤-refl
                               (a≤b=>c≤d=>a+c≤b+d
                                 {nbOpFor B}
                                 {nbOpFor A + nbOpFor B}
                                 {nbOpListFor D}
                                 {nbOpListFor D}
                                 (cong-≤-r
                                   (+-comm (nbOpFor B) (nbOpFor A))
                                   a≤a+b)
                                 ≤-refl))
                             k≤sk)))) ⟩
            maxOp G ∎)))
      (cong-<L-r
        {maxOp G , nbSeqCompl (G ∣ (T , (D ∷ (A ⊔S B)))) (maxOp G)}
        (cong
          (λ x -> x , nbSeqCompl (G ∣ (T , D ∷ (A ⊔S B))) x)
          {maxOp G}
          {maxOp G ⊔ (nbOpListFor T + suc (nbOpFor A + nbOpFor B + nbOpListFor D))}
          (sym
            (trans
              (k≤k'=>k⊔k'=k' maxOpG≤Seq)
              (sym p))))
        (second
          (cong-≤-r
            {suc (nbSeqCompl G (maxOp G))}
            (sym
              (unfoldNbSeqComplIfP
                G
                (T , (D ∷ (A ⊔S B)))
                (maxOp G)
                (sym p)))
            (cong-≤-l
              (cong
                suc
                  (sym
                    (trans
                      (unfoldNbSeqComplIf¬P
                        (G ∣ (T , D ∷ A))
                        (T , D ∷ B)
                        (maxOp G)
                        (k<k'=>¬k=k'
                          {nbOpListFor T + (nbOpFor B + nbOpListFor D)}
                          {maxOp G}
                          (cong-≤-r
                            (sym p)
                            (cong-≤-r
                              {suc (nbOpListFor T + (nbOpFor A + nbOpFor B + nbOpListFor D))}
                              (sa+b=a+sb {nbOpListFor T} {nbOpFor A + nbOpFor B + nbOpListFor D})
                              (s≤s
                                (a≤b=>c≤d=>a+c≤b+d
                                  {nbOpListFor T}
                                  {nbOpListFor T}
                                  {nbOpFor B + nbOpListFor D}
                                  {nbOpFor A + nbOpFor B + nbOpListFor D}
                                  ≤-refl
                                  (a≤b=>c≤d=>a+c≤b+d
                                    {nbOpFor B}
                                    {nbOpFor A + nbOpFor B}
                                    {nbOpListFor D}
                                    {nbOpListFor D}
                                    (cong-≤-r
                                      (+-comm (nbOpFor B) (nbOpFor A))
                                      a≤a+b)
                                    ≤-refl)))))))
                      (unfoldNbSeqComplIf¬P
                        G
                        (T , D ∷ A)
                        (maxOp G)
                        (k<k'=>¬k=k'
                          {nbOpListFor T + (nbOpFor A + nbOpListFor D)}
                          {maxOp G}
                          (cong-≤-r
                            (sym p)
                            (cong-≤-r
                              {suc (nbOpListFor T + (nbOpFor A + nbOpFor B + nbOpListFor D))}
                              (sa+b=a+sb {nbOpListFor T} {nbOpFor A + nbOpFor B + nbOpListFor D})
                              (s≤s
                                (a≤b=>c≤d=>a+c≤b+d
                                  {nbOpListFor T}
                                  {nbOpListFor T}
                                  {nbOpFor A + nbOpListFor D}
                                  {nbOpFor A + nbOpFor B + nbOpListFor D}
                                  ≤-refl
                                  (a≤b=>c≤d=>a+c≤b+d
                                    {nbOpFor A}
                                    {nbOpFor A + nbOpFor B}
                                    {nbOpListFor D}
                                    {nbOpListFor D}
                                    a≤a+b
                                    ≤-refl))))))))))
              ≤-refl))))
  complexityDecMaxR G T D A B maxOpG≤Seq | no ¬p =
    first
      (cong-≤-r
        {nbOpSeq (T , D ∷ (A ⊔S B))}
        (sym
          (k≤k'=>k⊔k'=k'
            maxOpG≤Seq))
        (cong-≤-l
          {suc (maxOp G) ⊔ ((suc (nbOpListFor T + (nbOpFor A + nbOpListFor D))) ⊔ (suc (nbOpListFor T + (nbOpFor B + nbOpListFor D))))}
          (sym
            (cong
              suc
              (⊔-assoc (maxOp G) (nbOpListFor T + (nbOpFor A + nbOpListFor D)) (nbOpListFor T + (nbOpFor B + nbOpListFor D)))))
          (⊔-≤
            {suc (maxOp G)}
            {suc (nbOpListFor T + (nbOpFor A + nbOpListFor D) ⊔ (nbOpListFor T + (nbOpFor B + nbOpListFor D)))}
            {nbOpListFor T + suc (nbOpFor A + nbOpFor B + nbOpListFor D)}
            (a≤b=>¬a=b=>a<b maxOpG≤Seq ¬p)
            (cong-≤-r
              (sa+b=a+sb {nbOpListFor T} {nbOpFor A + nbOpFor B + nbOpListFor D})
              (s≤s
                (⊔-≤
                  {nbOpListFor T + (nbOpFor A + nbOpListFor D)}
                  {nbOpListFor T + (nbOpFor B + nbOpListFor D)}
                  {nbOpListFor T + (nbOpFor A + nbOpFor B + nbOpListFor D)}
                  (a≤b=>c≤d=>a+c≤b+d
                    {nbOpListFor T}
                    {nbOpListFor T}
                    {nbOpFor A + nbOpListFor D}
                    {nbOpFor A + nbOpFor B + nbOpListFor D}
                    ≤-refl
                    (a≤b=>c≤d=>a+c≤b+d
                      {nbOpFor A}
                      {nbOpFor A + nbOpFor B}
                      {nbOpListFor D}
                      {nbOpListFor D}
                      a≤a+b
                      ≤-refl))
                  (a≤b=>c≤d=>a+c≤b+d
                    {nbOpListFor T}
                    {nbOpListFor T}
                    {nbOpFor B + nbOpListFor D}
                    {nbOpFor A + nbOpFor B + nbOpListFor D}
                    ≤-refl
                    (a≤b=>c≤d=>a+c≤b+d
                      {nbOpFor B}
                      {nbOpFor A + nbOpFor B}
                      {nbOpListFor D}
                      {nbOpListFor D}
                      (cong-≤-r
                        (+-comm (nbOpFor B) (nbOpFor A))
                        a≤a+b)
                      ≤-refl))))))))
--}}}

  complexityDecMinL :
    (G : HSeq) ->
    (T D : ListTerm) ->
    (A B : Term) ->
    maxOp G ≤ nbOpSeq (T ∷ (A ⊓S B) , D) ->
    complexity (G ∣ (T ∷ A , D) ∣ (T ∷ B , D)) <L complexity (G ∣ (T ∷ (A ⊓S B) , D))
--{{{
  complexityDecMinL G T D A B maxOpG≤Seq  with maxOp G ≡? nbOpSeq (T ∷ (A ⊓S B) , D)
  complexityDecMinL G T D A B maxOpG≤Seq | yes p =
    cong-<L-l
      {maxOp G , (nbSeqCompl (G ∣ (T ∷ A , D) ∣ (T ∷ B , D)) (maxOp G))}
      (cong
        (λ x -> x , nbSeqCompl (G ∣ (T ∷ A , D) ∣ (T ∷ B , D)) x)
        {maxOp G}
        {maxOp G ⊔ (nbOpFor A + nbOpListFor T + nbOpListFor D) ⊔ (nbOpFor B + nbOpListFor T + nbOpListFor D)}
        (sym
          (begin
            maxOp G ⊔ (nbOpFor A + nbOpListFor T + nbOpListFor D) ⊔ (nbOpFor B + nbOpListFor T + nbOpListFor D)
              ≡⟨ cong
                   (λ x -> x ⊔ (nbOpFor B + nbOpListFor T + nbOpListFor D))
                   (trans
                     (⊔-comm (maxOp G) (nbOpFor A + nbOpListFor T + nbOpListFor D))
                     (k≤k'=>k⊔k'=k'
                       (cong-≤-r
                         (sym p)
                         (≤-trans
                           (a≤b=>c≤d=>a+c≤b+d
                             {nbOpFor A + nbOpListFor T}
                             {nbOpFor A + nbOpFor B + nbOpListFor T}
                             {nbOpListFor D}
                             {nbOpListFor D}
                             (a≤b=>c≤d=>a+c≤b+d
                               {nbOpFor A}
                               {nbOpFor A + nbOpFor B}
                               {nbOpListFor T}
                               {nbOpListFor T}
                               a≤a+b
                               ≤-refl)
                             ≤-refl)
                           k≤sk)))) ⟩
            maxOp G ⊔ (nbOpFor B + nbOpListFor T + nbOpListFor D)
              ≡⟨ trans
                   (⊔-comm (maxOp G) (nbOpFor B + nbOpListFor T + nbOpListFor D))
                   (k≤k'=>k⊔k'=k'
                     (cong-≤-r
                       (sym p)
                       (≤-trans
                         (a≤b=>c≤d=>a+c≤b+d
                           {nbOpFor B + nbOpListFor T}
                           {nbOpFor A + nbOpFor B + nbOpListFor T}
                           {nbOpListFor D}
                           {nbOpListFor D}
                           (a≤b=>c≤d=>a+c≤b+d
                             {nbOpFor B}
                             {nbOpFor A + nbOpFor B}
                             {nbOpListFor T}
                             {nbOpListFor T}
                             (cong-≤-r
                               (+-comm (nbOpFor B) (nbOpFor A))
                               a≤a+b)
                             ≤-refl)
                           ≤-refl)
                         k≤sk))) ⟩
            maxOp G ∎)))
      (cong-<L-r
        {maxOp G , nbSeqCompl (G ∣ (T ∷ (A ⊓S B) , D)) (maxOp G)}
        (cong
          (λ x -> x , nbSeqCompl (G ∣ (T ∷ (A ⊓S B) , D)) x)
          (sym
            (trans
              (k≤k'=>k⊔k'=k'
                maxOpG≤Seq)
              (sym p))))
        (second
          (cong-≤-l
            {suc (nbSeqCompl G (maxOp G))}
            (cong
              suc
              (sym
                (begin
                  nbSeqCompl (G ∣ (T ∷ A , D) ∣ (T ∷ B , D)) (maxOp G)
                    ≡⟨ unfoldNbSeqComplIf¬P
                         (G ∣ ((T ∷ A) , D))
                         (T ∷ B , D)
                         (maxOp G)
                         (k<k'=>¬k=k'
                           {nbOpFor B + nbOpListFor T + nbOpListFor D}
                           {maxOp G}
                           (cong-≤-r
                             (sym p)
                             (s≤s
                               (a≤b=>c≤d=>a+c≤b+d
                                 {nbOpFor B + nbOpListFor T}
                                 {nbOpFor A + nbOpFor B + nbOpListFor T}
                                 {nbOpListFor D}
                                 {nbOpListFor D}
                                   (a≤b=>c≤d=>a+c≤b+d
                                     {nbOpFor B}
                                     {nbOpFor A + nbOpFor B}
                                     {nbOpListFor T}
                                     {nbOpListFor T}
                                     (cong-≤-r
                                       (+-comm (nbOpFor B) (nbOpFor A))
                                       a≤a+b)
                                     ≤-refl)
                                   ≤-refl)))) ⟩
                  nbSeqCompl (G ∣ (T ∷ A , D)) (maxOp G)
                    ≡⟨ unfoldNbSeqComplIf¬P
                         G
                         (T ∷ A , D)
                         (maxOp G)
                         (k<k'=>¬k=k'
                           {nbOpFor A + nbOpListFor T + nbOpListFor D}
                           {maxOp G}
                           (cong-≤-r
                             (sym p)
                             (s≤s
                               (a≤b=>c≤d=>a+c≤b+d
                                 {nbOpFor A + nbOpListFor T}
                                 {nbOpFor A + nbOpFor B + nbOpListFor T}
                                 {nbOpListFor D}
                                 {nbOpListFor D}
                                   (a≤b=>c≤d=>a+c≤b+d
                                     {nbOpFor A}
                                     {nbOpFor A + nbOpFor B}
                                     {nbOpListFor T}
                                     {nbOpListFor T}
                                     a≤a+b
                                     ≤-refl)
                                   ≤-refl)))) ⟩
                  nbSeqCompl G (maxOp G) ∎)))
            (cong-≤-r
              (sym
                (unfoldNbSeqComplIfP
                  G
                  (T ∷ (A ⊓S B) , D)
                  (maxOp G)
                  (sym p)))
              ≤-refl))))
  complexityDecMinL G T D A B maxOpG≤Seq | no ¬p =
    first
      (cong-≤-r
        {suc (nbOpFor A + nbOpFor B + nbOpListFor T + nbOpListFor D)}
        (sym
          (k≤k'=>k⊔k'=k'
            maxOpG≤Seq))
        (⊔-≤
          {suc (maxOp G ⊔ (nbOpFor A + nbOpListFor T + nbOpListFor D))}
          {suc (nbOpFor B + nbOpListFor T + nbOpListFor D)}
          {suc (nbOpFor A + nbOpFor B + nbOpListFor T + nbOpListFor D)}
          (⊔-≤
            {suc (maxOp G)}
            {suc (nbOpFor A + nbOpListFor T + nbOpListFor D)}
            {suc (nbOpFor A + nbOpFor B + nbOpListFor T + nbOpListFor D)}
            (a≤b=>¬a=b=>a<b
              maxOpG≤Seq
              ¬p)
            (s≤s
              (a≤b=>c≤d=>a+c≤b+d
                {nbOpFor A + nbOpListFor T}
                {nbOpFor A + nbOpFor B + nbOpListFor T}
                {nbOpListFor D}
                {nbOpListFor D}
                (a≤b=>c≤d=>a+c≤b+d
                  {nbOpFor A}
                  {nbOpFor A + nbOpFor B}
                  {nbOpListFor T}
                  {nbOpListFor T}
                  a≤a+b
                  ≤-refl)
                ≤-refl)))
          (s≤s
              (a≤b=>c≤d=>a+c≤b+d
                {nbOpFor B + nbOpListFor T}
                {nbOpFor A + nbOpFor B + nbOpListFor T}
                {nbOpListFor D}
                {nbOpListFor D}
                (a≤b=>c≤d=>a+c≤b+d
                  {nbOpFor B}
                  {nbOpFor A + nbOpFor B}
                  {nbOpListFor T}
                  {nbOpListFor T}
                  (cong-≤-r
                    (+-comm (nbOpFor B) (nbOpFor A))
                    a≤a+b)
                  ≤-refl)
                ≤-refl))))
--}}}
