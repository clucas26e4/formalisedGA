module Syntax.Preproof.Create where
  {- STDLIB -}
  open import Nat
  open import Equality
  open import Data.Empty
  open import Data.Product
  open import Relation.Nullary
  open import Induction.WellFounded

  {- Syntax -}
  open import Syntax.Term
  open import Syntax.ListTerm
  open import Syntax.ListTerm.Properties
  open import Syntax.Seq
  open import Syntax.HSeq
  open import Syntax.HSeq.Ordered
  open import Syntax.HSeq.Complexity
  open import Syntax.HSeqList
  open import Syntax.Preproof
  open import Syntax.Preproof.Leaf
  open import Syntax.Proof

  {- Semantic -}

  createPreproofFun :
    {G : HSeq} ->
    (OG : OrderedHSeq G) ->
    Acc _<L_ (complexity G)->
    Preproof G
--{{{
  createPreproofFun {G} OG (acc rs) with complexity G | inspect complexity G
  createPreproofFun {head (T , D)} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] with (nbOpListFor T + nbOpListFor D) ≡? (nbOpListFor T + nbOpListFor D)
  createPreproofFun {head (T , D)} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p with nbOpListFor T | inspect nbOpListFor T
  createPreproofFun {head (T , D)} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] with nbOpListFor D | inspect nbOpListFor D
  createPreproofFun {head (T , D)} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | zero | [ eq₂ ] =
    leaf (head (T , D))
  createPreproofFun {head (T , [])} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] =
    ⊥-elim (notSucEqZero (sym eq₂))
  createPreproofFun {head (T , (D ∷ A))} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] with ListDoExchange (D ∷ A) | inspect ListDoExchange (D ∷ A)
  createPreproofFun {head (T , (D ∷ A))} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] | [] | [ eq₃ ] =
    ⊥-elim (¬ListDoExchangeΓ∷A=[] D A eq₃)
  createPreproofFun {head (T , (D ∷ A))} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] | Δ ∷ varAG x | [ eq₃ ] =
    ⊥-elim (ListDoExchangeNoVar {D ∷ A} (λ x₁ → notSucEqZero (trans (sym eq₂) x₁)) Δ x eq₃)
  createPreproofFun {head (T , (D ∷ A))} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] | Δ ∷ botAG | [ eq₃ ] =
    Preseq-exchange-head
      T
      T
      (Δ ∷ botAG)
      (D ∷ A)
      idLE
      (ListExchangeCong
        eq₃
        (ListExchangeSym ListDoExchangeCorrect))
      (PreZ-R-head
        T
        Δ
        (createPreproofFun
          {head (T , Δ)}
          (HeadOrdered (T , Δ))
          (rs
            (complexity (head (T , Δ)))
            (cong-<L-r
              {complexity (head (T , Δ ∷ botAG))}
              (begin
                complexity (head (T , (Δ ∷ botAG)))
                  ≡⟨ complexityHead (T , Δ ∷ botAG) ⟩
                (nbOpSeq (T , Δ ∷ botAG) , 1)
                  ≡⟨ cong
                       (λ x -> (nbOpListFor T + x , 1))
                       (ListExchangeKeepOperator
                         {Δ ∷ botAG}
                         {D ∷ A}
                         (ListExchangeCong
                           eq₃
                           (ListExchangeSym ListDoExchangeCorrect))) ⟩
                (nbOpSeq (T , (D ∷ A)) , 1)
                  ≡⟨ cong
                       (λ x -> (x + nbOpListFor (D ∷ A) , 1))
                       eq₁ ⟩
                (nbOpListFor (D ∷ A) , 1)
                  ≡⟨ cong
                       (λ x -> (x , 1))
                       eq₂ ⟩
                (suc nbOpD , 1)
                  ≡⟨ eq ⟩
                (maxOpG , nbMaxOp) ∎)
              (first
                (cong-≤-r
                  (sa+b=a+sb {nbOpListFor T} {nbOpListFor Δ})
                  ≤-refl))))))
  createPreproofFun {head (T , (D ∷ A))} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] | Δ ∷ (A₁ ⊔S A₂) | [ eq₃ ] =
    Preseq-exchange-head
      T
      T
      (Δ ∷ (A₁ ⊔S A₂))
      (D ∷ A)
      idLE
      (ListExchangeCong
        eq₃
        (ListExchangeSym ListDoExchangeCorrect))
      (Premax-R-head
        T
        Δ
        A₁
        A₂
        (Prehseq-exchange
          (insert (head (T , (Δ ∷ A₁))) (T , Δ ∷ A₂))
          (head (T , Δ ∷ A₁) ∣ (T , Δ ∷ A₂))
          (HSeqExchangeSym
            (insertDoExchange
              (head (T , Δ ∷ A₁))
              (T , Δ ∷ A₂)))
          (createPreproofFun
            {insert (head (T , Δ ∷ A₁)) (T , Δ ∷ A₂)}
            (insertKeepOrder
              {head (T , Δ ∷ A₁)}
              {T , Δ ∷ A₂}
              (HeadOrdered (T , Δ ∷ A₁)))
            (rs
              (complexity (insert (head (T , Δ ∷ A₁)) (T , Δ ∷ A₂)))
              (cong-<L-l
                {complexity (head (T , Δ ∷ A₁) ∣ (T , Δ ∷ A₂))}
                (ExchangeKeepComplexity
                  {head (T , (Δ ∷ A₁)) ∣ (T , (Δ ∷ A₂))}
                  {insert (head (T , Δ ∷ A₁)) (T , Δ ∷ A₂)}
                  (insertDoExchange
                    (head (T , Δ ∷ A₁))
                    (T , Δ ∷ A₂)))
                (cong-<L-r
                  {complexity (head (T , Δ ∷ (A₁ ⊔S A₂)))}
                  (begin
                    complexity (head (T , (Δ ∷ (A₁ ⊔S A₂))))
                      ≡⟨ complexityHead (T , Δ ∷ (A₁ ⊔S A₂)) ⟩
                    (nbOpSeq (T , (Δ ∷ (A₁ ⊔S A₂))) , 1)
                      ≡⟨ cong
                           (λ x -> (x + nbOpListFor (Δ ∷ (A₁ ⊔S A₂)) , 1))
                           eq₁ ⟩
                    nbOpListFor (Δ ∷ (A₁ ⊔S A₂)) , 1
                      ≡⟨ cong
                           (λ x -> x , 1)
                           (ListExchangeKeepOperator
                             {Δ ∷ (A₁ ⊔S A₂)}
                             {D ∷ A}
                             (ListExchangeCong
                               eq₃
                               (ListExchangeSym ListDoExchangeCorrect))) ⟩
                    nbOpListFor (D ∷ A) , 1
                      ≡⟨ cong
                           (λ x -> x , 1)
                           eq₂ ⟩
                    suc nbOpD , 1
                      ≡⟨ eq ⟩
                    maxOpG , nbMaxOp ∎)
                  (first
                    (⊔-≤
                      {suc (nbOpListFor T + (nbOpFor A₁ + nbOpListFor Δ))}
                      {suc (nbOpListFor T + (nbOpFor A₂ + nbOpListFor Δ))}
                      {nbOpListFor T + suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ)}
                      (cong-≤-l
                        {suc (nbOpFor A₁ + nbOpListFor Δ)}
                        (cong
                          (λ x -> suc (x + (nbOpFor A₁ + nbOpListFor Δ)))
                          (sym eq₁))
                        (cong-≤-r
                          {suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ)}
                          (cong
                            (λ x -> x + suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ))
                            (sym eq₁))
                          (s≤s
                            (cong-≤-r
                              {nbOpFor A₁ + nbOpListFor Δ + nbOpFor A₂}
                              (begin
                                nbOpFor A₁ + nbOpListFor Δ + nbOpFor A₂
                                  ≡⟨ +-assoc (nbOpFor A₁) (nbOpListFor Δ) (nbOpFor A₂) ⟩
                                nbOpFor A₁ + (nbOpListFor Δ + nbOpFor A₂)
                                  ≡⟨ cong
                                       (λ x -> nbOpFor A₁ + x)
                                       (+-comm (nbOpListFor Δ) (nbOpFor A₂)) ⟩
                                nbOpFor A₁ + (nbOpFor A₂ + nbOpListFor Δ)
                                  ≡⟨ sym (+-assoc (nbOpFor A₁) (nbOpFor A₂) (nbOpListFor Δ)) ⟩
                                nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ ∎)
                              a≤a+b))))
                      ((cong-≤-l
                        {suc (nbOpFor A₂ + nbOpListFor Δ)}
                        (cong
                          (λ x -> suc (x + (nbOpFor A₂ + nbOpListFor Δ)))
                          (sym eq₁))
                        (cong-≤-r
                          {suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ)}
                          (cong
                            (λ x -> x + suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ))
                            (sym eq₁))
                          (s≤s
                            (cong-≤-r
                              {nbOpFor A₂ + nbOpListFor Δ + nbOpFor A₁}
                              (begin
                                nbOpFor A₂ + nbOpListFor Δ + nbOpFor A₁
                                  ≡⟨ +-comm (nbOpFor A₂ + nbOpListFor Δ) (nbOpFor A₁) ⟩
                                nbOpFor A₁ + (nbOpFor A₂ + nbOpListFor Δ)
                                  ≡⟨ sym (+-assoc (nbOpFor A₁) (nbOpFor A₂) (nbOpListFor Δ)) ⟩
                                nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ ∎)
                              a≤a+b)))))))))))))
  createPreproofFun {head (T , (D ∷ A))} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] | Δ ∷ (A₁ +S A₂) | [ eq₃ ] =
    Preseq-exchange-head
      T
      T
      (Δ ∷ (A₁ +S A₂))
      (D ∷ A)
      idLE
      (ListExchangeCong
        eq₃
        (ListExchangeSym ListDoExchangeCorrect))
      (Preplus-R-head
        T
        Δ
        A₁
        A₂
        (createPreproofFun
          {head (T , (Δ ∷ A₁ ∷ A₂))}
          (HeadOrdered (T , (Δ ∷ A₁ ∷ A₂)))
          (rs
            (complexity (head (T , (Δ ∷ A₁ ∷ A₂))))
            (cong-<L-r
              {complexity (head (T , (Δ ∷ (A₁ +S A₂))))}
              (begin
                complexity (head (T , (Δ ∷ (A₁ +S A₂))))
                  ≡⟨ complexityHead (T , Δ ∷ (A₁ +S A₂)) ⟩
                (nbOpSeq (T , (Δ ∷ (A₁ +S A₂))) , 1)
                  ≡⟨ cong
                       (λ x -> (x + nbOpListFor (Δ ∷ (A₁ +S A₂)) , 1))
                       eq₁ ⟩
                (nbOpListFor (Δ ∷ (A₁ +S A₂)) , 1)
                  ≡⟨ cong
                       (λ x -> (x , 1))
                       (ListExchangeKeepOperator
                         {Δ ∷ (A₁ +S A₂)}
                         {D ∷ A}
                         (ListExchangeCong
                           eq₃
                           (ListExchangeSym ListDoExchangeCorrect))) ⟩
                (nbOpListFor (D ∷ A) , 1)
                  ≡⟨ cong
                       (λ x -> x , 1)
                       eq₂ ⟩
                (suc nbOpD , 1)
                  ≡⟨ eq ⟩
                (maxOpG , nbMaxOp) ∎)
              (first
                (cong-≤-r
                  {suc (nbOpListFor T + nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ)}
                  (trans
                    (cong
                      suc
                      (sym
                        (trans
                          (sym (+-assoc (nbOpListFor T) (nbOpFor A₁ + nbOpFor A₂) (nbOpListFor Δ)))
                          (cong
                            (λ x -> (x + nbOpListFor Δ))
                            (sym (+-assoc (nbOpListFor T) (nbOpFor A₁) (nbOpFor A₂)))))))
                    (sa+b=a+sb {nbOpListFor T} {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ}))
                  (s≤s
                    (cong-≤-r
                      {nbOpListFor T + (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ)}
                      (trans
                        (sym
                          (+-assoc (nbOpListFor T) (nbOpFor A₁ + nbOpFor A₂) (nbOpListFor Δ)))
                        (sym
                          (cong
                            (λ x -> x + nbOpListFor Δ)
                            (+-assoc (nbOpListFor T) (nbOpFor A₁) (nbOpFor A₂)))))
                      (a≤b=>c≤d=>a+c≤b+d
                        {nbOpListFor T}
                        {nbOpListFor T}
                        {(nbOpFor A₂ + (nbOpFor A₁ + nbOpListFor Δ))}
                        {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ}
                        ≤-refl
                        (cong-≤-r
                          (trans
                            (sym
                              (+-assoc (nbOpFor A₂) (nbOpFor A₁) (nbOpListFor Δ)))
                            (cong
                              (λ x -> (x + nbOpListFor Δ))
                              (+-comm (nbOpFor A₂) (nbOpFor A₁))))
                          ≤-refl))))))))))
  createPreproofFun {head (T , (D ∷ A))} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] | Δ ∷ (A₁ ⊓S A₂) | [ eq₃ ] =
    Preseq-exchange-head
      T
      T
      (Δ ∷ (A₁ ⊓S A₂))
      (D ∷ A)
      idLE
      (ListExchangeCong
        eq₃
        (ListExchangeSym ListDoExchangeCorrect))
      (Premin-R-head
        T
        Δ
        A₁
        A₂
        (createPreproofFun
          {head (T , (Δ ∷ A₁))}
          (HeadOrdered (T , Δ ∷ A₁))
          (rs
           (complexity (head (T , (Δ ∷ A₁))))
           (cong-<L-r
             {complexity (head (T , (Δ ∷ (A₁ ⊓S A₂))))}
             (begin
                    complexity (head (T , (Δ ∷ (A₁ ⊓S A₂))))
                      ≡⟨ complexityHead (T , Δ ∷ (A₁ ⊓S A₂)) ⟩
                    (nbOpSeq (T , (Δ ∷ (A₁ ⊓S A₂))) , 1)
                      ≡⟨ cong
                           (λ x -> (x + nbOpListFor (Δ ∷ (A₁ ⊓S A₂)) , 1))
                           eq₁ ⟩
                    nbOpListFor (Δ ∷ (A₁ ⊓S A₂)) , 1
                      ≡⟨ cong
                           (λ x -> x , 1)
                           (ListExchangeKeepOperator
                             {Δ ∷ (A₁ ⊓S A₂)}
                             {D ∷ A}
                             (ListExchangeCong
                               eq₃
                               (ListExchangeSym ListDoExchangeCorrect))) ⟩
                    nbOpListFor (D ∷ A) , 1
                      ≡⟨ cong
                           (λ x -> x , 1)
                           eq₂ ⟩
                    suc nbOpD , 1
                      ≡⟨ eq ⟩
                    maxOpG , nbMaxOp ∎)
             (first
               (cong-≤-l
                        {suc (nbOpFor A₁ + nbOpListFor Δ)}
                        (cong
                          (λ x -> suc (x + (nbOpFor A₁ + nbOpListFor Δ)))
                          (sym eq₁))
                        (cong-≤-r
                          {suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ)}
                          (cong
                            (λ x -> x + suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ))
                            (sym eq₁))
                          (s≤s
                            (cong-≤-r
                              {nbOpFor A₁ + nbOpListFor Δ + nbOpFor A₂}
                              (begin
                                nbOpFor A₁ + nbOpListFor Δ + nbOpFor A₂
                                  ≡⟨ +-assoc (nbOpFor A₁) (nbOpListFor Δ) (nbOpFor A₂) ⟩
                                nbOpFor A₁ + (nbOpListFor Δ + nbOpFor A₂)
                                  ≡⟨ cong
                                       (λ x -> nbOpFor A₁ + x)
                                       (+-comm (nbOpListFor Δ) (nbOpFor A₂)) ⟩
                                nbOpFor A₁ + (nbOpFor A₂ + nbOpListFor Δ)
                                  ≡⟨ sym (+-assoc (nbOpFor A₁) (nbOpFor A₂) (nbOpListFor Δ)) ⟩
                                nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ ∎)
                              a≤a+b))))))))
        (createPreproofFun
          {head (T , Δ ∷ A₂)}
          (HeadOrdered (T , Δ ∷ A₂))
          (rs
            (complexity (head (T , Δ ∷ A₂)))
            (cong-<L-r
              {complexity (head (T , (Δ ∷ (A₁ ⊓S A₂))))}
              (begin
                complexity (head (T , (Δ ∷ (A₁ ⊓S A₂))))
                  ≡⟨ complexityHead (T , Δ ∷ (A₁ ⊓S A₂)) ⟩
                (nbOpSeq (T , (Δ ∷ (A₁ ⊓S A₂))) , 1)
                  ≡⟨ cong
                       (λ x -> (x + nbOpListFor (Δ ∷ (A₁ ⊓S A₂)) , 1))
                       eq₁ ⟩
                nbOpListFor (Δ ∷ (A₁ ⊓S A₂)) , 1
                  ≡⟨ cong
                       (λ x -> x , 1)
                       (ListExchangeKeepOperator
                         {Δ ∷ (A₁ ⊓S A₂)}
                         {D ∷ A}
                         (ListExchangeCong
                           eq₃
                           (ListExchangeSym ListDoExchangeCorrect))) ⟩
                nbOpListFor (D ∷ A) , 1
                  ≡⟨ cong
                       (λ x -> x , 1)
                       eq₂ ⟩
                suc nbOpD , 1
                  ≡⟨ eq ⟩
                maxOpG , nbMaxOp ∎)
                (first
                  (cong-≤-l
                        {suc (nbOpFor A₂ + nbOpListFor Δ)}
                        (cong
                          (λ x -> suc (x + (nbOpFor A₂ + nbOpListFor Δ)))
                          (sym eq₁))
                        (cong-≤-r
                          {suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ)}
                          (cong
                            (λ x -> x + suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ))
                            (sym eq₁))
                          (s≤s
                            (cong-≤-r
                              {nbOpFor A₂ + nbOpListFor Δ + nbOpFor A₁}
                              (begin
                                nbOpFor A₂ + nbOpListFor Δ + nbOpFor A₁
                                  ≡⟨ +-comm (nbOpFor A₂ + nbOpListFor Δ) (nbOpFor A₁) ⟩
                                nbOpFor A₁ + (nbOpFor A₂ + nbOpListFor Δ)
                                  ≡⟨ sym (+-assoc (nbOpFor A₁) (nbOpFor A₂) (nbOpListFor Δ)) ⟩
                                nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ ∎)
                              a≤a+b)))))))))
  createPreproofFun {head (T , (D ∷ A))} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] | Δ ∷ (-S A₁) | [ eq₃ ] =
    Preseq-exchange-head
      T
      T
      (Δ ∷ (-S A₁))
      (D ∷ A)
      idLE
      (ListExchangeCong
        eq₃
        (ListExchangeSym ListDoExchangeCorrect))
      (Preminus-R-head
        T
        Δ
        A₁
        (createPreproofFun
          (HeadOrdered (T ∷ A₁ , Δ))
          (rs
            (complexity (head (T ∷ A₁ , Δ)))
            (cong-<L-r
              {complexity (head (T , (Δ ∷ (-S A₁))))}
              (begin
                complexity (head (T , (Δ ∷ (-S A₁))))
                  ≡⟨ complexityHead (T , Δ ∷ (-S A₁)) ⟩
                (nbOpSeq (T , (Δ ∷ (-S A₁))) , 1)
                  ≡⟨ cong
                       (λ x -> (x + nbOpListFor (Δ ∷ (-S A₁)) , 1))
                       eq₁ ⟩
                nbOpListFor (Δ ∷ (-S A₁)) , 1
                  ≡⟨ cong
                       (λ x -> x , 1)
                       (ListExchangeKeepOperator
                         {Δ ∷ (-S A₁)}
                         {D ∷ A}
                         (ListExchangeCong
                           eq₃
                           (ListExchangeSym ListDoExchangeCorrect))) ⟩
                nbOpListFor (D ∷ A) , 1
                  ≡⟨ cong
                       (λ x -> x , 1)
                       eq₂ ⟩
                suc nbOpD , 1
                  ≡⟨ eq ⟩
                maxOpG , nbMaxOp ∎)
              (first
                (cong-≤-l
                  {suc (nbOpFor A₁ + nbOpListFor Δ)}
                  (cong
                    suc
                    (cong
                      (λ x -> x + nbOpListFor Δ)
                      (trans
                        (cong (λ x -> x + nbOpFor A₁) (sym eq₁))
                        (+-comm (nbOpListFor T) (nbOpFor A₁)))))
                  (cong-≤-r
                    (begin
                      suc (nbOpFor A₁ + nbOpListFor Δ)
                        ≡⟨ cong
                             (λ x -> suc (x + (nbOpFor A₁ + nbOpListFor Δ)))
                             (sym eq₁) ⟩
                      suc (nbOpListFor T + (nbOpFor A₁ + nbOpListFor Δ))
                        ≡⟨ sa+b=a+sb {nbOpListFor T} ⟩
                      nbOpListFor T + suc (nbOpFor A₁ + nbOpListFor Δ) ∎)
                    ≤-refl)))))))
  createPreproofFun {head ([] , D)} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] =
    ⊥-elim (notSucEqZero (sym eq₁))
  createPreproofFun {head ((T ∷ A) , D)} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] with ListDoExchange (T ∷ A) | inspect ListDoExchange (T ∷ A)
  createPreproofFun {head ((T ∷ A) , D)} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] | [] | [ eq₂ ] =
    ⊥-elim (¬ListDoExchangeΓ∷A=[] T A eq₂)
  createPreproofFun {head ((T ∷ A) , D)} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] | Γ ∷ varAG x | [ eq₂ ] =
    ⊥-elim (ListDoExchangeNoVar {T ∷ A} ((λ x → notSucEqZero (trans (sym eq₁) x))) Γ x eq₂)
  createPreproofFun {head ((T ∷ A) , D)} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] | Γ ∷ botAG | [ eq₂ ] =
    Preseq-exchange-head
      (Γ ∷ botAG)
      (T ∷ A)
      D
      D
      (ListExchangeCong
        eq₂
        (ListExchangeSym ListDoExchangeCorrect))
      idLE
      (PreZ-L-head
        Γ
        D
        (createPreproofFun
          (HeadOrdered (Γ , D))
          (rs
            (complexity (head (Γ , D)))
            (cong-<L-r
              {complexity (head (Γ ∷ botAG , D))}
              (begin
                complexity (head ((Γ ∷ botAG) , D))
                  ≡⟨ complexityHead (Γ ∷ botAG , D) ⟩
                nbOpSeq (Γ ∷ botAG , D) , 1
                  ≡⟨ cong
                       (λ x -> (x + nbOpListFor D) , 1)
                       {suc (nbOpListFor Γ)}
                       {nbOpFor A + nbOpListFor T}
                       (ListExchangeKeepOperator
                         {Γ ∷ botAG}
                         {T ∷ A}
                         (ListExchangeCong
                           eq₂
                           (ListExchangeSym ListDoExchangeCorrect))) ⟩
                nbOpSeq ((T ∷ A) , D) , 1
                  ≡⟨ cong
                       (λ x -> (x + nbOpListFor D) , 1)
                       eq₁ ⟩
                (suc nbOpT + nbOpListFor D) , 1
                  ≡⟨ eq ⟩
                maxOpG , nbMaxOp ∎)
              (first
                ≤-refl)))))
  createPreproofFun {head ((T ∷ A) , D)} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] | Γ ∷ (A₁ ⊔S A₂) | [ eq₂ ] =
    Preseq-exchange-head
      (Γ ∷ (A₁ ⊔S A₂))
      (T ∷ A)
      D
      D
      (ListExchangeCong
        eq₂
        (ListExchangeSym ListDoExchangeCorrect))
      idLE
      (Premax-L-head
        Γ
        D
        A₁
        A₂
        (createPreproofFun
          (HeadOrdered (Γ ∷ A₁ , D))
          (rs
            (complexity (head (Γ ∷ A₁ , D)))
            (cong-<L-r
              {complexity (head (Γ ∷ (A₁ ⊔S A₂) , D))}
              (begin
                complexity (head ((Γ ∷ (A₁ ⊔S A₂)) , D))
                  ≡⟨ complexityHead (Γ ∷ (A₁ ⊔S A₂) , D) ⟩
                nbOpSeq (Γ ∷ (A₁ ⊔S A₂) , D) , 1
                  ≡⟨ cong
                       (λ x -> (x + nbOpListFor D) , 1)
                       {suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ)}
                       {nbOpFor A + nbOpListFor T}
                       (ListExchangeKeepOperator
                         {Γ ∷ (A₁ ⊔S A₂)}
                         {T ∷ A}
                         (ListExchangeCong
                           eq₂
                           (ListExchangeSym ListDoExchangeCorrect))) ⟩
                nbOpSeq ((T ∷ A) , D) , 1
                  ≡⟨ cong
                       (λ x -> (x + nbOpListFor D) , 1)
                       eq₁ ⟩
                (suc nbOpT + nbOpListFor D) , 1
                  ≡⟨ eq ⟩
                maxOpG , nbMaxOp ∎)
              (first
                (s≤s
                  (a≤b=>c≤d=>a+c≤b+d
                    {nbOpFor A₁ + nbOpListFor Γ}
                    {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ}
                    {nbOpListFor D}
                    {nbOpListFor D}
                    (a≤b=>c≤d=>a+c≤b+d
                      {nbOpFor A₁}
                      {nbOpFor A₁ + nbOpFor A₂}
                      {nbOpListFor Γ}
                      {nbOpListFor Γ}
                      a≤a+b
                      ≤-refl)
                    ≤-refl))))))
        (createPreproofFun
          (HeadOrdered (Γ ∷ A₂ , D))
          (rs
            (complexity (head (Γ ∷ A₂ , D)))
            (cong-<L-r
              {complexity (head (Γ ∷ (A₁ ⊔S A₂) , D))}
              (begin
                complexity (head ((Γ ∷ (A₁ ⊔S A₂)) , D))
                  ≡⟨ complexityHead (Γ ∷ (A₁ ⊔S A₂) , D) ⟩
                nbOpSeq (Γ ∷ (A₁ ⊔S A₂) , D) , 1
                  ≡⟨ cong
                       (λ x -> (x + nbOpListFor D) , 1)
                       {suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ)}
                       {nbOpFor A + nbOpListFor T}
                       (ListExchangeKeepOperator
                         {Γ ∷ (A₁ ⊔S A₂)}
                         {T ∷ A}
                         (ListExchangeCong
                           eq₂
                           (ListExchangeSym ListDoExchangeCorrect))) ⟩
                nbOpSeq ((T ∷ A) , D) , 1
                  ≡⟨ cong
                       (λ x -> (x + nbOpListFor D) , 1)
                       eq₁ ⟩
                (suc nbOpT + nbOpListFor D) , 1
                  ≡⟨ eq ⟩
                maxOpG , nbMaxOp ∎)
              (first
                (s≤s
                  (a≤b=>c≤d=>a+c≤b+d
                    {nbOpFor A₂ + nbOpListFor Γ}
                    {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ}
                    {nbOpListFor D}
                    {nbOpListFor D}
                    (a≤b=>c≤d=>a+c≤b+d
                      {nbOpFor A₂}
                      {nbOpFor A₁ + nbOpFor A₂}
                      {nbOpListFor Γ}
                      {nbOpListFor Γ}
                      (cong-≤-r
                        (+-comm (nbOpFor A₂) (nbOpFor A₁))
                        a≤a+b)
                      ≤-refl)
                    ≤-refl)))))))
  createPreproofFun {head ((T ∷ A) , D)} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] | Γ ∷ (A₁ +S A₂) | [ eq₂ ] =
    Preseq-exchange-head
      (Γ ∷ (A₁ +S A₂))
      (T ∷ A)
      D
      D
      (ListExchangeCong
        eq₂
        (ListExchangeSym ListDoExchangeCorrect))
      idLE
      (Preplus-L-head
        Γ
        D
        A₁
        A₂
        (createPreproofFun
          {head ((Γ ∷ A₁ ∷ A₂) , D)}
          (HeadOrdered ((Γ ∷ A₁ ∷ A₂) , D))
          (rs
            (complexity (head ((Γ ∷ A₁ ∷ A₂) , D)))
            (cong-<L-r
              {complexity (head (Γ ∷ (A₁ +S A₂) , D))}
              (begin
                complexity (head ((Γ ∷ (A₁ +S A₂)) , D))
                  ≡⟨ complexityHead (Γ ∷ (A₁ +S A₂) , D) ⟩
                nbOpSeq (Γ ∷ (A₁ +S A₂) , D) , 1
                  ≡⟨ cong
                       (λ x -> (x + nbOpListFor D) , 1)
                       {suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ)}
                       {nbOpFor A + nbOpListFor T}
                       (ListExchangeKeepOperator
                         {Γ ∷ (A₁ +S A₂)}
                         {T ∷ A}
                         (ListExchangeCong
                           eq₂
                           (ListExchangeSym ListDoExchangeCorrect))) ⟩
                nbOpSeq ((T ∷ A) , D) , 1
                  ≡⟨ cong
                       (λ x -> (x + nbOpListFor D) , 1)
                       eq₁ ⟩
                (suc nbOpT + nbOpListFor D) , 1
                  ≡⟨ eq ⟩
                maxOpG , nbMaxOp ∎)
              (first
                (a≤b=>c≤d=>a+c≤b+d
                  {suc (nbOpFor A₂ + (nbOpFor A₁ + nbOpListFor Γ))}
                  {suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ)}
                  {nbOpListFor D}
                  {nbOpListFor D}
                  (s≤s
                    (cong-≤-l
                      (begin
                        nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ
                          ≡⟨ cong
                               (λ x -> x + nbOpListFor Γ)
                               (+-comm (nbOpFor A₁) (nbOpFor A₂)) ⟩
                        nbOpFor A₂ + nbOpFor A₁ + nbOpListFor Γ
                          ≡⟨ +-assoc (nbOpFor A₂) (nbOpFor A₁) (nbOpListFor Γ) ⟩
                        nbOpFor A₂ + (nbOpFor A₁ + nbOpListFor Γ) ∎)
                      ≤-refl))
                  ≤-refl))))))
  createPreproofFun {head ((T ∷ A) , D)} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] | Γ ∷ (A₁ ⊓S A₂) | [ eq₂ ] =
    Preseq-exchange-head
      (Γ ∷ (A₁ ⊓S A₂))
      (T ∷ A)
      D
      D
      (ListExchangeCong
        eq₂
        (ListExchangeSym ListDoExchangeCorrect))
      idLE
      (Premin-L-head
        Γ
        D
        A₁
        A₂
        (Prehseq-exchange
          (insert (head ((Γ ∷ A₁) , D)) (Γ ∷ A₂ , D))
          (head (Γ ∷ A₁ , D) ∣ (Γ ∷ A₂ , D))
          (HSeqExchangeSym
            (insertDoExchange
              (head (Γ ∷ A₁ , D))
              (Γ ∷ A₂ , D)))
          (createPreproofFun
            {insert (head (Γ ∷ A₁ , D)) (Γ ∷ A₂ , D)}
            (insertKeepOrder
              {head (Γ ∷ A₁ , D)}
              {(Γ ∷ A₂) , D}
              (HeadOrdered (Γ ∷ A₁ , D)))
            (rs
              (complexity (insert (head (Γ ∷ A₁ , D)) (Γ ∷ A₂ , D)))
              (cong-<L-r
                {complexity (head (Γ ∷ (A₁ ⊓S A₂) , D))}
                (begin
                  complexity (head ((Γ ∷ (A₁ ⊓S A₂)) , D))
                    ≡⟨ complexityHead (Γ ∷ (A₁ ⊓S A₂) , D) ⟩
                  nbOpSeq (Γ ∷ (A₁ ⊓S A₂) , D) , 1
                    ≡⟨ cong
                         (λ x -> (x + nbOpListFor D) , 1)
                         {suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ)}
                         {nbOpFor A + nbOpListFor T}
                         (ListExchangeKeepOperator
                           {Γ ∷ (A₁ ⊓S A₂)}
                           {T ∷ A}
                           (ListExchangeCong
                             eq₂
                             (ListExchangeSym ListDoExchangeCorrect))) ⟩
                  nbOpSeq ((T ∷ A) , D) , 1
                    ≡⟨ cong
                         (λ x -> (x + nbOpListFor D) , 1)
                         eq₁ ⟩
                  (suc nbOpT + nbOpListFor D) , 1
                    ≡⟨ eq ⟩
                  maxOpG , nbMaxOp ∎)
                (cong-<L-l
                  {complexity (head (Γ ∷ A₁ , D) ∣ (Γ ∷ A₂ , D))}
                  (ExchangeKeepComplexity
                    (insertDoExchange
                      (head (Γ ∷ A₁ , D))
                      (Γ ∷ A₂ , D)))
                  (first
                    (s≤s
                      (⊔-≤
                        {nbOpFor A₁ + nbOpListFor Γ + nbOpListFor D}
                        {nbOpFor A₂ + nbOpListFor Γ + nbOpListFor D}
                        {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ + nbOpListFor D}
                        (a≤b=>c≤d=>a+c≤b+d
                          {nbOpFor A₁ + nbOpListFor Γ}
                          {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ}
                          {nbOpListFor D}
                          {nbOpListFor D}
                          (a≤b=>c≤d=>a+c≤b+d
                            {nbOpFor A₁}
                            {nbOpFor A₁ + nbOpFor A₂}
                            {nbOpListFor Γ}
                            {nbOpListFor Γ}
                            a≤a+b
                            ≤-refl)
                          ≤-refl)
                        (a≤b=>c≤d=>a+c≤b+d
                          {nbOpFor A₂ + nbOpListFor Γ}
                          {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ}
                          {nbOpListFor D}
                          {nbOpListFor D}
                          (a≤b=>c≤d=>a+c≤b+d
                            {nbOpFor A₂}
                            {nbOpFor A₁ + nbOpFor A₂}
                            {nbOpListFor Γ}
                            {nbOpListFor Γ}
                            (cong-≤-r
                              (+-comm (nbOpFor A₂) (nbOpFor A₁))
                              a≤a+b)
                            ≤-refl)
                          ≤-refl))))))))))
  createPreproofFun {head ((T ∷ A) , D)} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] | Γ ∷ (-S A₁) | [ eq₂ ] =
    Preseq-exchange-head
      (Γ ∷ (-S A₁))
      (T ∷ A)
      D
      D
      (ListExchangeCong
        eq₂
        (ListExchangeSym ListDoExchangeCorrect))
      idLE
      (Preminus-L-head
        Γ
        D
        A₁
        (createPreproofFun
          (HeadOrdered (Γ , (D ∷ A₁)))
          (rs
            (complexity (head (Γ , (D ∷ A₁))))
            (cong-<L-r
              {complexity (head (Γ ∷ (-S A₁) , D))}
              (begin
                complexity (head ((Γ ∷ (-S A₁)) , D))
                  ≡⟨ complexityHead
                       (Γ ∷ (-S A₁) , D) ⟩
                nbOpSeq (Γ ∷ (-S A₁) , D) , 1
                  ≡⟨ cong
                       (λ x -> (x + nbOpListFor D) , 1)
                       (ListExchangeKeepOperator
                         {Γ ∷ (-S A₁)}
                         {T ∷ A}
                         (ListExchangeCong
                           eq₂
                           (ListExchangeSym ListDoExchangeCorrect))) ⟩
                nbOpSeq (T ∷ A , D) , 1
                  ≡⟨ cong
                       (λ x -> (x + nbOpListFor D) , 1)
                       eq₁ ⟩
                suc nbOpT + nbOpListFor D , 1
                  ≡⟨ eq ⟩
                maxOpG , nbMaxOp ∎)
              (first
                (s≤s
                  (cong-≤-r
                    {nbOpListFor Γ + (nbOpFor A₁ + nbOpListFor D)}
                    (begin
                      nbOpListFor Γ + (nbOpFor A₁ + nbOpListFor D)
                        ≡⟨ sym (+-assoc (nbOpListFor Γ) (nbOpFor A₁) (nbOpListFor D)) ⟩
                      nbOpListFor Γ + nbOpFor A₁ + nbOpListFor D
                        ≡⟨ cong
                             (λ x -> x + nbOpListFor D)
                             (+-comm (nbOpListFor Γ) (nbOpFor A₁)) ⟩
                      nbOpFor A₁ + nbOpListFor Γ + nbOpListFor D ∎)
                    ≤-refl)))))))
  createPreproofFun {head (T , D)} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | no ¬p =
    ⊥-elim (¬p refl)
  createPreproofFun {G ∣ H} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] with nbOpSeq H ≡? (maxOp G ⊔ nbOpSeq H)
  createPreproofFun {G ∣ (T , D)} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p with nbOpListFor T | inspect nbOpListFor T
  createPreproofFun {G ∣ (T , D)} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] with nbOpListFor D | inspect nbOpListFor D
  createPreproofFun {G ∣ (T , D)} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | zero | [ eq₂ ] =
    leaf (G ∣ (T , D))
  createPreproofFun {G ∣ (T , [])} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] =
    ⊥-elim (notSucEqZero (sym eq₂))
  createPreproofFun {G ∣ (T , (D ∷ A))} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ]  with ListDoExchange (D ∷ A) | inspect ListDoExchange (D ∷ A)
  createPreproofFun {G ∣ (T , (D ∷ A))} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] | [] | [ eq₃ ] =
    ⊥-elim (¬ListDoExchangeΓ∷A=[] D A eq₃)
  createPreproofFun {G ∣ (T , (D ∷ A))} (ConsOrdered OG x') (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] | Δ ∷ varAG x | [ eq₃ ] =
    ⊥-elim (ListDoExchangeNoVar {D ∷ A} (λ x₁ → notSucEqZero (trans (sym eq₂) x₁)) Δ x eq₃)
  createPreproofFun {G ∣ (T , (D ∷ A))} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] | Δ ∷ botAG | [ eq₃ ] =
    Preseq-exchange
      G
      T
      T
      (Δ ∷ botAG)
      (D ∷ A)
      idLE
      (ListExchangeCong
        eq₃
        (ListExchangeSym ListDoExchangeCorrect))
      (PreZ-R
        G
        T
        Δ
        (Prehseq-exchange
          (insert G (T , Δ))
          (G ∣ (T , Δ))
          (HSeqExchangeSym
            (insertDoExchange
              G
              (T , Δ)))
          (createPreproofFun
            {insert G (T , Δ)}
            (insertKeepOrder
              OG)
            (rs
              (complexity (insert G (T , Δ)))
              (cong-<L-r
                {complexity (G ∣ (T , Δ ∷ botAG))}
                (begin
                  complexity (G ∣ (T , (Δ ∷ botAG)))
                    ≡⟨ ListExchangeRKeepComplexity
                         G
                         T
                         (Δ ∷ botAG)
                         (D ∷ A)
                         (ListExchangeCong
                           eq₃
                           (ListExchangeSym ListDoExchangeCorrect)) ⟩
                  complexity (G ∣ (T , (D ∷ A)))
                    ≡⟨ unfoldComplexity
                         G
                         (T , (D ∷ A))
                         (cong-≤-r
                           {suc nbOpD}
                           (sym
                             (trans
                               (cong
                                 (λ x -> x + (nbOpFor A + nbOpListFor D))
                                 eq₁)
                               eq₂))
                           x) ⟩
                  (maxOp G ⊔ (nbOpListFor T + (nbOpFor A + nbOpListFor D)), suc (nbSeqCompl G (maxOp G ⊔ (nbOpListFor T + (nbOpFor A + nbOpListFor D)))))
                    ≡⟨ cong
                         (λ x -> (maxOp G ⊔ x , suc (nbSeqCompl G (maxOp G ⊔ x))))
                         {nbOpListFor T + (nbOpFor A + nbOpListFor D)}
                         {suc nbOpD}
                         (trans
                           (cong
                             (λ x -> x + (nbOpFor A + nbOpListFor D))
                             eq₁)
                           eq₂) ⟩
                  (maxOp G ⊔ suc nbOpD , suc (nbSeqCompl G (maxOp G ⊔ suc nbOpD)))
                    ≡⟨ eq ⟩
                  (maxOpG , nbMaxOp) ∎)
                (cong-<L-l
                  {complexity (G ∣ (T , Δ))}
                  (ExchangeKeepComplexity
                    (insertDoExchange
                      G
                      (T , Δ)))
                  (complexityDecreasing
                    G
                    (T , Δ)
                    (T , Δ ∷ botAG)
                    (cong-≤-r
                      (sa+b=a+sb {nbOpListFor T} {nbOpListFor Δ})
                      ≤-refl)
                    (a≤b=>c≤d=>a+c≤b+d
                      {0}
                      {nbOpListFor T}
                      {maxOp G}
                      {suc (nbOpListFor Δ)}
                      (cong-≤-r
                        (sym eq₁)
                        ≤-refl)
                      (cong-≤-r
                        (sym
                          (trans
                            (ListExchangeKeepOperator
                              {Δ ∷ botAG}
                              {D ∷ A}
                              (ListExchangeCong
                                eq₃
                                (ListExchangeSym ListDoExchangeCorrect)))
                            eq₂))
                        x)))))))))
  createPreproofFun {G ∣ (T , (D ∷ A))} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] | Δ ∷ (A₁ ⊔S A₂) | [ eq₃ ] =
    Preseq-exchange
      G
      T
      T
      (Δ ∷ (A₁ ⊔S A₂))
      (D ∷ A)
      idLE
      (ListExchangeCong
        eq₃
        (ListExchangeSym ListDoExchangeCorrect))
      (Premax-R
        G
        T
        Δ
        A₁
        A₂
        (Prehseq-exchange
          (insert (insert G (T , Δ ∷ A₁)) (T , Δ ∷ A₂))
          (G ∣ (T , Δ ∷ A₁) ∣ (T , Δ ∷ A₂))
          (transHE
            (HSeqExchangeSym
              (insertDoExchange
                (insert G (T , Δ ∷ A₁))
                (T , Δ ∷ A₂)))
            (indHE
              (insert G (T , Δ ∷ A₁))
              (G ∣ (T , Δ ∷ A₁))
              (HSeqExchangeSym
                (insertDoExchange
                  G
                  (T , Δ ∷ A₁)))))
          (createPreproofFun
            {insert (insert G (T , (Δ ∷ A₁))) (T , (Δ ∷ A₂))}
            (insertKeepOrder
              {insert G (T , Δ ∷ A₁)}
              (insertKeepOrder
                OG))
            (rs
              (complexity (insert (insert G (T , (Δ ∷ A₁))) (T , (Δ ∷ A₂))))
              (cong-<L-r
                {complexity (G ∣ (T , Δ ∷ (A₁ ⊔S A₂)))}
                (begin
                  complexity (G ∣ (T , (Δ ∷ (A₁ ⊔S A₂))))
                    ≡⟨ ListExchangeRKeepComplexity
                         G
                         T
                         (Δ ∷ (A₁ ⊔S A₂))
                         (D ∷ A)
                         (ListExchangeCong
                           eq₃
                           (ListExchangeSym ListDoExchangeCorrect)) ⟩
                  complexity (G ∣ (T , (D ∷ A)))
                    ≡⟨ unfoldComplexity
                         G
                         (T , (D ∷ A))
                         (cong-≤-r
                           {suc nbOpD}
                           (sym
                             (trans
                               (cong
                                 (λ x -> x + (nbOpFor A + nbOpListFor D))
                                 eq₁)
                               eq₂))
                           x) ⟩
                  (maxOp G ⊔ (nbOpListFor T + (nbOpFor A + nbOpListFor D)), suc (nbSeqCompl G (maxOp G ⊔ (nbOpListFor T + (nbOpFor A + nbOpListFor D)))))
                    ≡⟨ cong
                         (λ x -> (maxOp G ⊔ x , suc (nbSeqCompl G (maxOp G ⊔ x))))
                         {nbOpListFor T + (nbOpFor A + nbOpListFor D)}
                         {suc nbOpD}
                         (trans
                           (cong
                             (λ x -> x + (nbOpFor A + nbOpListFor D))
                             eq₁)
                           eq₂) ⟩
                  (maxOp G ⊔ suc nbOpD , suc (nbSeqCompl G (maxOp G ⊔ suc nbOpD)))
                    ≡⟨ eq ⟩
                  (maxOpG , nbMaxOp) ∎)
               (cong-<L-l
                 {complexity (G ∣ (T , Δ ∷ A₁) ∣ (T , Δ ∷ A₂))}
                 (ExchangeKeepComplexity
                   {G ∣ (T , Δ ∷ A₁) ∣ (T , Δ ∷ A₂)}
                   {insert (insert G (T , Δ ∷ A₁)) (T , Δ ∷ A₂)}
                   (transHE
                     (indHE
                       (G ∣ (T , (Δ ∷ A₁)))
                       (insert G (T , Δ ∷ A₁))
                       (insertDoExchange
                         G
                         (T , Δ ∷ A₁)))
                     (insertDoExchange
                       (insert G (T , Δ ∷ A₁))
                       (T , Δ ∷ A₂))))
                 (complexityDecMaxR
                   G
                   T
                   Δ
                   A₁
                   A₂
                   (cong-≤-r
                     (begin
                       suc nbOpD
                         ≡⟨ sym eq₂ ⟩
                       nbOpFor A + nbOpListFor D
                         ≡⟨ ListExchangeKeepOperator
                              {D ∷ A}
                              {Δ ∷ (A₁ ⊔S A₂)}
                              (ListExchangeSym
                                (ListExchangeCong
                                  eq₃
                                  (ListExchangeSym ListDoExchangeCorrect))) ⟩
                       suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ)
                         ≡⟨ cong
                              (λ x -> x + suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ))
                              (sym eq₁) ⟩
                       nbOpListFor T + suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ) ∎)
                     x))) )))))
  createPreproofFun {G ∣ (T , (D ∷ A))} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] | Δ ∷ (A₁ +S A₂) | [ eq₃ ] =
    Preseq-exchange
      G
      T
      T
      (Δ ∷ (A₁ +S A₂))
      (D ∷ A)
      idLE
      (ListExchangeCong
        eq₃
        (ListExchangeSym ListDoExchangeCorrect))
      (Preplus-R
        G
        T
        Δ
        A₁
        A₂
        (Prehseq-exchange
          (insert G (T , (Δ ∷ A₁ ∷ A₂)))
          (G ∣ (T , (Δ ∷ A₁ ∷ A₂)))
          (HSeqExchangeSym (insertDoExchange G (T , (Δ ∷ A₁ ∷ A₂))))
          (createPreproofFun
            {insert G (T , (Δ ∷ A₁ ∷ A₂))}
            (insertKeepOrder OG)
            (rs
              (complexity (insert G (T , (Δ ∷ A₁ ∷ A₂))))
              (cong-<L-r
                {complexity (G ∣ (T , Δ ∷ (A₁ +S A₂)))}
                (begin
                  complexity (G ∣ (T , (Δ ∷ (A₁ +S A₂))))
                    ≡⟨ ListExchangeRKeepComplexity
                         G
                         T
                         (Δ ∷ (A₁ +S A₂))
                         (D ∷ A)
                         (ListExchangeCong
                           eq₃
                           (ListExchangeSym ListDoExchangeCorrect)) ⟩
                  complexity (G ∣ (T , (D ∷ A)))
                    ≡⟨ unfoldComplexity
                         G
                         (T , (D ∷ A))
                         (cong-≤-r
                           {suc nbOpD}
                           (sym
                             (trans
                               (cong
                                 (λ x -> x + (nbOpFor A + nbOpListFor D))
                                 eq₁)
                               eq₂))
                           x) ⟩
                  (maxOp G ⊔ (nbOpListFor T + (nbOpFor A + nbOpListFor D)), suc (nbSeqCompl G (maxOp G ⊔ (nbOpListFor T + (nbOpFor A + nbOpListFor D)))))
                    ≡⟨ cong
                         (λ x -> (maxOp G ⊔ x , suc (nbSeqCompl G (maxOp G ⊔ x))))
                         {nbOpListFor T + (nbOpFor A + nbOpListFor D)}
                         {suc nbOpD}
                         (trans
                           (cong
                             (λ x -> x + (nbOpFor A + nbOpListFor D))
                             eq₁)
                           eq₂) ⟩
                  (maxOp G ⊔ suc nbOpD , suc (nbSeqCompl G (maxOp G ⊔ suc nbOpD)))
                    ≡⟨ eq ⟩
                  (maxOpG , nbMaxOp) ∎)
                (cong-<L-l
                  {complexity (G ∣ (T , (Δ ∷ A₁ ∷ A₂)))}
                  (ExchangeKeepComplexity
                    (insertDoExchange G (T , (Δ ∷ A₁ ∷ A₂))))
                  (complexityDecreasing
                    G
                    (T , (Δ ∷ A₁ ∷ A₂))
                    (T , (Δ ∷ (A₁ +S A₂)))
                    (cong-≤-r
                      (sa+b=a+sb {nbOpListFor T} {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ})
                      (s≤s
                        (a≤b=>c≤d=>a+c≤b+d
                          {nbOpListFor T}
                          {nbOpListFor T}
                          {nbOpFor A₂ + (nbOpFor A₁ + nbOpListFor Δ)}
                          {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ}
                          ≤-refl
                          (cong-≤-l
                            {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ}
                            (trans
                              (cong
                                (λ x -> x + nbOpListFor Δ)
                                (+-comm (nbOpFor A₁) (nbOpFor A₂)))
                              (+-assoc (nbOpFor A₂) (nbOpFor A₁) (nbOpListFor Δ)))
                            ≤-refl))))
                    (cong-≤-r
                      (sym (
                        trans
                          (cong
                            (λ x -> nbOpListFor T + x)
                            (ListExchangeKeepOperator
                              {Δ ∷ (A₁ +S A₂)}
                              {D ∷ A}
                              (ListExchangeCong
                                eq₃
                                (ListExchangeSym ListDoExchangeCorrect))))
                          (trans
                            (cong
                              (λ x -> x + (nbOpFor A + nbOpListFor D))
                              eq₁)
                            eq₂)))
                      x))))))))
  createPreproofFun {G ∣ (T , (D ∷ A))} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] | Δ ∷ (A₁ ⊓S A₂) | [ eq₃ ] =
    Preseq-exchange
      G
      T
      T
      (Δ ∷ (A₁ ⊓S A₂))
      (D ∷ A)
      idLE
      (ListExchangeCong
        eq₃
        (ListExchangeSym ListDoExchangeCorrect))
      (Premin-R
        G
        T
        Δ
        A₁
        A₂
        (Prehseq-exchange
          (insert G (T , Δ ∷ A₁))
          (G ∣ (T , Δ ∷ A₁))
          (HSeqExchangeSym
            (insertDoExchange
              G
              (T , Δ ∷ A₁)))
          (createPreproofFun
            (insertKeepOrder OG)
            (rs
              (complexity (insert G (T , (Δ ∷ A₁))))
              (cong-<L-r
                {complexity (G ∣ (T , Δ ∷ (A₁ ⊓S A₂)))}
                (begin
                  complexity (G ∣ (T , (Δ ∷ (A₁ ⊓S A₂))))
                    ≡⟨ ListExchangeRKeepComplexity
                         G
                         T
                         (Δ ∷ (A₁ ⊓S A₂))
                         (D ∷ A)
                         (ListExchangeCong
                           eq₃
                           (ListExchangeSym ListDoExchangeCorrect)) ⟩
                  complexity (G ∣ (T , (D ∷ A)))
                    ≡⟨ unfoldComplexity
                         G
                         (T , (D ∷ A))
                         (cong-≤-r
                           {suc nbOpD}
                           (sym
                             (trans
                               (cong
                                 (λ x -> x + (nbOpFor A + nbOpListFor D))
                                 eq₁)
                               eq₂))
                           x) ⟩
                  (maxOp G ⊔ (nbOpListFor T + (nbOpFor A + nbOpListFor D)), suc (nbSeqCompl G (maxOp G ⊔ (nbOpListFor T + (nbOpFor A + nbOpListFor D)))))
                    ≡⟨ cong
                         (λ x -> (maxOp G ⊔ x , suc (nbSeqCompl G (maxOp G ⊔ x))))
                         {nbOpListFor T + (nbOpFor A + nbOpListFor D)}
                         {suc nbOpD}
                         (trans
                           (cong
                             (λ x -> x + (nbOpFor A + nbOpListFor D))
                             eq₁)
                           eq₂) ⟩
                  (maxOp G ⊔ suc nbOpD , suc (nbSeqCompl G (maxOp G ⊔ suc nbOpD)))
                    ≡⟨ eq ⟩
                  (maxOpG , nbMaxOp) ∎)
                (cong-<L-l
                  {complexity (G ∣ (T , Δ ∷ A₁))}
                  (ExchangeKeepComplexity
                    (insertDoExchange
                      G
                      (T , Δ ∷ A₁)))
                  (complexityDecreasing
                    G
                    (T , (Δ ∷ A₁))
                    (T , (Δ ∷ (A₁ ⊓S A₂)))
                    (cong-≤-r
                      (sa+b=a+sb {nbOpListFor T} {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ})
                      (s≤s
                        (a≤b=>c≤d=>a+c≤b+d
                          {nbOpListFor T}
                          {nbOpListFor T}
                          {nbOpFor A₁ + nbOpListFor Δ}
                          {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ}
                          ≤-refl
                          (cong-≤-r
                            (sym (+-assoc (nbOpFor A₁) (nbOpFor A₂) (nbOpListFor Δ)))
                            (a≤b=>c≤d=>a+c≤b+d
                              {nbOpFor A₁}
                              {nbOpFor A₁}
                              {nbOpListFor Δ}
                              {nbOpFor A₂ + nbOpListFor Δ}
                              ≤-refl
                              (cong-≤-r
                                (+-comm (nbOpListFor Δ) (nbOpFor A₂))
                                a≤a+b))))))
                    (≤-trans
                      x
                      (cong-≤-l
                        eq₂
                        (cong-≤-r
                          (cong
                            (λ x -> nbOpListFor T + x)
                            (ListExchangeKeepOperator
                              {D ∷ A}
                              {Δ ∷ (A₁ ⊓S A₂)}
                              (ListExchangeSym
                                (ListExchangeCong
                                  eq₃
                                  (ListExchangeSym ListDoExchangeCorrect)))))
                          (a≤b=>c≤d=>a+c≤b+d
                            {0}
                            {nbOpListFor T}
                            {nbOpFor A + nbOpListFor D}
                            {nbOpFor A + nbOpListFor D}
                            (cong-≤-l
                              eq₁
                              ≤-refl)
                            ≤-refl))))))))))
        (Prehseq-exchange
          (insert G (T , Δ ∷ A₂))
          (G ∣ (T , Δ ∷ A₂))
          (HSeqExchangeSym
            (insertDoExchange
              G
              (T , Δ ∷ A₂)))
          (createPreproofFun
            (insertKeepOrder OG)
            (rs
              (complexity (insert G (T , (Δ ∷ A₂))))
              (cong-<L-r
                {complexity (G ∣ (T , Δ ∷ (A₁ ⊓S A₂)))}
                (begin
                  complexity (G ∣ (T , (Δ ∷ (A₁ ⊓S A₂))))
                    ≡⟨ ListExchangeRKeepComplexity
                         G
                         T
                         (Δ ∷ (A₁ ⊓S A₂))
                         (D ∷ A)
                         (ListExchangeCong
                           eq₃
                           (ListExchangeSym ListDoExchangeCorrect)) ⟩
                  complexity (G ∣ (T , (D ∷ A)))
                    ≡⟨ unfoldComplexity
                         G
                         (T , (D ∷ A))
                         (cong-≤-r
                           {suc nbOpD}
                           (sym
                             (trans
                               (cong
                                 (λ x -> x + (nbOpFor A + nbOpListFor D))
                                 eq₁)
                               eq₂))
                           x) ⟩
                  (maxOp G ⊔ (nbOpListFor T + (nbOpFor A + nbOpListFor D)), suc (nbSeqCompl G (maxOp G ⊔ (nbOpListFor T + (nbOpFor A + nbOpListFor D)))))
                    ≡⟨ cong
                         (λ x -> (maxOp G ⊔ x , suc (nbSeqCompl G (maxOp G ⊔ x))))
                         {nbOpListFor T + (nbOpFor A + nbOpListFor D)}
                         {suc nbOpD}
                         (trans
                           (cong
                             (λ x -> x + (nbOpFor A + nbOpListFor D))
                             eq₁)
                           eq₂) ⟩
                  (maxOp G ⊔ suc nbOpD , suc (nbSeqCompl G (maxOp G ⊔ suc nbOpD)))
                    ≡⟨ eq ⟩
                  (maxOpG , nbMaxOp) ∎)
                (cong-<L-l
                  {complexity (G ∣ (T , Δ ∷ A₂))}
                  (ExchangeKeepComplexity
                    (insertDoExchange
                      G
                      (T , Δ ∷ A₂)))
                  (complexityDecreasing
                    G
                    (T , (Δ ∷ A₂))
                    (T , (Δ ∷ (A₁ ⊓S A₂)))
                    (cong-≤-r
                      (sa+b=a+sb {nbOpListFor T} {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ})
                      (s≤s
                        (a≤b=>c≤d=>a+c≤b+d
                          {nbOpListFor T}
                          {nbOpListFor T}
                          {nbOpFor A₂ + nbOpListFor Δ}
                          {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ}
                          ≤-refl
                          (cong-≤-r
                            {nbOpFor A₂ +( nbOpFor A₁ + nbOpListFor Δ)}
                            (trans
                              (sym (+-assoc (nbOpFor A₂) (nbOpFor A₁) (nbOpListFor Δ)))
                              (cong
                                (λ x -> x + nbOpListFor Δ)
                                (+-comm (nbOpFor A₂) (nbOpFor A₁))))
                            (a≤b=>c≤d=>a+c≤b+d
                              {nbOpFor A₂}
                              {nbOpFor A₂}
                              {nbOpListFor Δ}
                              {nbOpFor A₁ + nbOpListFor Δ}
                              ≤-refl
                              (cong-≤-r
                                (+-comm (nbOpListFor Δ) (nbOpFor A₁))
                                a≤a+b))))))
                    (≤-trans
                      x
                      (cong-≤-l
                        eq₂
                        (cong-≤-r
                          (cong
                            (λ x -> nbOpListFor T + x)
                            (ListExchangeKeepOperator
                              {D ∷ A}
                              {Δ ∷ (A₁ ⊓S A₂)}
                              (ListExchangeSym
                                (ListExchangeCong
                                  eq₃
                                  (ListExchangeSym ListDoExchangeCorrect)))))
                          (a≤b=>c≤d=>a+c≤b+d
                            {0}
                            {nbOpListFor T}
                            {nbOpFor A + nbOpListFor D}
                            {nbOpFor A + nbOpListFor D}
                            (cong-≤-l
                              eq₁
                              ≤-refl)
                            ≤-refl)))))))))))
  createPreproofFun {G ∣ (T , (D ∷ A))} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] | Δ ∷ (-S A₁) | [ eq₃ ] =
    Preseq-exchange
      G
      T
      T
      (Δ ∷ (-S A₁))
      (D ∷ A)
      idLE
      (ListExchangeCong
        eq₃
        (ListExchangeSym ListDoExchangeCorrect))
      (Preminus-R
        G
        T
        Δ
        A₁
        (Prehseq-exchange
          (insert G (T ∷ A₁ , Δ))
          (G ∣ (T ∷ A₁ , Δ))
          (HSeqExchangeSym
            (insertDoExchange
              G
              (T ∷ A₁ , Δ)))
          (createPreproofFun
            (insertKeepOrder OG)
            (rs
              (complexity (insert G ((T ∷ A₁) , Δ)))
              (cong-<L-r
                {complexity (G ∣ (T , Δ ∷ (-S A₁)))}
                (begin
                  complexity (G ∣ (T , (Δ ∷ (-S A₁))))
                    ≡⟨ ListExchangeRKeepComplexity
                         G
                         T
                         (Δ ∷ (-S A₁))
                         (D ∷ A)
                         (ListExchangeCong
                           eq₃
                           (ListExchangeSym ListDoExchangeCorrect)) ⟩
                  complexity (G ∣ (T , (D ∷ A)))
                    ≡⟨ unfoldComplexity
                         G
                         (T , (D ∷ A))
                         (cong-≤-r
                           {suc nbOpD}
                           (sym
                             (trans
                               (cong
                                 (λ x -> x + (nbOpFor A + nbOpListFor D))
                                 eq₁)
                               eq₂))
                           x) ⟩
                  (maxOp G ⊔ (nbOpListFor T + (nbOpFor A + nbOpListFor D)), suc (nbSeqCompl G (maxOp G ⊔ (nbOpListFor T + (nbOpFor A + nbOpListFor D)))))
                    ≡⟨ cong
                         (λ x -> (maxOp G ⊔ x , suc (nbSeqCompl G (maxOp G ⊔ x))))
                         {nbOpListFor T + (nbOpFor A + nbOpListFor D)}
                         {suc nbOpD}
                         (trans
                           (cong
                             (λ x -> x + (nbOpFor A + nbOpListFor D))
                             eq₁)
                           eq₂) ⟩
                  (maxOp G ⊔ suc nbOpD , suc (nbSeqCompl G (maxOp G ⊔ suc nbOpD)))
                    ≡⟨ eq ⟩
                  (maxOpG , nbMaxOp) ∎)
                (cong-<L-l
                  {complexity (G ∣ (T ∷ A₁ , Δ))}
                  (ExchangeKeepComplexity
                    (insertDoExchange
                      G
                      (T ∷ A₁ , Δ)))
                  (complexityDecreasing
                    G
                    (T ∷ A₁ , Δ)
                    (T , (Δ ∷ (-S A₁)))
                    (cong-≤-r
                      (begin
                        suc (nbOpFor A₁ + nbOpListFor T + nbOpListFor Δ)
                          ≡⟨ cong
                               (λ x -> suc (x + nbOpListFor Δ))
                               (+-comm (nbOpFor A₁) (nbOpListFor T)) ⟩
                        suc (nbOpListFor T + nbOpFor A₁ + nbOpListFor Δ)
                          ≡⟨ cong
                               suc
                               (+-assoc (nbOpListFor T) (nbOpFor A₁) (nbOpListFor Δ)) ⟩
                        suc (nbOpListFor T + (nbOpFor A₁ + nbOpListFor Δ))
                          ≡⟨ sa+b=a+sb {nbOpListFor T} {nbOpFor A₁ + nbOpListFor Δ} ⟩
                        nbOpListFor T + suc (nbOpFor A₁ + nbOpListFor Δ) ∎)
                      ≤-refl)
                    (≤-trans
                      x
                      (cong-≤-l
                        eq₂
                        (cong-≤-l
                          {suc (nbOpFor A₁ + nbOpListFor Δ)}
                          (ListExchangeKeepOperator
                            {Δ ∷ (-S A₁)}
                            {D ∷ A}
                            (ListExchangeCong
                              eq₃
                              (ListExchangeSym ListDoExchangeCorrect)))
                          (a≤b=>c≤d=>a+c≤b+d
                            {0}
                            {nbOpListFor T}
                            {suc (nbOpFor A₁ + nbOpListFor Δ)}
                            {suc (nbOpFor A₁ + nbOpListFor Δ)}
                            (cong-≤-l
                              eq₁
                              ≤-refl)
                            ≤-refl)))))))))))
  createPreproofFun {G ∣ ([] , D)} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] =
    ⊥-elim (notSucEqZero (sym eq₁))
  createPreproofFun {G ∣ ((T ∷ A) , D)} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] with ListDoExchange (T ∷ A) | inspect ListDoExchange (T ∷ A)
  createPreproofFun {G ∣ ((T ∷ A) , D)} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] | [] | [ eq₂ ] =
    ⊥-elim (¬ListDoExchangeΓ∷A=[] T A eq₂)
  createPreproofFun {G ∣ ((T ∷ A) , D)} (ConsOrdered OG x') (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] | Γ ∷ varAG x | [ eq₂ ] =
    ⊥-elim (ListDoExchangeNoVar {T ∷ A} (λ x₁ → notSucEqZero (trans (sym eq₁) x₁)) Γ x eq₂)
  createPreproofFun {G ∣ ((T ∷ A) , D)} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] | Γ ∷ botAG | [ eq₂ ] =
    Preseq-exchange
      G
      (Γ ∷ botAG)
      (T ∷ A)
      D
      D
      (ListExchangeCong
        eq₂
        (ListExchangeSym ListDoExchangeCorrect))
      idLE
      (PreZ-L
        G
        Γ
        D
        (Prehseq-exchange
          (insert G (Γ , D))
          (G ∣ (Γ , D))
          (HSeqExchangeSym
            (insertDoExchange G (Γ , D)))
          (createPreproofFun
            (insertKeepOrder OG)
            (rs
              (complexity (insert G (Γ , D)))
              (cong-<L-r
                {complexity (G ∣ (Γ ∷ botAG , D))}
                (begin
                  complexity (G ∣ ((Γ ∷ botAG) , D))
                    ≡⟨ ListExchangeLKeepComplexity
                         G
                         (Γ ∷ botAG)
                         (T ∷ A)
                         D
                         (ListExchangeCong eq₂ (ListExchangeSym ListDoExchangeCorrect)) ⟩
                  complexity (G ∣ (T ∷ A , D))
                    ≡⟨ unfoldComplexity G (T ∷ A , D) (cong-≤-r (cong (λ x -> x + nbOpListFor D) (sym eq₁)) x) ⟩
                  (maxOp G ⊔ ((nbOpFor A + nbOpListFor T) + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ ((nbOpFor A + nbOpListFor T) + nbOpListFor D))))
                    ≡⟨ cong (λ x -> (maxOp G ⊔ (x + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ (x + nbOpListFor D))))) eq₁ ⟩
                  (maxOp G ⊔ suc (nbOpT + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ suc (nbOpT + nbOpListFor D))))
                    ≡⟨ eq ⟩
                  (maxOpG , nbMaxOp) ∎)
                (cong-<L-l
                  {complexity (G ∣ (Γ , D))}
                  (ExchangeKeepComplexity
                    {(G ∣ (Γ , D))}
                    {(insert G (Γ  , D))}
                    (insertDoExchange
                      G
                      (Γ , D)))
                    (complexityDecreasing
                      G
                      (Γ , D)
                      (Γ ∷ botAG , D)
                      ≤-refl
                      (cong-≤-r
                        {suc (nbOpT + nbOpListFor D)}
                        (cong
                          (λ x -> x + nbOpListFor D)
                          (trans
                            (sym eq₁)
                            (ListExchangeKeepOperator
                              {T ∷ A}
                              {Γ ∷ botAG}
                              (ListExchangeSym
                                (ListExchangeCong
                                  eq₂
                                  (ListExchangeSym ListDoExchangeCorrect))))))
                        x))))))))
  createPreproofFun {G ∣ ((T ∷ A) , D)} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] | Γ ∷ (A₁ ⊔S A₂) | [ eq₂ ] =
    Preseq-exchange
      G
      (Γ ∷ (A₁ ⊔S A₂))
      (T ∷ A)
      D
      D
      (ListExchangeCong
        eq₂
        (ListExchangeSym ListDoExchangeCorrect))
      idLE
      (Premax-L
        G
        Γ
        D
        A₁
        A₂
        (Prehseq-exchange
          (insert G (Γ ∷ A₁ , D))
          (G ∣ (Γ ∷ A₁ , D))
          (HSeqExchangeSym
            (insertDoExchange G (Γ ∷ A₁ , D)))
          (createPreproofFun
            (insertKeepOrder OG)
            (rs
              (complexity (insert G (Γ ∷ A₁ , D)))
              (cong-<L-r
                {complexity (G ∣ (Γ ∷ (A₁ ⊔S A₂) , D))}
                (begin
                  complexity (G ∣ ((Γ ∷ (A₁ ⊔S A₂)) , D))
                    ≡⟨ ListExchangeLKeepComplexity
                         G
                         (Γ ∷ (A₁ ⊔S A₂))
                         (T ∷ A)
                         D
                         (ListExchangeCong eq₂ (ListExchangeSym ListDoExchangeCorrect)) ⟩
                  complexity (G ∣ (T ∷ A , D))
                    ≡⟨ unfoldComplexity G (T ∷ A , D) (cong-≤-r (cong (λ x -> x + nbOpListFor D) (sym eq₁)) x) ⟩
                  (maxOp G ⊔ ((nbOpFor A + nbOpListFor T) + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ ((nbOpFor A + nbOpListFor T) + nbOpListFor D))))
                    ≡⟨ cong (λ x -> (maxOp G ⊔ (x + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ (x + nbOpListFor D))))) eq₁ ⟩
                  (maxOp G ⊔ suc (nbOpT + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ suc (nbOpT + nbOpListFor D))))
                    ≡⟨ eq ⟩
                  (maxOpG , nbMaxOp) ∎)
                (cong-<L-l
                  {complexity (G ∣ (Γ ∷ A₁ , D))}
                  (ExchangeKeepComplexity
                    {(G ∣ (Γ ∷ A₁ , D))}
                    {(insert G (Γ ∷ A₁  , D))}
                    (insertDoExchange
                      G
                      (Γ ∷ A₁ , D)))
                    (complexityDecreasing
                      G
                      (Γ ∷ A₁ , D)
                      (Γ ∷ (A₁ ⊔S A₂) , D)
                      (s≤s
                        (a≤b=>c≤d=>a+c≤b+d
                          {nbOpFor A₁ + nbOpListFor Γ}
                          {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ}
                          {nbOpListFor D}
                          {nbOpListFor D}
                          (a≤b=>c≤d=>a+c≤b+d
                            {nbOpFor A₁}
                            {nbOpFor A₁ + nbOpFor A₂}
                            {nbOpListFor Γ}
                            {nbOpListFor Γ}
                            (a≤a+b {nbOpFor A₁} {nbOpFor A₂})
                            ≤-refl)
                          ≤-refl))
                      ((cong-≤-r
                        {suc (nbOpT + nbOpListFor D)}
                        (cong
                          (λ x -> x + nbOpListFor D)
                          (trans
                            (sym eq₁)
                            (ListExchangeKeepOperator
                              {T ∷ A}
                              {Γ ∷ (A₁ ⊔S A₂)}
                              (ListExchangeSym
                                (ListExchangeCong
                                  eq₂
                                  (ListExchangeSym ListDoExchangeCorrect))))))
                        x))))))))
        (Prehseq-exchange
          (insert G (Γ ∷ A₂ , D))
          (G ∣ (Γ ∷ A₂ , D))
          (HSeqExchangeSym
            (insertDoExchange G (Γ ∷ A₂ , D)))
          (createPreproofFun
            (insertKeepOrder OG)
            (rs
              (complexity (insert G (Γ ∷ A₂ , D)))
              (cong-<L-r
                {complexity (G ∣ (Γ ∷ (A₁ ⊔S A₂) , D))}
                (begin
                  complexity (G ∣ ((Γ ∷ (A₁ ⊔S A₂)) , D))
                    ≡⟨ ListExchangeLKeepComplexity
                         G
                         (Γ ∷ (A₁ ⊔S A₂))
                         (T ∷ A)
                         D
                         (ListExchangeCong eq₂ (ListExchangeSym ListDoExchangeCorrect)) ⟩
                  complexity (G ∣ (T ∷ A , D))
                    ≡⟨ unfoldComplexity G (T ∷ A , D) (cong-≤-r (cong (λ x -> x + nbOpListFor D) (sym eq₁)) x) ⟩
                  (maxOp G ⊔ ((nbOpFor A + nbOpListFor T) + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ ((nbOpFor A + nbOpListFor T) + nbOpListFor D))))
                    ≡⟨ cong (λ x -> (maxOp G ⊔ (x + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ (x + nbOpListFor D))))) eq₁ ⟩
                  (maxOp G ⊔ suc (nbOpT + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ suc (nbOpT + nbOpListFor D))))
                    ≡⟨ eq ⟩
                  (maxOpG , nbMaxOp) ∎)
                (cong-<L-l
                  {complexity (G ∣ (Γ ∷ A₂ , D))}
                  (ExchangeKeepComplexity
                    {(G ∣ (Γ ∷ A₂ , D))}
                    {(insert G (Γ ∷ A₂  , D))}
                    (insertDoExchange
                      G
                      (Γ ∷ A₂ , D)))
                    (complexityDecreasing
                      G
                      (Γ ∷ A₂ , D)
                      (Γ ∷ (A₁ ⊔S A₂) , D)
                      (s≤s
                        (a≤b=>c≤d=>a+c≤b+d
                          {nbOpFor A₂ + nbOpListFor Γ}
                          {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ}
                          {nbOpListFor D}
                          {nbOpListFor D}
                          (a≤b=>c≤d=>a+c≤b+d
                            {nbOpFor A₂}
                            {nbOpFor A₁ + nbOpFor A₂}
                            {nbOpListFor Γ}
                            {nbOpListFor Γ}
                            (cong-≤-r
                              (+-comm (nbOpFor A₂) (nbOpFor A₁))
                              (a≤a+b {nbOpFor A₂} {nbOpFor A₁}))
                            ≤-refl)
                          ≤-refl))
                      ((cong-≤-r
                        {suc (nbOpT + nbOpListFor D)}
                        (cong
                          (λ x -> x + nbOpListFor D)
                          (trans
                            (sym eq₁)
                            (ListExchangeKeepOperator
                              {T ∷ A}
                              {Γ ∷ (A₁ ⊔S A₂)}
                              (ListExchangeSym
                                (ListExchangeCong
                                  eq₂
                                  (ListExchangeSym ListDoExchangeCorrect))))))
                        x)))))))))
  createPreproofFun {G ∣ ((T ∷ A) , D)} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] | Γ ∷ (A₁ +S A₂) | [ eq₂ ] =
    Preseq-exchange
      G
      (Γ ∷ (A₁ +S A₂))
      (T ∷ A)
      D
      D
      (ListExchangeCong
        eq₂
        (ListExchangeSym ListDoExchangeCorrect))
      idLE
      (Preplus-L
        G
        Γ
        D
        A₁
        A₂
        (Prehseq-exchange
          (insert G ((Γ ∷ A₁ ∷ A₂) , D))
          (G ∣ ((Γ ∷ A₁ ∷ A₂) , D))
          (HSeqExchangeSym
            (insertDoExchange
              G
              ((Γ ∷ A₁ ∷ A₂) , D)))
          (createPreproofFun
            {insert G ((Γ ∷ A₁ ∷ A₂) , D)}
            (insertKeepOrder OG)
            (rs
              (complexity (insert G ((Γ ∷ A₁ ∷ A₂) , D)))
              (cong-<L-r
                {complexity (G ∣ (Γ ∷ (A₁ +S A₂), D))}
                (begin
                  complexity (G ∣ ((Γ ∷ (A₁ +S A₂)) , D))
                    ≡⟨ ListExchangeLKeepComplexity
                         G
                         (Γ ∷ (A₁ +S A₂))
                         (T ∷ A)
                         D
                         (ListExchangeCong eq₂ (ListExchangeSym ListDoExchangeCorrect)) ⟩
                  complexity (G ∣ (T ∷ A , D))
                    ≡⟨ unfoldComplexity G (T ∷ A , D) (cong-≤-r (cong (λ x -> x + nbOpListFor D) (sym eq₁)) x) ⟩
                  (maxOp G ⊔ ((nbOpFor A + nbOpListFor T) + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ ((nbOpFor A + nbOpListFor T) + nbOpListFor D))))
                    ≡⟨ cong (λ x -> (maxOp G ⊔ (x + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ (x + nbOpListFor D))))) eq₁ ⟩
                  (maxOp G ⊔ suc (nbOpT + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ suc (nbOpT + nbOpListFor D))))
                    ≡⟨ eq ⟩
                  (maxOpG , nbMaxOp) ∎)
                (cong-<L-l
                  {complexity (G ∣ ((Γ ∷ A₁ ∷ A₂) , D))}
                  (ExchangeKeepComplexity
                    {(G ∣ ((Γ ∷ A₁ ∷ A₂) , D))}
                    {(insert G ((Γ ∷ A₁ ∷ A₂) , D))}
                    (insertDoExchange
                      G
                      (Γ ∷ A₁ ∷ A₂ , D)))
                  (complexityDecreasing
                    G
                    ((Γ ∷ A₁ ∷ A₂) , D)
                    ((Γ ∷ (A₁ +S A₂)) , D)
                    (s≤s (cong-≤-l
                           (cong
                             (λ x -> x + nbOpListFor D)
                             {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ}
                             {nbOpFor A₂ + (nbOpFor A₁ + nbOpListFor Γ)}
                             (begin
                               nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ
                                 ≡⟨ cong
                                      (λ x -> x + nbOpListFor Γ)
                                      (+-comm (nbOpFor A₁) (nbOpFor A₂)) ⟩
                               nbOpFor A₂ + nbOpFor A₁ + nbOpListFor Γ
                                 ≡⟨ +-assoc (nbOpFor A₂) (nbOpFor A₁) (nbOpListFor Γ) ⟩
                               nbOpFor A₂ + (nbOpFor A₁ + nbOpListFor Γ) ∎))
                           ≤-refl))
                    (cong-≤-r
                      (cong
                        (λ x -> x + nbOpListFor D)
                        {suc nbOpT}
                        {suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ)}
                        (trans
                          (sym eq₁)
                          (ListExchangeKeepOperator
                            {T ∷ A}
                            {Γ ∷ (A₁ +S A₂)}
                            (ListExchangeSym (
                              ListExchangeCong
                              eq₂
                              (ListExchangeSym ListDoExchangeCorrect))))))
                      x))))))))
  createPreproofFun {G ∣ ((T ∷ A) , D)} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] | Γ ∷ (A₁ ⊓S A₂) | [ eq₂ ] =
    Preseq-exchange
      G
      (Γ ∷ (A₁ ⊓S A₂))
      (T ∷ A)
      D
      D
      (ListExchangeCong
        eq₂
        (ListExchangeSym ListDoExchangeCorrect))
      idLE
      (Premin-L
        G
        Γ
        D
        A₁
        A₂
        (Prehseq-exchange
          (insert (insert G (Γ ∷ A₁ , D)) (Γ ∷ A₂ , D))
          (G ∣ (Γ ∷ A₁ , D) ∣ (Γ ∷ A₂ , D))
          (HSeqExchangeSym
            (transHE
              (indHE
                (G ∣ (Γ ∷ A₁ , D))
                (insert G (Γ ∷ A₁ , D))
                (insertDoExchange G (Γ ∷ A₁ , D)))
              (insertDoExchange (insert G (Γ ∷ A₁ , D)) (Γ ∷ A₂ , D))))
          (createPreproofFun
            (insertKeepOrder
              (insertKeepOrder OG))
            (rs
              (complexity (insert (insert G (Γ ∷ A₁ , D)) (Γ ∷ A₂ , D)))
              (cong-<L-r
                {complexity (G ∣ (Γ ∷ (A₁ ⊓S A₂), D))}
                (begin
                  complexity (G ∣ ((Γ ∷ (A₁ ⊓S A₂)) , D))
                    ≡⟨ ListExchangeLKeepComplexity
                         G
                         (Γ ∷ (A₁ ⊓S A₂))
                         (T ∷ A)
                         D
                         (ListExchangeCong eq₂ (ListExchangeSym ListDoExchangeCorrect)) ⟩
                  complexity (G ∣ (T ∷ A , D))
                    ≡⟨ unfoldComplexity G (T ∷ A , D) (cong-≤-r (cong (λ x -> x + nbOpListFor D) (sym eq₁)) x) ⟩
                  (maxOp G ⊔ ((nbOpFor A + nbOpListFor T) + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ ((nbOpFor A + nbOpListFor T) + nbOpListFor D))))
                    ≡⟨ cong (λ x -> (maxOp G ⊔ (x + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ (x + nbOpListFor D))))) eq₁ ⟩
                  (maxOp G ⊔ suc (nbOpT + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ suc (nbOpT + nbOpListFor D))))
                    ≡⟨ eq ⟩
                  (maxOpG , nbMaxOp) ∎)
                (cong-<L-l
                  {complexity (G ∣ (Γ ∷ A₁ , D) ∣ (Γ ∷ A₂ , D))}
                  (ExchangeKeepComplexity
                    (transHE
                      (indHE
                        (G ∣ (Γ ∷ A₁ , D))
                        (insert G (Γ ∷ A₁ , D))
                        (insertDoExchange G (Γ ∷ A₁ , D)))
                    (insertDoExchange (insert G (Γ ∷ A₁ , D)) (Γ ∷ A₂ , D))))
                  (complexityDecMinL
                    G
                    Γ
                    D
                    A₁
                    A₂
                    (cong-≤-r
                      (cong
                        (λ x -> x + nbOpListFor D)
                        (trans
                          (sym eq₁)
                          (ListExchangeKeepOperator
                            {T ∷ A}
                            {Γ ∷ (A₁ ⊓S A₂)}
                            (ListExchangeSym
                              (ListExchangeCong
                                eq₂
                                (ListExchangeSym ListDoExchangeCorrect))))))
                      x))))))))
  createPreproofFun {G ∣ ((T ∷ A) , D)} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] | Γ ∷ (-S A₁) | [ eq₂ ] =
    Preseq-exchange
      G
      (Γ ∷ (-S A₁))
      (T ∷ A)
      D
      D
      (ListExchangeCong
        eq₂
        (ListExchangeSym ListDoExchangeCorrect))
      idLE
      (Preminus-L
        G
        Γ
        D
        A₁
        (Prehseq-exchange
          (insert G (Γ , D ∷ A₁))
          (G ∣ (Γ , D ∷ A₁))
          (HSeqExchangeSym
            (insertDoExchange G (Γ , D ∷ A₁)))
          (createPreproofFun
            (insertKeepOrder OG)
            (rs
              (complexity (insert G (Γ , D ∷ A₁)))
              (cong-<L-r
                {complexity (G ∣ (Γ ∷ (-S A₁), D))}
                (begin
                  complexity (G ∣ ((Γ ∷ (-S A₁)) , D))
                    ≡⟨ ListExchangeLKeepComplexity
                         G
                         (Γ ∷ (-S A₁))
                         (T ∷ A)
                         D
                         (ListExchangeCong eq₂ (ListExchangeSym ListDoExchangeCorrect)) ⟩
                  complexity (G ∣ (T ∷ A , D))
                    ≡⟨ unfoldComplexity G (T ∷ A , D) (cong-≤-r (cong (λ x -> x + nbOpListFor D) (sym eq₁)) x) ⟩
                  (maxOp G ⊔ ((nbOpFor A + nbOpListFor T) + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ ((nbOpFor A + nbOpListFor T) + nbOpListFor D))))
                    ≡⟨ cong (λ x -> (maxOp G ⊔ (x + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ (x + nbOpListFor D))))) eq₁ ⟩
                  (maxOp G ⊔ suc (nbOpT + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ suc (nbOpT + nbOpListFor D))))
                    ≡⟨ eq ⟩
                  (maxOpG , nbMaxOp) ∎)
                (cong-<L-l
                  {complexity (G ∣ (Γ , D ∷ A₁))}
                  (ExchangeKeepComplexity
                    {(G ∣ (Γ , D ∷ A₁))}
                    {(insert G (Γ , D ∷ A₁))}
                    (insertDoExchange
                      G
                      (Γ , D ∷ A₁)))
                  (complexityDecreasing
                    G
                    (Γ , D ∷ A₁)
                    (Γ ∷ (-S A₁) , D)
                    (s≤s
                      (cong-≤-l
                        (begin
                          nbOpFor A₁ + nbOpListFor Γ + nbOpListFor D
                            ≡⟨ cong
                                 (λ x -> x + nbOpListFor D)
                                 (+-comm (nbOpFor A₁) (nbOpListFor Γ)) ⟩
                          nbOpListFor Γ + nbOpFor A₁ + nbOpListFor D
                            ≡⟨ +-assoc (nbOpListFor Γ) (nbOpFor A₁) (nbOpListFor D) ⟩
                          nbOpListFor Γ + (nbOpFor A₁ + nbOpListFor D) ∎)
                        ≤-refl))
                    (cong-≤-r
                      (cong
                        (λ x -> x + nbOpListFor D)
                        {suc nbOpT}
                        {suc (nbOpFor A₁ + nbOpListFor Γ)}
                        (trans
                          (sym eq₁)
                          (ListExchangeKeepOperator
                            {T ∷ A}
                            {Γ ∷ (-S A₁)}
                            (ListExchangeSym (
                              ListExchangeCong
                              eq₂
                              (ListExchangeSym ListDoExchangeCorrect))))))
                      x))))))))
  createPreproofFun {G ∣ (T , D)} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | no ¬p =
    ⊥-elim (¬p (sym (k≤k'=>k⊔k'=k' x)))
--}}}

  createPreproof :
    (G : HSeq) ->
    Preproof G
--{{{
  createPreproof G =
    Prehseq-exchange
      (order G)
      G
      (HSeqExchangeSym
        (orderDoExchange G))
      (createPreproofFun
        {order G}
        (orderCorrect G)
        (AccessibleL (complexity (order G))))
--}}}

  abstract
    cPpFunGiveAtomicLeaves :
      {G : HSeq} ->
      (OG : OrderedHSeq G) ->
      (accCG : Acc _<L_ (complexity G)) ->
      AtomicHSeqList (getLeaf (createPreproofFun OG accCG))
--{{{
    cPpFunGiveAtomicLeaves {G} OG (acc rs) with complexity G | inspect complexity G
    cPpFunGiveAtomicLeaves {head (T , D)} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] with (nbOpListFor T + nbOpListFor D) ≡? (nbOpListFor T + nbOpListFor D)
    cPpFunGiveAtomicLeaves {head (T , D)} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p with nbOpListFor T | inspect nbOpListFor T
    cPpFunGiveAtomicLeaves {head (T , D)} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] with nbOpListFor D | inspect nbOpListFor D
    cPpFunGiveAtomicLeaves {head (T , D)} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | zero | [ eq₂ ] =
      atomicConsH
        atomic[]H
        (trans
          (cong
            (λ x -> x + nbOpListFor D)
            eq₁)
          eq₂)
    cPpFunGiveAtomicLeaves {head (T , [])} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] =
      ⊥-elim (notSucEqZero (sym eq₂))
    cPpFunGiveAtomicLeaves {head (T , (D ∷ A))} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] with ListDoExchange (D ∷ A) | inspect ListDoExchange (D ∷ A)
    cPpFunGiveAtomicLeaves {head (T , (D ∷ A))} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] | [] | [ eq₃ ] =
      ⊥-elim (¬ListDoExchangeΓ∷A=[] D A eq₃)
    cPpFunGiveAtomicLeaves {head (T , (D ∷ A))} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] | Δ ∷ varAG x | [ eq₃ ] =
      ⊥-elim
        (ListDoExchangeNoVar
          {D ∷ A}
          (λ x₁ -> notSucEqZero (trans (sym eq₂) x₁))
          Δ
          x
          eq₃)
    cPpFunGiveAtomicLeaves {head (T , (D ∷ A))} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] | Δ ∷ botAG | [ eq₃ ] =
      cPpFunGiveAtomicLeaves
        (HeadOrdered (T , Δ))
        (rs
          (complexity (head (T , Δ)))
          (cong-<L-r
            {complexity (head (T , Δ ∷ botAG))}
            (begin
              complexity (head (T , (Δ ∷ botAG)))
                ≡⟨ complexityHead (T , Δ ∷ botAG) ⟩
              (nbOpSeq (T , Δ ∷ botAG) , 1)
                ≡⟨ cong
                     (λ x -> (nbOpListFor T + x , 1))
                     (ListExchangeKeepOperator
                       {Δ ∷ botAG}
                       {D ∷ A}
                       (ListExchangeCong
                         eq₃
                         (ListExchangeSym ListDoExchangeCorrect))) ⟩
              (nbOpSeq (T , (D ∷ A)) , 1)
                ≡⟨ cong
                     (λ x -> (x + nbOpListFor (D ∷ A) , 1))
                     eq₁ ⟩
              (nbOpListFor (D ∷ A) , 1)
                ≡⟨ cong
                     (λ x -> (x , 1))
                     eq₂ ⟩
              (suc nbOpD , 1)
                ≡⟨ eq ⟩
              (maxOpG , nbMaxOp) ∎)
            (first
              (cong-≤-r
                (sa+b=a+sb {nbOpListFor T} {nbOpListFor Δ})
                ≤-refl))))
    cPpFunGiveAtomicLeaves {head (T , (D ∷ A))} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] | Δ ∷ (A₁ ⊔S A₂) | [ eq₃ ] =
      cPpFunGiveAtomicLeaves
        {insert (head (T , Δ ∷ A₁)) (T , Δ ∷ A₂)}
        (insertKeepOrder
          {head (T , Δ ∷ A₁)}
          {T , Δ ∷ A₂}
          (HeadOrdered (T , Δ ∷ A₁)))
        (rs
          (complexity (insert (head (T , Δ ∷ A₁)) (T , Δ ∷ A₂)))
          (cong-<L-l
            {complexity (head (T , Δ ∷ A₁) ∣ (T , Δ ∷ A₂))}
            (ExchangeKeepComplexity
              {head (T , (Δ ∷ A₁)) ∣ (T , (Δ ∷ A₂))}
              {insert (head (T , Δ ∷ A₁)) (T , Δ ∷ A₂)}
              (insertDoExchange
                (head (T , Δ ∷ A₁))
                (T , Δ ∷ A₂)))
            (cong-<L-r
              {complexity (head (T , Δ ∷ (A₁ ⊔S A₂)))}
              (begin
                complexity (head (T , (Δ ∷ (A₁ ⊔S A₂))))
                  ≡⟨ complexityHead (T , Δ ∷ (A₁ ⊔S A₂)) ⟩
                (nbOpSeq (T , (Δ ∷ (A₁ ⊔S A₂))) , 1)
                  ≡⟨ cong
                       (λ x -> (x + nbOpListFor (Δ ∷ (A₁ ⊔S A₂)) , 1))
                       eq₁ ⟩
                nbOpListFor (Δ ∷ (A₁ ⊔S A₂)) , 1
                  ≡⟨ cong
                       (λ x -> x , 1)
                       (ListExchangeKeepOperator
                         {Δ ∷ (A₁ ⊔S A₂)}
                         {D ∷ A}
                         (ListExchangeCong
                           eq₃
                           (ListExchangeSym ListDoExchangeCorrect))) ⟩
                nbOpListFor (D ∷ A) , 1
                  ≡⟨ cong
                       (λ x -> x , 1)
                       eq₂ ⟩
                suc nbOpD , 1
                  ≡⟨ eq ⟩
                maxOpG , nbMaxOp ∎)
              (first
                (⊔-≤
                  {suc (nbOpListFor T + (nbOpFor A₁ + nbOpListFor Δ))}
                  {suc (nbOpListFor T + (nbOpFor A₂ + nbOpListFor Δ))}
                  {nbOpListFor T + suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ)}
                  (cong-≤-l
                    {suc (nbOpFor A₁ + nbOpListFor Δ)}
                    (cong
                      (λ x -> suc (x + (nbOpFor A₁ + nbOpListFor Δ)))
                        (sym eq₁))
                    (cong-≤-r
                      {suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ)}
                      (cong
                        (λ x -> x + suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ))
                        (sym eq₁))
                      (s≤s
                        (cong-≤-r
                          {nbOpFor A₁ + nbOpListFor Δ + nbOpFor A₂}
                          (begin
                            nbOpFor A₁ + nbOpListFor Δ + nbOpFor A₂
                              ≡⟨ +-assoc (nbOpFor A₁) (nbOpListFor Δ) (nbOpFor A₂) ⟩
                            nbOpFor A₁ + (nbOpListFor Δ + nbOpFor A₂)
                              ≡⟨ cong
                                   (λ x -> nbOpFor A₁ + x)
                                   (+-comm (nbOpListFor Δ) (nbOpFor A₂)) ⟩
                            nbOpFor A₁ + (nbOpFor A₂ + nbOpListFor Δ)
                              ≡⟨ sym (+-assoc (nbOpFor A₁) (nbOpFor A₂) (nbOpListFor Δ)) ⟩
                            nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ ∎)
                          a≤a+b))))
                      ((cong-≤-l
                        {suc (nbOpFor A₂ + nbOpListFor Δ)}
                        (cong
                          (λ x -> suc (x + (nbOpFor A₂ + nbOpListFor Δ)))
                          (sym eq₁))
                        (cong-≤-r
                          {suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ)}
                          (cong
                            (λ x -> x + suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ))
                            (sym eq₁))
                          (s≤s
                            (cong-≤-r
                              {nbOpFor A₂ + nbOpListFor Δ + nbOpFor A₁}
                              (begin
                                nbOpFor A₂ + nbOpListFor Δ + nbOpFor A₁
                                  ≡⟨ +-comm (nbOpFor A₂ + nbOpListFor Δ) (nbOpFor A₁) ⟩
                                nbOpFor A₁ + (nbOpFor A₂ + nbOpListFor Δ)
                                  ≡⟨ sym (+-assoc (nbOpFor A₁) (nbOpFor A₂) (nbOpListFor Δ)) ⟩
                                nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ ∎)
                              a≤a+b))))))))))
    cPpFunGiveAtomicLeaves {head (T , (D ∷ A))} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] | Δ ∷ (A₁ +S A₂) | [ eq₃ ] =
      cPpFunGiveAtomicLeaves
          {head (T , (Δ ∷ A₁ ∷ A₂))}
          (HeadOrdered (T , (Δ ∷ A₁ ∷ A₂)))
          (rs
            (complexity (head (T , (Δ ∷ A₁ ∷ A₂))))
            (cong-<L-r
              {complexity (head (T , (Δ ∷ (A₁ +S A₂))))}
              (begin
                complexity (head (T , (Δ ∷ (A₁ +S A₂))))
                  ≡⟨ complexityHead (T , Δ ∷ (A₁ +S A₂)) ⟩
                (nbOpSeq (T , (Δ ∷ (A₁ +S A₂))) , 1)
                  ≡⟨ cong
                       (λ x -> (x + nbOpListFor (Δ ∷ (A₁ +S A₂)) , 1))
                       eq₁ ⟩
                (nbOpListFor (Δ ∷ (A₁ +S A₂)) , 1)
                  ≡⟨ cong
                       (λ x -> (x , 1))
                       (ListExchangeKeepOperator
                         {Δ ∷ (A₁ +S A₂)}
                         {D ∷ A}
                         (ListExchangeCong
                           eq₃
                           (ListExchangeSym ListDoExchangeCorrect))) ⟩
                (nbOpListFor (D ∷ A) , 1)
                  ≡⟨ cong
                       (λ x -> x , 1)
                       eq₂ ⟩
                (suc nbOpD , 1)
                  ≡⟨ eq ⟩
                (maxOpG , nbMaxOp) ∎)
              (first
                (cong-≤-r
                  {suc (nbOpListFor T + nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ)}
                  (trans
                    (cong
                      suc
                      (sym
                        (trans
                          (sym (+-assoc (nbOpListFor T) (nbOpFor A₁ + nbOpFor A₂) (nbOpListFor Δ)))
                          (cong
                            (λ x -> (x + nbOpListFor Δ))
                            (sym (+-assoc (nbOpListFor T) (nbOpFor A₁) (nbOpFor A₂)))))))
                    (sa+b=a+sb {nbOpListFor T} {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ}))
                  (s≤s
                    (cong-≤-r
                      {nbOpListFor T + (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ)}
                      (trans
                        (sym
                          (+-assoc (nbOpListFor T) (nbOpFor A₁ + nbOpFor A₂) (nbOpListFor Δ)))
                        (sym
                          (cong
                            (λ x -> x + nbOpListFor Δ)
                            (+-assoc (nbOpListFor T) (nbOpFor A₁) (nbOpFor A₂)))))
                      (a≤b=>c≤d=>a+c≤b+d
                        {nbOpListFor T}
                        {nbOpListFor T}
                        {(nbOpFor A₂ + (nbOpFor A₁ + nbOpListFor Δ))}
                        {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ}
                        ≤-refl
                        (cong-≤-r
                          (trans
                            (sym
                              (+-assoc (nbOpFor A₂) (nbOpFor A₁) (nbOpListFor Δ)))
                            (cong
                              (λ x -> (x + nbOpListFor Δ))
                              (+-comm (nbOpFor A₂) (nbOpFor A₁))))
                          ≤-refl))))))))
    cPpFunGiveAtomicLeaves {head (T , (D ∷ A))} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] | Δ ∷ (A₁ ⊓S A₂) | [ eq₃ ] =
      unionAtomicIsAtomic
        (cPpFunGiveAtomicLeaves
          {head (T , (Δ ∷ A₁))}
          (HeadOrdered (T , Δ ∷ A₁))
          (rs
           (complexity (head (T , (Δ ∷ A₁))))
           (cong-<L-r
             {complexity (head (T , (Δ ∷ (A₁ ⊓S A₂))))}
             (begin
                    complexity (head (T , (Δ ∷ (A₁ ⊓S A₂))))
                      ≡⟨ complexityHead (T , Δ ∷ (A₁ ⊓S A₂)) ⟩
                    (nbOpSeq (T , (Δ ∷ (A₁ ⊓S A₂))) , 1)
                      ≡⟨ cong
                           (λ x -> (x + nbOpListFor (Δ ∷ (A₁ ⊓S A₂)) , 1))
                           eq₁ ⟩
                    nbOpListFor (Δ ∷ (A₁ ⊓S A₂)) , 1
                      ≡⟨ cong
                           (λ x -> x , 1)
                           (ListExchangeKeepOperator
                             {Δ ∷ (A₁ ⊓S A₂)}
                             {D ∷ A}
                             (ListExchangeCong
                               eq₃
                               (ListExchangeSym ListDoExchangeCorrect))) ⟩
                    nbOpListFor (D ∷ A) , 1
                      ≡⟨ cong
                           (λ x -> x , 1)
                           eq₂ ⟩
                    suc nbOpD , 1
                      ≡⟨ eq ⟩
                    maxOpG , nbMaxOp ∎)
             (first
               (cong-≤-l
                        {suc (nbOpFor A₁ + nbOpListFor Δ)}
                        (cong
                          (λ x -> suc (x + (nbOpFor A₁ + nbOpListFor Δ)))
                          (sym eq₁))
                        (cong-≤-r
                          {suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ)}
                          (cong
                            (λ x -> x + suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ))
                            (sym eq₁))
                          (s≤s
                            (cong-≤-r
                              {nbOpFor A₁ + nbOpListFor Δ + nbOpFor A₂}
                              (begin
                                nbOpFor A₁ + nbOpListFor Δ + nbOpFor A₂
                                  ≡⟨ +-assoc (nbOpFor A₁) (nbOpListFor Δ) (nbOpFor A₂) ⟩
                                nbOpFor A₁ + (nbOpListFor Δ + nbOpFor A₂)
                                  ≡⟨ cong
                                       (λ x -> nbOpFor A₁ + x)
                                       (+-comm (nbOpListFor Δ) (nbOpFor A₂)) ⟩
                                nbOpFor A₁ + (nbOpFor A₂ + nbOpListFor Δ)
                                  ≡⟨ sym (+-assoc (nbOpFor A₁) (nbOpFor A₂) (nbOpListFor Δ)) ⟩
                                nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ ∎)
                              a≤a+b))))))))
        (cPpFunGiveAtomicLeaves
          {head (T , Δ ∷ A₂)}
          (HeadOrdered (T , Δ ∷ A₂))
          (rs
            (complexity (head (T , Δ ∷ A₂)))
            (cong-<L-r
              {complexity (head (T , (Δ ∷ (A₁ ⊓S A₂))))}
              (begin
                complexity (head (T , (Δ ∷ (A₁ ⊓S A₂))))
                  ≡⟨ complexityHead (T , Δ ∷ (A₁ ⊓S A₂)) ⟩
                (nbOpSeq (T , (Δ ∷ (A₁ ⊓S A₂))) , 1)
                  ≡⟨ cong
                       (λ x -> (x + nbOpListFor (Δ ∷ (A₁ ⊓S A₂)) , 1))
                       eq₁ ⟩
                nbOpListFor (Δ ∷ (A₁ ⊓S A₂)) , 1
                  ≡⟨ cong
                       (λ x -> x , 1)
                       (ListExchangeKeepOperator
                         {Δ ∷ (A₁ ⊓S A₂)}
                         {D ∷ A}
                         (ListExchangeCong
                           eq₃
                           (ListExchangeSym ListDoExchangeCorrect))) ⟩
                nbOpListFor (D ∷ A) , 1
                  ≡⟨ cong
                       (λ x -> x , 1)
                       eq₂ ⟩
                suc nbOpD , 1
                  ≡⟨ eq ⟩
                maxOpG , nbMaxOp ∎)
                (first
                  (cong-≤-l
                        {suc (nbOpFor A₂ + nbOpListFor Δ)}
                        (cong
                          (λ x -> suc (x + (nbOpFor A₂ + nbOpListFor Δ)))
                          (sym eq₁))
                        (cong-≤-r
                          {suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ)}
                          (cong
                            (λ x -> x + suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ))
                            (sym eq₁))
                          (s≤s
                            (cong-≤-r
                              {nbOpFor A₂ + nbOpListFor Δ + nbOpFor A₁}
                              (begin
                                nbOpFor A₂ + nbOpListFor Δ + nbOpFor A₁
                                  ≡⟨ +-comm (nbOpFor A₂ + nbOpListFor Δ) (nbOpFor A₁) ⟩
                                nbOpFor A₁ + (nbOpFor A₂ + nbOpListFor Δ)
                                  ≡⟨ sym (+-assoc (nbOpFor A₁) (nbOpFor A₂) (nbOpListFor Δ)) ⟩
                                nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ ∎)
                              a≤a+b))))))))
    cPpFunGiveAtomicLeaves {head (T , (D ∷ A))} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] | Δ ∷ (-S A₁) | [ eq₃ ] =
      cPpFunGiveAtomicLeaves
          (HeadOrdered (T ∷ A₁ , Δ))
          (rs
            (complexity (head (T ∷ A₁ , Δ)))
            (cong-<L-r
              {complexity (head (T , (Δ ∷ (-S A₁))))}
              (begin
                complexity (head (T , (Δ ∷ (-S A₁))))
                  ≡⟨ complexityHead (T , Δ ∷ (-S A₁)) ⟩
                (nbOpSeq (T , (Δ ∷ (-S A₁))) , 1)
                  ≡⟨ cong
                       (λ x -> (x + nbOpListFor (Δ ∷ (-S A₁)) , 1))
                       eq₁ ⟩
                nbOpListFor (Δ ∷ (-S A₁)) , 1
                  ≡⟨ cong
                       (λ x -> x , 1)
                       (ListExchangeKeepOperator
                         {Δ ∷ (-S A₁)}
                         {D ∷ A}
                         (ListExchangeCong
                           eq₃
                           (ListExchangeSym ListDoExchangeCorrect))) ⟩
                nbOpListFor (D ∷ A) , 1
                  ≡⟨ cong
                       (λ x -> x , 1)
                       eq₂ ⟩
                suc nbOpD , 1
                  ≡⟨ eq ⟩
                maxOpG , nbMaxOp ∎)
              (first
                (cong-≤-l
                  {suc (nbOpFor A₁ + nbOpListFor Δ)}
                  (cong
                    suc
                    (cong
                      (λ x -> x + nbOpListFor Δ)
                      (trans
                        (cong (λ x -> x + nbOpFor A₁) (sym eq₁))
                        (+-comm (nbOpListFor T) (nbOpFor A₁)))))
                  (cong-≤-r
                    (begin
                      suc (nbOpFor A₁ + nbOpListFor Δ)
                        ≡⟨ cong
                             (λ x -> suc (x + (nbOpFor A₁ + nbOpListFor Δ)))
                             (sym eq₁) ⟩
                      suc (nbOpListFor T + (nbOpFor A₁ + nbOpListFor Δ))
                        ≡⟨ sa+b=a+sb {nbOpListFor T} ⟩
                      nbOpListFor T + suc (nbOpFor A₁ + nbOpListFor Δ) ∎)
                    ≤-refl)))))
    cPpFunGiveAtomicLeaves {head ([] , D)} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] =
      ⊥-elim (notSucEqZero (sym eq₁))
    cPpFunGiveAtomicLeaves {head ((T ∷ A) , D)} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] with ListDoExchange (T ∷ A) | inspect ListDoExchange (T ∷ A)
    cPpFunGiveAtomicLeaves {head ((T ∷ A) , D)} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] | [] | [ eq₂ ] =
      ⊥-elim (¬ListDoExchangeΓ∷A=[] T A eq₂)
    cPpFunGiveAtomicLeaves {head ((T ∷ A) , D)} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] | Γ ∷ varAG x | [ eq₂ ] =
      ⊥-elim
        (ListDoExchangeNoVar
          {T ∷ A}
          (λ x₁ -> notSucEqZero (trans (sym eq₁) x₁))
          Γ
          x
          eq₂)
    cPpFunGiveAtomicLeaves {head ((T ∷ A) , D)} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] | Γ ∷ botAG | [ eq₂ ] =
      cPpFunGiveAtomicLeaves
          (HeadOrdered (Γ , D))
          (rs
            (complexity (head (Γ , D)))
            (cong-<L-r
              {complexity (head (Γ ∷ botAG , D))}
              (begin
                complexity (head ((Γ ∷ botAG) , D))
                  ≡⟨ complexityHead (Γ ∷ botAG , D) ⟩
                nbOpSeq (Γ ∷ botAG , D) , 1
                  ≡⟨ cong
                       (λ x -> (x + nbOpListFor D) , 1)
                       {suc (nbOpListFor Γ)}
                       {nbOpFor A + nbOpListFor T}
                       (ListExchangeKeepOperator
                         {Γ ∷ botAG}
                         {T ∷ A}
                         (ListExchangeCong
                           eq₂
                           (ListExchangeSym ListDoExchangeCorrect))) ⟩
                nbOpSeq ((T ∷ A) , D) , 1
                  ≡⟨ cong
                       (λ x -> (x + nbOpListFor D) , 1)
                       eq₁ ⟩
                (suc nbOpT + nbOpListFor D) , 1
                  ≡⟨ eq ⟩
                maxOpG , nbMaxOp ∎)
              (first
                ≤-refl)))
    cPpFunGiveAtomicLeaves {head ((T ∷ A) , D)} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] | Γ ∷ (A₁ ⊔S A₂) | [ eq₂ ] = 
      unionAtomicIsAtomic
        (cPpFunGiveAtomicLeaves
          (HeadOrdered (Γ ∷ A₁ , D))
          (rs
            (complexity (head (Γ ∷ A₁ , D)))
            (cong-<L-r
              {complexity (head (Γ ∷ (A₁ ⊔S A₂) , D))}
              (begin
                complexity (head ((Γ ∷ (A₁ ⊔S A₂)) , D))
                  ≡⟨ complexityHead (Γ ∷ (A₁ ⊔S A₂) , D) ⟩
                nbOpSeq (Γ ∷ (A₁ ⊔S A₂) , D) , 1
                  ≡⟨ cong
                       (λ x -> (x + nbOpListFor D) , 1)
                       {suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ)}
                       {nbOpFor A + nbOpListFor T}
                       (ListExchangeKeepOperator
                         {Γ ∷ (A₁ ⊔S A₂)}
                         {T ∷ A}
                         (ListExchangeCong
                           eq₂
                           (ListExchangeSym ListDoExchangeCorrect))) ⟩
                nbOpSeq ((T ∷ A) , D) , 1
                  ≡⟨ cong
                       (λ x -> (x + nbOpListFor D) , 1)
                       eq₁ ⟩
                (suc nbOpT + nbOpListFor D) , 1
                  ≡⟨ eq ⟩
                maxOpG , nbMaxOp ∎)
              (first
                (s≤s
                  (a≤b=>c≤d=>a+c≤b+d
                    {nbOpFor A₁ + nbOpListFor Γ}
                    {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ}
                    {nbOpListFor D}
                    {nbOpListFor D}
                    (a≤b=>c≤d=>a+c≤b+d
                      {nbOpFor A₁}
                      {nbOpFor A₁ + nbOpFor A₂}
                      {nbOpListFor Γ}
                      {nbOpListFor Γ}
                      a≤a+b
                      ≤-refl)
                    ≤-refl))))))
        (cPpFunGiveAtomicLeaves
          (HeadOrdered (Γ ∷ A₂ , D))
          (rs
            (complexity (head (Γ ∷ A₂ , D)))
            (cong-<L-r
              {complexity (head (Γ ∷ (A₁ ⊔S A₂) , D))}
              (begin
                complexity (head ((Γ ∷ (A₁ ⊔S A₂)) , D))
                  ≡⟨ complexityHead (Γ ∷ (A₁ ⊔S A₂) , D) ⟩
                nbOpSeq (Γ ∷ (A₁ ⊔S A₂) , D) , 1
                  ≡⟨ cong
                       (λ x -> (x + nbOpListFor D) , 1)
                       {suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ)}
                       {nbOpFor A + nbOpListFor T}
                       (ListExchangeKeepOperator
                         {Γ ∷ (A₁ ⊔S A₂)}
                         {T ∷ A}
                         (ListExchangeCong
                           eq₂
                           (ListExchangeSym ListDoExchangeCorrect))) ⟩
                nbOpSeq ((T ∷ A) , D) , 1
                  ≡⟨ cong
                       (λ x -> (x + nbOpListFor D) , 1)
                       eq₁ ⟩
                (suc nbOpT + nbOpListFor D) , 1
                  ≡⟨ eq ⟩
                maxOpG , nbMaxOp ∎)
              (first
                (s≤s
                  (a≤b=>c≤d=>a+c≤b+d
                    {nbOpFor A₂ + nbOpListFor Γ}
                    {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ}
                    {nbOpListFor D}
                    {nbOpListFor D}
                    (a≤b=>c≤d=>a+c≤b+d
                      {nbOpFor A₂}
                      {nbOpFor A₁ + nbOpFor A₂}
                      {nbOpListFor Γ}
                      {nbOpListFor Γ}
                      (cong-≤-r
                        (+-comm (nbOpFor A₂) (nbOpFor A₁))
                        a≤a+b)
                      ≤-refl)
                    ≤-refl))))))
    cPpFunGiveAtomicLeaves {head ((T ∷ A) , D)} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] | Γ ∷ (A₁ +S A₂) | [ eq₂ ] =
      cPpFunGiveAtomicLeaves
          {head ((Γ ∷ A₁ ∷ A₂) , D)}
          (HeadOrdered ((Γ ∷ A₁ ∷ A₂) , D))
          (rs
            (complexity (head ((Γ ∷ A₁ ∷ A₂) , D)))
            (cong-<L-r
              {complexity (head (Γ ∷ (A₁ +S A₂) , D))}
              (begin
                complexity (head ((Γ ∷ (A₁ +S A₂)) , D))
                  ≡⟨ complexityHead (Γ ∷ (A₁ +S A₂) , D) ⟩
                nbOpSeq (Γ ∷ (A₁ +S A₂) , D) , 1
                  ≡⟨ cong
                       (λ x -> (x + nbOpListFor D) , 1)
                       {suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ)}
                       {nbOpFor A + nbOpListFor T}
                       (ListExchangeKeepOperator
                         {Γ ∷ (A₁ +S A₂)}
                         {T ∷ A}
                         (ListExchangeCong
                           eq₂
                           (ListExchangeSym ListDoExchangeCorrect))) ⟩
                nbOpSeq ((T ∷ A) , D) , 1
                  ≡⟨ cong
                       (λ x -> (x + nbOpListFor D) , 1)
                       eq₁ ⟩
                (suc nbOpT + nbOpListFor D) , 1
                  ≡⟨ eq ⟩
                maxOpG , nbMaxOp ∎)
              (first
                (a≤b=>c≤d=>a+c≤b+d
                  {suc (nbOpFor A₂ + (nbOpFor A₁ + nbOpListFor Γ))}
                  {suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ)}
                  {nbOpListFor D}
                  {nbOpListFor D}
                  (s≤s
                    (cong-≤-l
                      (begin
                        nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ
                          ≡⟨ cong
                               (λ x -> x + nbOpListFor Γ)
                               (+-comm (nbOpFor A₁) (nbOpFor A₂)) ⟩
                        nbOpFor A₂ + nbOpFor A₁ + nbOpListFor Γ
                          ≡⟨ +-assoc (nbOpFor A₂) (nbOpFor A₁) (nbOpListFor Γ) ⟩
                        nbOpFor A₂ + (nbOpFor A₁ + nbOpListFor Γ) ∎)
                      ≤-refl))
                  ≤-refl))))
    cPpFunGiveAtomicLeaves {head ((T ∷ A) , D)} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] | Γ ∷ (A₁ ⊓S A₂) | [ eq₂ ] =
      cPpFunGiveAtomicLeaves
            {insert (head (Γ ∷ A₁ , D)) (Γ ∷ A₂ , D)}
            (insertKeepOrder
              {head (Γ ∷ A₁ , D)}
              {(Γ ∷ A₂) , D}
              (HeadOrdered (Γ ∷ A₁ , D)))
            (rs
              (complexity (insert (head (Γ ∷ A₁ , D)) (Γ ∷ A₂ , D)))
              (cong-<L-r
                {complexity (head (Γ ∷ (A₁ ⊓S A₂) , D))}
                (begin
                  complexity (head ((Γ ∷ (A₁ ⊓S A₂)) , D))
                    ≡⟨ complexityHead (Γ ∷ (A₁ ⊓S A₂) , D) ⟩
                  nbOpSeq (Γ ∷ (A₁ ⊓S A₂) , D) , 1
                    ≡⟨ cong
                         (λ x -> (x + nbOpListFor D) , 1)
                         {suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ)}
                         {nbOpFor A + nbOpListFor T}
                         (ListExchangeKeepOperator
                           {Γ ∷ (A₁ ⊓S A₂)}
                           {T ∷ A}
                           (ListExchangeCong
                             eq₂
                             (ListExchangeSym ListDoExchangeCorrect))) ⟩
                  nbOpSeq ((T ∷ A) , D) , 1
                    ≡⟨ cong
                         (λ x -> (x + nbOpListFor D) , 1)
                         eq₁ ⟩
                  (suc nbOpT + nbOpListFor D) , 1
                    ≡⟨ eq ⟩
                  maxOpG , nbMaxOp ∎)
                (cong-<L-l
                  {complexity (head (Γ ∷ A₁ , D) ∣ (Γ ∷ A₂ , D))}
                  (ExchangeKeepComplexity
                    (insertDoExchange
                      (head (Γ ∷ A₁ , D))
                      (Γ ∷ A₂ , D)))
                  (first
                    (s≤s
                      (⊔-≤
                        {nbOpFor A₁ + nbOpListFor Γ + nbOpListFor D}
                        {nbOpFor A₂ + nbOpListFor Γ + nbOpListFor D}
                        {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ + nbOpListFor D}
                        (a≤b=>c≤d=>a+c≤b+d
                          {nbOpFor A₁ + nbOpListFor Γ}
                          {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ}
                          {nbOpListFor D}
                          {nbOpListFor D}
                          (a≤b=>c≤d=>a+c≤b+d
                            {nbOpFor A₁}
                            {nbOpFor A₁ + nbOpFor A₂}
                            {nbOpListFor Γ}
                            {nbOpListFor Γ}
                            a≤a+b
                            ≤-refl)
                          ≤-refl)
                        (a≤b=>c≤d=>a+c≤b+d
                          {nbOpFor A₂ + nbOpListFor Γ}
                          {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ}
                          {nbOpListFor D}
                          {nbOpListFor D}
                          (a≤b=>c≤d=>a+c≤b+d
                            {nbOpFor A₂}
                            {nbOpFor A₁ + nbOpFor A₂}
                            {nbOpListFor Γ}
                            {nbOpListFor Γ}
                            (cong-≤-r
                              (+-comm (nbOpFor A₂) (nbOpFor A₁))
                              a≤a+b)
                            ≤-refl)
                          ≤-refl)))))))
    cPpFunGiveAtomicLeaves {head ((T ∷ A) , D)} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] | Γ ∷ (-S A₁) | [ eq₂ ] =
      cPpFunGiveAtomicLeaves
          (HeadOrdered (Γ , (D ∷ A₁)))
          (rs
            (complexity (head (Γ , (D ∷ A₁))))
            (cong-<L-r
              {complexity (head (Γ ∷ (-S A₁) , D))}
              (begin
                complexity (head ((Γ ∷ (-S A₁)) , D))
                  ≡⟨ complexityHead
                       (Γ ∷ (-S A₁) , D) ⟩
                nbOpSeq (Γ ∷ (-S A₁) , D) , 1
                  ≡⟨ cong
                       (λ x -> (x + nbOpListFor D) , 1)
                       (ListExchangeKeepOperator
                         {Γ ∷ (-S A₁)}
                         {T ∷ A}
                         (ListExchangeCong
                           eq₂
                           (ListExchangeSym ListDoExchangeCorrect))) ⟩
                nbOpSeq (T ∷ A , D) , 1
                  ≡⟨ cong
                       (λ x -> (x + nbOpListFor D) , 1)
                       eq₁ ⟩
                suc nbOpT + nbOpListFor D , 1
                  ≡⟨ eq ⟩
                maxOpG , nbMaxOp ∎)
              (first
                (s≤s
                  (cong-≤-r
                    {nbOpListFor Γ + (nbOpFor A₁ + nbOpListFor D)}
                    (begin
                      nbOpListFor Γ + (nbOpFor A₁ + nbOpListFor D)
                        ≡⟨ sym (+-assoc (nbOpListFor Γ) (nbOpFor A₁) (nbOpListFor D)) ⟩
                      nbOpListFor Γ + nbOpFor A₁ + nbOpListFor D
                        ≡⟨ cong
                             (λ x -> x + nbOpListFor D)
                             (+-comm (nbOpListFor Γ) (nbOpFor A₁)) ⟩
                      nbOpFor A₁ + nbOpListFor Γ + nbOpListFor D ∎)
                    ≤-refl)))))
    cPpFunGiveAtomicLeaves {head (T , D)} OG (acc rs) | maxOpG , nbMaxOp | [ eq ] | no ¬p =
      ⊥-elim (¬p refl)
    cPpFunGiveAtomicLeaves {G ∣ H} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] with nbOpSeq H ≡? (maxOp G ⊔ nbOpSeq H)
    cPpFunGiveAtomicLeaves {G ∣ (T , D)} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p with nbOpListFor T | inspect nbOpListFor T
    cPpFunGiveAtomicLeaves {G ∣ (T , D)} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] with nbOpListFor D | inspect nbOpListFor D
    cPpFunGiveAtomicLeaves {G ∣ (T , D)} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | zero | [ eq₂ ] =
      atomicConsH
        atomic[]H
        (trans
          (cong
            (λ x -> maxOp G ⊔ x)
            (trans
              (cong
                (λ x -> x + nbOpListFor D)
                eq₁)
              eq₂))
          (sym p))
    cPpFunGiveAtomicLeaves {G ∣ (T , [])} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] =
      ⊥-elim (notSucEqZero (sym eq₂))
    cPpFunGiveAtomicLeaves {G ∣ (T , (D ∷ A))} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] with ListDoExchange (D ∷ A) | inspect ListDoExchange (D ∷ A)
    cPpFunGiveAtomicLeaves {G ∣ (T , (D ∷ A))} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] | [] | [ eq₃ ] = 
      ⊥-elim (¬ListDoExchangeΓ∷A=[] D A eq₃)
    cPpFunGiveAtomicLeaves {G ∣ (T , (D ∷ A))} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] | Δ ∷ varAG x₁ | [ eq₃ ] =
      ⊥-elim
        (ListDoExchangeNoVar
          {D ∷ A}
          (λ x₂ -> notSucEqZero (trans (sym eq₂) x₂))
          Δ
          x₁
          eq₃)
    cPpFunGiveAtomicLeaves {G ∣ (T , (D ∷ A))} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] | Δ ∷ botAG | [ eq₃ ] = 
      cPpFunGiveAtomicLeaves
            {insert G (T , Δ)}
            (insertKeepOrder
              OG)
            (rs
              (complexity (insert G (T , Δ)))
              (cong-<L-r
                {complexity (G ∣ (T , Δ ∷ botAG))}
                (begin
                  complexity (G ∣ (T , (Δ ∷ botAG)))
                    ≡⟨ ListExchangeRKeepComplexity
                         G
                         T
                         (Δ ∷ botAG)
                         (D ∷ A)
                         (ListExchangeCong
                           eq₃
                           (ListExchangeSym ListDoExchangeCorrect)) ⟩
                  complexity (G ∣ (T , (D ∷ A)))
                    ≡⟨ unfoldComplexity
                         G
                         (T , (D ∷ A))
                         (cong-≤-r
                           {suc nbOpD}
                           (sym
                             (trans
                               (cong
                                 (λ x -> x + (nbOpFor A + nbOpListFor D))
                                 eq₁)
                               eq₂))
                           x) ⟩
                  (maxOp G ⊔ (nbOpListFor T + (nbOpFor A + nbOpListFor D)), suc (nbSeqCompl G (maxOp G ⊔ (nbOpListFor T + (nbOpFor A + nbOpListFor D)))))
                    ≡⟨ cong
                         (λ x -> (maxOp G ⊔ x , suc (nbSeqCompl G (maxOp G ⊔ x))))
                         {nbOpListFor T + (nbOpFor A + nbOpListFor D)}
                         {suc nbOpD}
                         (trans
                           (cong
                             (λ x -> x + (nbOpFor A + nbOpListFor D))
                             eq₁)
                           eq₂) ⟩
                  (maxOp G ⊔ suc nbOpD , suc (nbSeqCompl G (maxOp G ⊔ suc nbOpD)))
                    ≡⟨ eq ⟩
                  (maxOpG , nbMaxOp) ∎)
                (cong-<L-l
                  {complexity (G ∣ (T , Δ))}
                  (ExchangeKeepComplexity
                    (insertDoExchange
                      G
                      (T , Δ)))
                  (complexityDecreasing
                    G
                    (T , Δ)
                    (T , Δ ∷ botAG)
                    (cong-≤-r
                      (sa+b=a+sb {nbOpListFor T} {nbOpListFor Δ})
                      ≤-refl)
                    (a≤b=>c≤d=>a+c≤b+d
                      {0}
                      {nbOpListFor T}
                      {maxOp G}
                      {suc (nbOpListFor Δ)}
                      (cong-≤-r
                        (sym eq₁)
                        ≤-refl)
                      (cong-≤-r
                        (sym
                          (trans
                            (ListExchangeKeepOperator
                              {Δ ∷ botAG}
                              {D ∷ A}
                              (ListExchangeCong
                                eq₃
                                (ListExchangeSym ListDoExchangeCorrect)))
                            eq₂))
                        x))))))
    cPpFunGiveAtomicLeaves {G ∣ (T , (D ∷ A))} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] | Δ ∷ (A₁ ⊔S A₂) | [ eq₃ ] =
      cPpFunGiveAtomicLeaves
            {insert (insert G (T , (Δ ∷ A₁))) (T , (Δ ∷ A₂))}
            (insertKeepOrder
              {insert G (T , Δ ∷ A₁)}
              (insertKeepOrder
                OG))
            (rs
              (complexity (insert (insert G (T , (Δ ∷ A₁))) (T , (Δ ∷ A₂))))
              (cong-<L-r
                {complexity (G ∣ (T , Δ ∷ (A₁ ⊔S A₂)))}
                (begin
                  complexity (G ∣ (T , (Δ ∷ (A₁ ⊔S A₂))))
                    ≡⟨ ListExchangeRKeepComplexity
                         G
                         T
                         (Δ ∷ (A₁ ⊔S A₂))
                         (D ∷ A)
                         (ListExchangeCong
                           eq₃
                           (ListExchangeSym ListDoExchangeCorrect)) ⟩
                  complexity (G ∣ (T , (D ∷ A)))
                    ≡⟨ unfoldComplexity
                         G
                         (T , (D ∷ A))
                         (cong-≤-r
                           {suc nbOpD}
                           (sym
                             (trans
                               (cong
                                 (λ x -> x + (nbOpFor A + nbOpListFor D))
                                 eq₁)
                               eq₂))
                           x) ⟩
                  (maxOp G ⊔ (nbOpListFor T + (nbOpFor A + nbOpListFor D)), suc (nbSeqCompl G (maxOp G ⊔ (nbOpListFor T + (nbOpFor A + nbOpListFor D)))))
                    ≡⟨ cong
                         (λ x -> (maxOp G ⊔ x , suc (nbSeqCompl G (maxOp G ⊔ x))))
                         {nbOpListFor T + (nbOpFor A + nbOpListFor D)}
                         {suc nbOpD}
                         (trans
                           (cong
                             (λ x -> x + (nbOpFor A + nbOpListFor D))
                             eq₁)
                           eq₂) ⟩
                  (maxOp G ⊔ suc nbOpD , suc (nbSeqCompl G (maxOp G ⊔ suc nbOpD)))
                    ≡⟨ eq ⟩
                  (maxOpG , nbMaxOp) ∎)
               (cong-<L-l
                 {complexity (G ∣ (T , Δ ∷ A₁) ∣ (T , Δ ∷ A₂))}
                 (ExchangeKeepComplexity
                   {G ∣ (T , Δ ∷ A₁) ∣ (T , Δ ∷ A₂)}
                   {insert (insert G (T , Δ ∷ A₁)) (T , Δ ∷ A₂)}
                   (transHE
                     (indHE
                       (G ∣ (T , (Δ ∷ A₁)))
                       (insert G (T , Δ ∷ A₁))
                       (insertDoExchange
                         G
                         (T , Δ ∷ A₁)))
                     (insertDoExchange
                       (insert G (T , Δ ∷ A₁))
                       (T , Δ ∷ A₂))))
                 (complexityDecMaxR
                   G
                   T
                   Δ
                   A₁
                   A₂
                   (cong-≤-r
                     (begin
                       suc nbOpD
                         ≡⟨ sym eq₂ ⟩
                       nbOpFor A + nbOpListFor D
                         ≡⟨ ListExchangeKeepOperator
                              {D ∷ A}
                              {Δ ∷ (A₁ ⊔S A₂)}
                              (ListExchangeSym
                                (ListExchangeCong
                                  eq₃
                                  (ListExchangeSym ListDoExchangeCorrect))) ⟩
                       suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ)
                         ≡⟨ cong
                              (λ x -> x + suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ))
                              (sym eq₁) ⟩
                       nbOpListFor T + suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ) ∎)
                     x)))))
    cPpFunGiveAtomicLeaves {G ∣ (T , (D ∷ A))} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] | Δ ∷ (A₁ +S A₂) | [ eq₃ ] =
      cPpFunGiveAtomicLeaves
            {insert G (T , (Δ ∷ A₁ ∷ A₂))}
            (insertKeepOrder OG)
            (rs
              (complexity (insert G (T , (Δ ∷ A₁ ∷ A₂))))
              (cong-<L-r
                {complexity (G ∣ (T , Δ ∷ (A₁ +S A₂)))}
                (begin
                  complexity (G ∣ (T , (Δ ∷ (A₁ +S A₂))))
                    ≡⟨ ListExchangeRKeepComplexity
                         G
                         T
                         (Δ ∷ (A₁ +S A₂))
                         (D ∷ A)
                         (ListExchangeCong
                           eq₃
                           (ListExchangeSym ListDoExchangeCorrect)) ⟩
                  complexity (G ∣ (T , (D ∷ A)))
                    ≡⟨ unfoldComplexity
                         G
                         (T , (D ∷ A))
                         (cong-≤-r
                           {suc nbOpD}
                           (sym
                             (trans
                               (cong
                                 (λ x -> x + (nbOpFor A + nbOpListFor D))
                                 eq₁)
                               eq₂))
                           x) ⟩
                  (maxOp G ⊔ (nbOpListFor T + (nbOpFor A + nbOpListFor D)), suc (nbSeqCompl G (maxOp G ⊔ (nbOpListFor T + (nbOpFor A + nbOpListFor D)))))
                    ≡⟨ cong
                         (λ x -> (maxOp G ⊔ x , suc (nbSeqCompl G (maxOp G ⊔ x))))
                         {nbOpListFor T + (nbOpFor A + nbOpListFor D)}
                         {suc nbOpD}
                         (trans
                           (cong
                             (λ x -> x + (nbOpFor A + nbOpListFor D))
                             eq₁)
                           eq₂) ⟩
                  (maxOp G ⊔ suc nbOpD , suc (nbSeqCompl G (maxOp G ⊔ suc nbOpD)))
                    ≡⟨ eq ⟩
                  (maxOpG , nbMaxOp) ∎)
                (cong-<L-l
                  {complexity (G ∣ (T , (Δ ∷ A₁ ∷ A₂)))}
                  (ExchangeKeepComplexity
                    (insertDoExchange G (T , (Δ ∷ A₁ ∷ A₂))))
                  (complexityDecreasing
                    G
                    (T , (Δ ∷ A₁ ∷ A₂))
                    (T , (Δ ∷ (A₁ +S A₂)))
                    (cong-≤-r
                      (sa+b=a+sb {nbOpListFor T} {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ})
                      (s≤s
                        (a≤b=>c≤d=>a+c≤b+d
                          {nbOpListFor T}
                          {nbOpListFor T}
                          {nbOpFor A₂ + (nbOpFor A₁ + nbOpListFor Δ)}
                          {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ}
                          ≤-refl
                          (cong-≤-l
                            {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ}
                            (trans
                              (cong
                                (λ x -> x + nbOpListFor Δ)
                                (+-comm (nbOpFor A₁) (nbOpFor A₂)))
                              (+-assoc (nbOpFor A₂) (nbOpFor A₁) (nbOpListFor Δ)))
                            ≤-refl))))
                    (cong-≤-r
                      (sym (
                        trans
                          (cong
                            (λ x -> nbOpListFor T + x)
                            (ListExchangeKeepOperator
                              {Δ ∷ (A₁ +S A₂)}
                              {D ∷ A}
                              (ListExchangeCong
                                eq₃
                                (ListExchangeSym ListDoExchangeCorrect))))
                          (trans
                            (cong
                              (λ x -> x + (nbOpFor A + nbOpListFor D))
                              eq₁)
                            eq₂)))
                      x)))))
    cPpFunGiveAtomicLeaves {G ∣ (T , (D ∷ A))} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] | Δ ∷ (A₁ ⊓S A₂) | [ eq₃ ] =
      unionAtomicIsAtomic
        (cPpFunGiveAtomicLeaves
            (insertKeepOrder OG)
            (rs
              (complexity (insert G (T , (Δ ∷ A₁))))
              (cong-<L-r
                {complexity (G ∣ (T , Δ ∷ (A₁ ⊓S A₂)))}
                (begin
                  complexity (G ∣ (T , (Δ ∷ (A₁ ⊓S A₂))))
                    ≡⟨ ListExchangeRKeepComplexity
                         G
                         T
                         (Δ ∷ (A₁ ⊓S A₂))
                         (D ∷ A)
                         (ListExchangeCong
                           eq₃
                           (ListExchangeSym ListDoExchangeCorrect)) ⟩
                  complexity (G ∣ (T , (D ∷ A)))
                    ≡⟨ unfoldComplexity
                         G
                         (T , (D ∷ A))
                         (cong-≤-r
                           {suc nbOpD}
                           (sym
                             (trans
                               (cong
                                 (λ x -> x + (nbOpFor A + nbOpListFor D))
                                 eq₁)
                               eq₂))
                           x) ⟩
                  (maxOp G ⊔ (nbOpListFor T + (nbOpFor A + nbOpListFor D)), suc (nbSeqCompl G (maxOp G ⊔ (nbOpListFor T + (nbOpFor A + nbOpListFor D)))))
                    ≡⟨ cong
                         (λ x -> (maxOp G ⊔ x , suc (nbSeqCompl G (maxOp G ⊔ x))))
                         {nbOpListFor T + (nbOpFor A + nbOpListFor D)}
                         {suc nbOpD}
                         (trans
                           (cong
                             (λ x -> x + (nbOpFor A + nbOpListFor D))
                             eq₁)
                           eq₂) ⟩
                  (maxOp G ⊔ suc nbOpD , suc (nbSeqCompl G (maxOp G ⊔ suc nbOpD)))
                    ≡⟨ eq ⟩
                  (maxOpG , nbMaxOp) ∎)
                (cong-<L-l
                  {complexity (G ∣ (T , Δ ∷ A₁))}
                  (ExchangeKeepComplexity
                    (insertDoExchange
                      G
                      (T , Δ ∷ A₁)))
                  (complexityDecreasing
                    G
                    (T , (Δ ∷ A₁))
                    (T , (Δ ∷ (A₁ ⊓S A₂)))
                    (cong-≤-r
                      (sa+b=a+sb {nbOpListFor T} {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ})
                      (s≤s
                        (a≤b=>c≤d=>a+c≤b+d
                          {nbOpListFor T}
                          {nbOpListFor T}
                          {nbOpFor A₁ + nbOpListFor Δ}
                          {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ}
                          ≤-refl
                          (cong-≤-r
                            (sym (+-assoc (nbOpFor A₁) (nbOpFor A₂) (nbOpListFor Δ)))
                            (a≤b=>c≤d=>a+c≤b+d
                              {nbOpFor A₁}
                              {nbOpFor A₁}
                              {nbOpListFor Δ}
                              {nbOpFor A₂ + nbOpListFor Δ}
                              ≤-refl
                              (cong-≤-r
                                (+-comm (nbOpListFor Δ) (nbOpFor A₂))
                                a≤a+b))))))
                    (≤-trans
                      x
                      (cong-≤-l
                        eq₂
                        (cong-≤-r
                          (cong
                            (λ x -> nbOpListFor T + x)
                            (ListExchangeKeepOperator
                              {D ∷ A}
                              {Δ ∷ (A₁ ⊓S A₂)}
                              (ListExchangeSym
                                (ListExchangeCong
                                  eq₃
                                  (ListExchangeSym ListDoExchangeCorrect)))))
                          (a≤b=>c≤d=>a+c≤b+d
                            {0}
                            {nbOpListFor T}
                            {nbOpFor A + nbOpListFor D}
                            {nbOpFor A + nbOpListFor D}
                            (cong-≤-l
                              eq₁
                              ≤-refl)
                            ≤-refl)))))))))
        (cPpFunGiveAtomicLeaves
            (insertKeepOrder OG)
            (rs
              (complexity (insert G (T , (Δ ∷ A₂))))
              (cong-<L-r
                {complexity (G ∣ (T , Δ ∷ (A₁ ⊓S A₂)))}
                (begin
                  complexity (G ∣ (T , (Δ ∷ (A₁ ⊓S A₂))))
                    ≡⟨ ListExchangeRKeepComplexity
                         G
                         T
                         (Δ ∷ (A₁ ⊓S A₂))
                         (D ∷ A)
                         (ListExchangeCong
                           eq₃
                           (ListExchangeSym ListDoExchangeCorrect)) ⟩
                  complexity (G ∣ (T , (D ∷ A)))
                    ≡⟨ unfoldComplexity
                         G
                         (T , (D ∷ A))
                         (cong-≤-r
                           {suc nbOpD}
                           (sym
                             (trans
                               (cong
                                 (λ x -> x + (nbOpFor A + nbOpListFor D))
                                 eq₁)
                               eq₂))
                           x) ⟩
                  (maxOp G ⊔ (nbOpListFor T + (nbOpFor A + nbOpListFor D)), suc (nbSeqCompl G (maxOp G ⊔ (nbOpListFor T + (nbOpFor A + nbOpListFor D)))))
                    ≡⟨ cong
                         (λ x -> (maxOp G ⊔ x , suc (nbSeqCompl G (maxOp G ⊔ x))))
                         {nbOpListFor T + (nbOpFor A + nbOpListFor D)}
                         {suc nbOpD}
                         (trans
                           (cong
                             (λ x -> x + (nbOpFor A + nbOpListFor D))
                             eq₁)
                           eq₂) ⟩
                  (maxOp G ⊔ suc nbOpD , suc (nbSeqCompl G (maxOp G ⊔ suc nbOpD)))
                    ≡⟨ eq ⟩
                  (maxOpG , nbMaxOp) ∎)
                (cong-<L-l
                  {complexity (G ∣ (T , Δ ∷ A₂))}
                  (ExchangeKeepComplexity
                    (insertDoExchange
                      G
                      (T , Δ ∷ A₂)))
                  (complexityDecreasing
                    G
                    (T , (Δ ∷ A₂))
                    (T , (Δ ∷ (A₁ ⊓S A₂)))
                    (cong-≤-r
                      (sa+b=a+sb {nbOpListFor T} {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ})
                      (s≤s
                        (a≤b=>c≤d=>a+c≤b+d
                          {nbOpListFor T}
                          {nbOpListFor T}
                          {nbOpFor A₂ + nbOpListFor Δ}
                          {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Δ}
                          ≤-refl
                          (cong-≤-r
                            {nbOpFor A₂ +( nbOpFor A₁ + nbOpListFor Δ)}
                            (trans
                              (sym (+-assoc (nbOpFor A₂) (nbOpFor A₁) (nbOpListFor Δ)))
                              (cong
                                (λ x -> x + nbOpListFor Δ)
                                (+-comm (nbOpFor A₂) (nbOpFor A₁))))
                            (a≤b=>c≤d=>a+c≤b+d
                              {nbOpFor A₂}
                              {nbOpFor A₂}
                              {nbOpListFor Δ}
                              {nbOpFor A₁ + nbOpListFor Δ}
                              ≤-refl
                              (cong-≤-r
                                (+-comm (nbOpListFor Δ) (nbOpFor A₁))
                                a≤a+b))))))
                    (≤-trans
                      x
                      (cong-≤-l
                        eq₂
                        (cong-≤-r
                          (cong
                            (λ x -> nbOpListFor T + x)
                            (ListExchangeKeepOperator
                              {D ∷ A}
                              {Δ ∷ (A₁ ⊓S A₂)}
                              (ListExchangeSym
                                (ListExchangeCong
                                  eq₃
                                  (ListExchangeSym ListDoExchangeCorrect)))))
                          (a≤b=>c≤d=>a+c≤b+d
                            {0}
                            {nbOpListFor T}
                            {nbOpFor A + nbOpListFor D}
                            {nbOpFor A + nbOpListFor D}
                            (cong-≤-l
                              eq₁
                              ≤-refl)
                            ≤-refl)))))))))
    cPpFunGiveAtomicLeaves {G ∣ (T , (D ∷ A))} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | zero | [ eq₁ ] | suc nbOpD | [ eq₂ ] | Δ ∷ (-S A₁) | [ eq₃ ] = cPpFunGiveAtomicLeaves
            (insertKeepOrder OG)
            (rs
              (complexity (insert G ((T ∷ A₁) , Δ)))
              (cong-<L-r
                {complexity (G ∣ (T , Δ ∷ (-S A₁)))}
                (begin
                  complexity (G ∣ (T , (Δ ∷ (-S A₁))))
                    ≡⟨ ListExchangeRKeepComplexity
                         G
                         T
                         (Δ ∷ (-S A₁))
                         (D ∷ A)
                         (ListExchangeCong
                           eq₃
                           (ListExchangeSym ListDoExchangeCorrect)) ⟩
                  complexity (G ∣ (T , (D ∷ A)))
                    ≡⟨ unfoldComplexity
                         G
                         (T , (D ∷ A))
                         (cong-≤-r
                           {suc nbOpD}
                           (sym
                             (trans
                               (cong
                                 (λ x -> x + (nbOpFor A + nbOpListFor D))
                                 eq₁)
                               eq₂))
                           x) ⟩
                  (maxOp G ⊔ (nbOpListFor T + (nbOpFor A + nbOpListFor D)), suc (nbSeqCompl G (maxOp G ⊔ (nbOpListFor T + (nbOpFor A + nbOpListFor D)))))
                    ≡⟨ cong
                         (λ x -> (maxOp G ⊔ x , suc (nbSeqCompl G (maxOp G ⊔ x))))
                         {nbOpListFor T + (nbOpFor A + nbOpListFor D)}
                         {suc nbOpD}
                         (trans
                           (cong
                             (λ x -> x + (nbOpFor A + nbOpListFor D))
                             eq₁)
                           eq₂) ⟩
                  (maxOp G ⊔ suc nbOpD , suc (nbSeqCompl G (maxOp G ⊔ suc nbOpD)))
                    ≡⟨ eq ⟩
                  (maxOpG , nbMaxOp) ∎)
                (cong-<L-l
                  {complexity (G ∣ (T ∷ A₁ , Δ))}
                  (ExchangeKeepComplexity
                    (insertDoExchange
                      G
                      (T ∷ A₁ , Δ)))
                  (complexityDecreasing
                    G
                    (T ∷ A₁ , Δ)
                    (T , (Δ ∷ (-S A₁)))
                    (cong-≤-r
                      (begin
                        suc (nbOpFor A₁ + nbOpListFor T + nbOpListFor Δ)
                          ≡⟨ cong
                               (λ x -> suc (x + nbOpListFor Δ))
                               (+-comm (nbOpFor A₁) (nbOpListFor T)) ⟩
                        suc (nbOpListFor T + nbOpFor A₁ + nbOpListFor Δ)
                          ≡⟨ cong
                               suc
                               (+-assoc (nbOpListFor T) (nbOpFor A₁) (nbOpListFor Δ)) ⟩
                        suc (nbOpListFor T + (nbOpFor A₁ + nbOpListFor Δ))
                          ≡⟨ sa+b=a+sb {nbOpListFor T} {nbOpFor A₁ + nbOpListFor Δ} ⟩
                        nbOpListFor T + suc (nbOpFor A₁ + nbOpListFor Δ) ∎)
                      ≤-refl)
                    (≤-trans
                      x
                      (cong-≤-l
                        eq₂
                        (cong-≤-l
                          {suc (nbOpFor A₁ + nbOpListFor Δ)}
                          (ListExchangeKeepOperator
                            {Δ ∷ (-S A₁)}
                            {D ∷ A}
                            (ListExchangeCong
                              eq₃
                              (ListExchangeSym ListDoExchangeCorrect)))
                          (a≤b=>c≤d=>a+c≤b+d
                            {0}
                            {nbOpListFor T}
                            {suc (nbOpFor A₁ + nbOpListFor Δ)}
                            {suc (nbOpFor A₁ + nbOpListFor Δ)}
                            (cong-≤-l
                              eq₁
                              ≤-refl)
                            ≤-refl))))))))
    cPpFunGiveAtomicLeaves {G ∣ ([] , D)} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] =
      ⊥-elim
        (notSucEqZero (sym eq₁))
    cPpFunGiveAtomicLeaves {G ∣ ((T ∷ A) , D)} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] with ListDoExchange (T ∷ A) | inspect ListDoExchange (T ∷ A)
    cPpFunGiveAtomicLeaves {G ∣ ((T ∷ A) , D)} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] | [] | [ eq₂ ] =
      ⊥-elim
        (¬ListDoExchangeΓ∷A=[] T A eq₂)
    cPpFunGiveAtomicLeaves {G ∣ ((T ∷ A) , D)} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] | Γ ∷ varAG x₁ | [ eq₂ ] =
      ⊥-elim
        (ListDoExchangeNoVar
          {T ∷ A}
          (λ x₂ -> notSucEqZero (trans (sym eq₁) x₂))
          Γ
          x₁
          eq₂)
    cPpFunGiveAtomicLeaves {G ∣ ((T ∷ A) , D)} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] | Γ ∷ botAG | [ eq₂ ] =
      cPpFunGiveAtomicLeaves
            (insertKeepOrder OG)
            (rs
              (complexity (insert G (Γ , D)))
              (cong-<L-r
                {complexity (G ∣ (Γ ∷ botAG , D))}
                (begin
                  complexity (G ∣ ((Γ ∷ botAG) , D))
                    ≡⟨ ListExchangeLKeepComplexity
                         G
                         (Γ ∷ botAG)
                         (T ∷ A)
                         D
                         (ListExchangeCong eq₂ (ListExchangeSym ListDoExchangeCorrect)) ⟩
                  complexity (G ∣ (T ∷ A , D))
                    ≡⟨ unfoldComplexity G (T ∷ A , D) (cong-≤-r (cong (λ x -> x + nbOpListFor D) (sym eq₁)) x) ⟩
                  (maxOp G ⊔ ((nbOpFor A + nbOpListFor T) + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ ((nbOpFor A + nbOpListFor T) + nbOpListFor D))))
                    ≡⟨ cong (λ x -> (maxOp G ⊔ (x + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ (x + nbOpListFor D))))) eq₁ ⟩
                  (maxOp G ⊔ suc (nbOpT + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ suc (nbOpT + nbOpListFor D))))
                    ≡⟨ eq ⟩
                  (maxOpG , nbMaxOp) ∎)
                (cong-<L-l
                  {complexity (G ∣ (Γ , D))}
                  (ExchangeKeepComplexity
                    {(G ∣ (Γ , D))}
                    {(insert G (Γ  , D))}
                    (insertDoExchange
                      G
                      (Γ , D)))
                    (complexityDecreasing
                      G
                      (Γ , D)
                      (Γ ∷ botAG , D)
                      ≤-refl
                      (cong-≤-r
                        {suc (nbOpT + nbOpListFor D)}
                        (cong
                          (λ x -> x + nbOpListFor D)
                          (trans
                            (sym eq₁)
                            (ListExchangeKeepOperator
                              {T ∷ A}
                              {Γ ∷ botAG}
                              (ListExchangeSym
                                (ListExchangeCong
                                  eq₂
                                  (ListExchangeSym ListDoExchangeCorrect))))))
                        x)))))
    cPpFunGiveAtomicLeaves {G ∣ ((T ∷ A) , D)} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] | Γ ∷ (A₁ ⊔S A₂) | [ eq₂ ] =
      unionAtomicIsAtomic
        (cPpFunGiveAtomicLeaves
            (insertKeepOrder OG)
            (rs
              (complexity (insert G (Γ ∷ A₁ , D)))
              (cong-<L-r
                {complexity (G ∣ (Γ ∷ (A₁ ⊔S A₂) , D))}
                (begin
                  complexity (G ∣ ((Γ ∷ (A₁ ⊔S A₂)) , D))
                    ≡⟨ ListExchangeLKeepComplexity
                         G
                         (Γ ∷ (A₁ ⊔S A₂))
                         (T ∷ A)
                         D
                         (ListExchangeCong eq₂ (ListExchangeSym ListDoExchangeCorrect)) ⟩
                  complexity (G ∣ (T ∷ A , D))
                    ≡⟨ unfoldComplexity G (T ∷ A , D) (cong-≤-r (cong (λ x -> x + nbOpListFor D) (sym eq₁)) x) ⟩
                  (maxOp G ⊔ ((nbOpFor A + nbOpListFor T) + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ ((nbOpFor A + nbOpListFor T) + nbOpListFor D))))
                    ≡⟨ cong (λ x -> (maxOp G ⊔ (x + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ (x + nbOpListFor D))))) eq₁ ⟩
                  (maxOp G ⊔ suc (nbOpT + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ suc (nbOpT + nbOpListFor D))))
                    ≡⟨ eq ⟩
                  (maxOpG , nbMaxOp) ∎)
                (cong-<L-l
                  {complexity (G ∣ (Γ ∷ A₁ , D))}
                  (ExchangeKeepComplexity
                    {(G ∣ (Γ ∷ A₁ , D))}
                    {(insert G (Γ ∷ A₁  , D))}
                    (insertDoExchange
                      G
                      (Γ ∷ A₁ , D)))
                    (complexityDecreasing
                      G
                      (Γ ∷ A₁ , D)
                      (Γ ∷ (A₁ ⊔S A₂) , D)
                      (s≤s
                        (a≤b=>c≤d=>a+c≤b+d
                          {nbOpFor A₁ + nbOpListFor Γ}
                          {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ}
                          {nbOpListFor D}
                          {nbOpListFor D}
                          (a≤b=>c≤d=>a+c≤b+d
                            {nbOpFor A₁}
                            {nbOpFor A₁ + nbOpFor A₂}
                            {nbOpListFor Γ}
                            {nbOpListFor Γ}
                            (a≤a+b {nbOpFor A₁} {nbOpFor A₂})
                            ≤-refl)
                          ≤-refl))
                      ((cong-≤-r
                        {suc (nbOpT + nbOpListFor D)}
                        (cong
                          (λ x -> x + nbOpListFor D)
                          (trans
                            (sym eq₁)
                            (ListExchangeKeepOperator
                              {T ∷ A}
                              {Γ ∷ (A₁ ⊔S A₂)}
                              (ListExchangeSym
                                (ListExchangeCong
                                  eq₂
                                  (ListExchangeSym ListDoExchangeCorrect))))))
                        x)))))))
        (cPpFunGiveAtomicLeaves
            (insertKeepOrder OG)
            (rs
              (complexity (insert G (Γ ∷ A₂ , D)))
              (cong-<L-r
                {complexity (G ∣ (Γ ∷ (A₁ ⊔S A₂) , D))}
                (begin
                  complexity (G ∣ ((Γ ∷ (A₁ ⊔S A₂)) , D))
                    ≡⟨ ListExchangeLKeepComplexity
                         G
                         (Γ ∷ (A₁ ⊔S A₂))
                         (T ∷ A)
                         D
                         (ListExchangeCong eq₂ (ListExchangeSym ListDoExchangeCorrect)) ⟩
                  complexity (G ∣ (T ∷ A , D))
                    ≡⟨ unfoldComplexity G (T ∷ A , D) (cong-≤-r (cong (λ x -> x + nbOpListFor D) (sym eq₁)) x) ⟩
                  (maxOp G ⊔ ((nbOpFor A + nbOpListFor T) + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ ((nbOpFor A + nbOpListFor T) + nbOpListFor D))))
                    ≡⟨ cong (λ x -> (maxOp G ⊔ (x + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ (x + nbOpListFor D))))) eq₁ ⟩
                  (maxOp G ⊔ suc (nbOpT + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ suc (nbOpT + nbOpListFor D))))
                    ≡⟨ eq ⟩
                  (maxOpG , nbMaxOp) ∎)
                (cong-<L-l
                  {complexity (G ∣ (Γ ∷ A₂ , D))}
                  (ExchangeKeepComplexity
                    {(G ∣ (Γ ∷ A₂ , D))}
                    {(insert G (Γ ∷ A₂  , D))}
                    (insertDoExchange
                      G
                      (Γ ∷ A₂ , D)))
                    (complexityDecreasing
                      G
                      (Γ ∷ A₂ , D)
                      (Γ ∷ (A₁ ⊔S A₂) , D)
                      (s≤s
                        (a≤b=>c≤d=>a+c≤b+d
                          {nbOpFor A₂ + nbOpListFor Γ}
                          {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ}
                          {nbOpListFor D}
                          {nbOpListFor D}
                          (a≤b=>c≤d=>a+c≤b+d
                            {nbOpFor A₂}
                            {nbOpFor A₁ + nbOpFor A₂}
                            {nbOpListFor Γ}
                            {nbOpListFor Γ}
                            (cong-≤-r
                              (+-comm (nbOpFor A₂) (nbOpFor A₁))
                              (a≤a+b {nbOpFor A₂} {nbOpFor A₁}))
                            ≤-refl)
                          ≤-refl))
                      ((cong-≤-r
                        {suc (nbOpT + nbOpListFor D)}
                        (cong
                          (λ x -> x + nbOpListFor D)
                          (trans
                            (sym eq₁)
                            (ListExchangeKeepOperator
                              {T ∷ A}
                              {Γ ∷ (A₁ ⊔S A₂)}
                              (ListExchangeSym
                                (ListExchangeCong
                                  eq₂
                                  (ListExchangeSym ListDoExchangeCorrect))))))
                        x)))))))
    cPpFunGiveAtomicLeaves {G ∣ ((T ∷ A) , D)} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] | Γ ∷ (A₁ +S A₂) | [ eq₂ ] =
      cPpFunGiveAtomicLeaves
            {insert G ((Γ ∷ A₁ ∷ A₂) , D)}
            (insertKeepOrder OG)
            (rs
              (complexity (insert G ((Γ ∷ A₁ ∷ A₂) , D)))
              (cong-<L-r
                {complexity (G ∣ (Γ ∷ (A₁ +S A₂), D))}
                (begin
                  complexity (G ∣ ((Γ ∷ (A₁ +S A₂)) , D))
                    ≡⟨ ListExchangeLKeepComplexity
                         G
                         (Γ ∷ (A₁ +S A₂))
                         (T ∷ A)
                         D
                         (ListExchangeCong eq₂ (ListExchangeSym ListDoExchangeCorrect)) ⟩
                  complexity (G ∣ (T ∷ A , D))
                    ≡⟨ unfoldComplexity G (T ∷ A , D) (cong-≤-r (cong (λ x -> x + nbOpListFor D) (sym eq₁)) x) ⟩
                  (maxOp G ⊔ ((nbOpFor A + nbOpListFor T) + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ ((nbOpFor A + nbOpListFor T) + nbOpListFor D))))
                    ≡⟨ cong (λ x -> (maxOp G ⊔ (x + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ (x + nbOpListFor D))))) eq₁ ⟩
                  (maxOp G ⊔ suc (nbOpT + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ suc (nbOpT + nbOpListFor D))))
                    ≡⟨ eq ⟩
                  (maxOpG , nbMaxOp) ∎)
                (cong-<L-l
                  {complexity (G ∣ ((Γ ∷ A₁ ∷ A₂) , D))}
                  (ExchangeKeepComplexity
                    {(G ∣ ((Γ ∷ A₁ ∷ A₂) , D))}
                    {(insert G ((Γ ∷ A₁ ∷ A₂) , D))}
                    (insertDoExchange
                      G
                      (Γ ∷ A₁ ∷ A₂ , D)))
                  (complexityDecreasing
                    G
                    ((Γ ∷ A₁ ∷ A₂) , D)
                    ((Γ ∷ (A₁ +S A₂)) , D)
                    (s≤s (cong-≤-l
                           (cong
                             (λ x -> x + nbOpListFor D)
                             {nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ}
                             {nbOpFor A₂ + (nbOpFor A₁ + nbOpListFor Γ)}
                             (begin
                               nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ
                                 ≡⟨ cong
                                      (λ x -> x + nbOpListFor Γ)
                                      (+-comm (nbOpFor A₁) (nbOpFor A₂)) ⟩
                               nbOpFor A₂ + nbOpFor A₁ + nbOpListFor Γ
                                 ≡⟨ +-assoc (nbOpFor A₂) (nbOpFor A₁) (nbOpListFor Γ) ⟩
                               nbOpFor A₂ + (nbOpFor A₁ + nbOpListFor Γ) ∎))
                           ≤-refl))
                    (cong-≤-r
                      (cong
                        (λ x -> x + nbOpListFor D)
                        {suc nbOpT}
                        {suc (nbOpFor A₁ + nbOpFor A₂ + nbOpListFor Γ)}
                        (trans
                          (sym eq₁)
                          (ListExchangeKeepOperator
                            {T ∷ A}
                            {Γ ∷ (A₁ +S A₂)}
                            (ListExchangeSym (
                              ListExchangeCong
                              eq₂
                              (ListExchangeSym ListDoExchangeCorrect))))))
                      x)))))
    cPpFunGiveAtomicLeaves {G ∣ ((T ∷ A) , D)} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] | Γ ∷ (A₁ ⊓S A₂) | [ eq₂ ] =
      cPpFunGiveAtomicLeaves
            (insertKeepOrder
              (insertKeepOrder OG))
            (rs
              (complexity (insert (insert G (Γ ∷ A₁ , D)) (Γ ∷ A₂ , D)))
              (cong-<L-r
                {complexity (G ∣ (Γ ∷ (A₁ ⊓S A₂), D))}
                (begin
                  complexity (G ∣ ((Γ ∷ (A₁ ⊓S A₂)) , D))
                    ≡⟨ ListExchangeLKeepComplexity
                         G
                         (Γ ∷ (A₁ ⊓S A₂))
                         (T ∷ A)
                         D
                         (ListExchangeCong eq₂ (ListExchangeSym ListDoExchangeCorrect)) ⟩
                  complexity (G ∣ (T ∷ A , D))
                    ≡⟨ unfoldComplexity G (T ∷ A , D) (cong-≤-r (cong (λ x -> x + nbOpListFor D) (sym eq₁)) x) ⟩
                  (maxOp G ⊔ ((nbOpFor A + nbOpListFor T) + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ ((nbOpFor A + nbOpListFor T) + nbOpListFor D))))
                    ≡⟨ cong (λ x -> (maxOp G ⊔ (x + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ (x + nbOpListFor D))))) eq₁ ⟩
                  (maxOp G ⊔ suc (nbOpT + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ suc (nbOpT + nbOpListFor D))))
                    ≡⟨ eq ⟩
                  (maxOpG , nbMaxOp) ∎)
                (cong-<L-l
                  {complexity (G ∣ (Γ ∷ A₁ , D) ∣ (Γ ∷ A₂ , D))}
                  (ExchangeKeepComplexity
                    (transHE
                      (indHE
                        (G ∣ (Γ ∷ A₁ , D))
                        (insert G (Γ ∷ A₁ , D))
                        (insertDoExchange G (Γ ∷ A₁ , D)))
                    (insertDoExchange (insert G (Γ ∷ A₁ , D)) (Γ ∷ A₂ , D))))
                  (complexityDecMinL
                    G
                    Γ
                    D
                    A₁
                    A₂
                    (cong-≤-r
                      (cong
                        (λ x -> x + nbOpListFor D)
                        (trans
                          (sym eq₁)
                          (ListExchangeKeepOperator
                            {T ∷ A}
                            {Γ ∷ (A₁ ⊓S A₂)}
                            (ListExchangeSym
                              (ListExchangeCong
                                eq₂
                                (ListExchangeSym ListDoExchangeCorrect))))))
                      x)))))
    cPpFunGiveAtomicLeaves {G ∣ ((T ∷ A) , D)} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | yes p | suc nbOpT | [ eq₁ ] | Γ ∷ (-S A₁) | [ eq₂ ] =
      cPpFunGiveAtomicLeaves
            (insertKeepOrder OG)
            (rs
              (complexity (insert G (Γ , D ∷ A₁)))
              (cong-<L-r
                {complexity (G ∣ (Γ ∷ (-S A₁), D))}
                (begin
                  complexity (G ∣ ((Γ ∷ (-S A₁)) , D))
                    ≡⟨ ListExchangeLKeepComplexity
                         G
                         (Γ ∷ (-S A₁))
                         (T ∷ A)
                         D
                         (ListExchangeCong eq₂ (ListExchangeSym ListDoExchangeCorrect)) ⟩
                  complexity (G ∣ (T ∷ A , D))
                    ≡⟨ unfoldComplexity G (T ∷ A , D) (cong-≤-r (cong (λ x -> x + nbOpListFor D) (sym eq₁)) x) ⟩
                  (maxOp G ⊔ ((nbOpFor A + nbOpListFor T) + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ ((nbOpFor A + nbOpListFor T) + nbOpListFor D))))
                    ≡⟨ cong (λ x -> (maxOp G ⊔ (x + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ (x + nbOpListFor D))))) eq₁ ⟩
                  (maxOp G ⊔ suc (nbOpT + nbOpListFor D) , suc (nbSeqCompl G (maxOp G ⊔ suc (nbOpT + nbOpListFor D))))
                    ≡⟨ eq ⟩
                  (maxOpG , nbMaxOp) ∎)
                (cong-<L-l
                  {complexity (G ∣ (Γ , D ∷ A₁))}
                  (ExchangeKeepComplexity
                    {(G ∣ (Γ , D ∷ A₁))}
                    {(insert G (Γ , D ∷ A₁))}
                    (insertDoExchange
                      G
                      (Γ , D ∷ A₁)))
                  (complexityDecreasing
                    G
                    (Γ , D ∷ A₁)
                    (Γ ∷ (-S A₁) , D)
                    (s≤s
                      (cong-≤-l
                        (begin
                          nbOpFor A₁ + nbOpListFor Γ + nbOpListFor D
                            ≡⟨ cong
                                 (λ x -> x + nbOpListFor D)
                                 (+-comm (nbOpFor A₁) (nbOpListFor Γ)) ⟩
                          nbOpListFor Γ + nbOpFor A₁ + nbOpListFor D
                            ≡⟨ +-assoc (nbOpListFor Γ) (nbOpFor A₁) (nbOpListFor D) ⟩
                          nbOpListFor Γ + (nbOpFor A₁ + nbOpListFor D) ∎)
                        ≤-refl))
                    (cong-≤-r
                      (cong
                        (λ x -> x + nbOpListFor D)
                        {suc nbOpT}
                        {suc (nbOpFor A₁ + nbOpListFor Γ)}
                        (trans
                          (sym eq₁)
                          (ListExchangeKeepOperator
                            {T ∷ A}
                            {Γ ∷ (-S A₁)}
                            (ListExchangeSym (
                              ListExchangeCong
                              eq₂
                              (ListExchangeSym ListDoExchangeCorrect))))))
                      x)))))
    cPpFunGiveAtomicLeaves {G ∣ (T , D)} (ConsOrdered OG x) (acc rs) | maxOpG , nbMaxOp | [ eq ] | no ¬p =
      ⊥-elim (¬p (sym (k≤k'=>k⊔k'=k' x)))
--}}}

  cPpGiveAtomicLeaves :
    (G : HSeq) ->
    AtomicHSeqList (getLeaf (createPreproof G))
--{{{
  cPpGiveAtomicLeaves G =
    cPpFunGiveAtomicLeaves
      (orderCorrect G)
      (AccessibleL (complexity (order G)))
--}}}
