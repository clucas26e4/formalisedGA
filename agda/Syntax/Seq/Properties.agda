module Syntax.Seq.Properties where

  {- STDLIB -}
  open import Nat
  open import Int
  open import Equality
  open import Data.Empty
  open import Relation.Nullary
  open import Relation.Nullary.Decidable

  {- Syntax -}
  open import Syntax.Term
  open import Syntax.ListTerm
  open import Syntax.ListTerm.Properties
  open import Syntax.ListTerm.Canonic
  open import Syntax.Seq

  {- Semantic -}
  open import Semantic.SemEquality
  open import Semantic.SemEquality.Properties
  open import Semantic.Interpretation
  open import Semantic.Model

  ⟦T,D⟧=0=>⟦T⟧=⟦D⟧ :
    (T D : ListTerm) ->
    ⟦ T , D ⟧S ≡ₛ botAG ->
    ⟦ T ⟧L ≡ₛ ⟦ D ⟧L
  ⟦T,D⟧=0=>⟦T⟧=⟦D⟧ T D TD=0 =
    symₛ
      (A-B=0=>A=B
        TD=0)

  checkNbVar :
    (T : ListTerm) ->
    (k : ℕ) ->
    nbOpListFor T ≡ 0 ->
    ⟦ (⟦ T ⟧L) ⟧/ (updateValuation (λ x -> (+ 0)) k (+ 1)) ≡ (+ nbOccurVar T k)
  checkNbVar [] k opT = 
    refl
  checkNbVar (T ∷ varAG x) k opT with x ≡? k
  checkNbVar (T ∷ varAG x) k opT | yes p with k ≡? x
  checkNbVar (T ∷ varAG x) k opT | yes p | yes p₁ =
    begin
      (⟦ ⟦ T ⟧L ⟧/ (λ n' → updateValuation (λ x₁ → + 0) k (+ 1) n')) Int.+ (+ 1)
        ≡⟨ Int.+-comm ((⟦ ⟦ T ⟧L ⟧/ (λ n' → updateValuation (λ x₁ → + 0) k (+ 1) n'))) (+ 1) ⟩
      (+ 1) Int.+ (⟦ ⟦ T ⟧L ⟧/ (λ n' → updateValuation (λ x₁ → + 0) k (+ 1) n'))
        ≡⟨ cong
             (λ y -> (+ 1) Int.+ y)
             (checkNbVar T k opT) ⟩
     (+ 1) Int.+ (+ nbOccurVar T k)
        ≡⟨ refl ⟩
      + Nat.suc (nbOccurVar T k) ∎
  checkNbVar (T ∷ varAG x) k opT | yes p | no ¬p =
    ⊥-elim (¬p (sym p))
  checkNbVar (T ∷ varAG x) k opT | no ¬p with k ≡? x
  checkNbVar (T ∷ varAG x) k opT | no ¬p | yes p =
    ⊥-elim (¬p (sym p))
  checkNbVar (T ∷ varAG x) k opT | no ¬p | no ¬p₁ =
    trans
      (Int.+-identityʳ (⟦ ⟦ T ⟧L ⟧/ (λ n' → updateValuation (λ x₁ → + 0) k (+ 1) n')) )
      (checkNbVar T k opT)
  checkNbVar (T ∷ botAG) k opT =
    ⊥-elim (notSucEqZero opT)
  checkNbVar (T ∷ (A ⊔S A₁)) k opT = 
    ⊥-elim (notSucEqZero opT)
  checkNbVar (T ∷ (A +S A₁)) k opT = 
    ⊥-elim (notSucEqZero opT)
  checkNbVar (T ∷ (A ⊓S A₁)) k opT = 
    ⊥-elim (notSucEqZero opT)
  checkNbVar (T ∷ (-S A)) k opT = 
    ⊥-elim (notSucEqZero opT)

  ⟦T⟧=⟦D⟧=>sameVar :
    (T D : ListTerm) ->
    (T=D : ⟦ T ⟧L ≡ₛ ⟦ D ⟧L) ->
    (k : ℕ) ->
    nbOpListFor T ≡ 0 ->
    nbOpListFor D ≡ 0 -> 
    nbOccurVar T k ≡ nbOccurVar D k
  ⟦T⟧=⟦D⟧=>sameVar T D T=D k opT opD =
    +-injective
      (begin
        + nbOccurVar T k
          ≡⟨ sym
               (checkNbVar T k opT) ⟩
        (⟦ ⟦ T ⟧L ⟧/ (λ n' → updateValuation (λ x₁ → + 0) k (+ 1) n'))
          ≡⟨ ℤisModel (⟦ T ⟧L) (⟦ D ⟧L) T=D (updateValuation (λ x -> + 0) k (+ 1)) ⟩
        (⟦ ⟦ D ⟧L ⟧/ (λ n' → updateValuation (λ x₁ → + 0) k (+ 1) n'))
          ≡⟨ checkNbVar D k opD ⟩
        + nbOccurVar D k ∎)

  unionSeqNeutral :
    (H : Seq) ->
    unionSeq ([] , []) H ≡ H
  unionSeqNeutral (T , D) =
    cong₂
      (λ x y -> x , y)
      (union[]T=T T)
      (union[]T=T D)
