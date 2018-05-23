module Semantic.Model where
  {- STDLIB -}
  open import Nat
  open import Int as ℤ
  open import Equality
  open import Relation.Nullary
  open import Relation.Nullary.Decidable
  open import Data.Empty

  {- Syntax -}
  open import Syntax.Term
  open import Syntax.ListTerm
  open import Syntax.Seq
  open import Syntax.HSeq

  {- Semantic -}
  open import Semantic.SemEquality
  open import Semantic.SemEquality.Properties

  updateValuation :
    (ℕ -> ℤ) ->
    ℕ ->
    ℤ ->
    (ℕ -> ℤ)
  updateValuation f n x n' with n ≡? n'
  updateValuation f n x n' | yes p =
    x
  updateValuation f n x n' | no ¬p =
    f n

  ⟦_⟧/_ :
    Term ->
    (ℕ -> ℤ) ->
    ℤ
  ⟦ varAG x ⟧/ v =
    v x
  ⟦ botAG ⟧/ v =
    ℤ.+ zero
  ⟦ A ⊔S A₁ ⟧/ v =
    (⟦ A ⟧/ v) ⊔ℤ (⟦ A₁ ⟧/ v)
  ⟦ A ⊓S A₁ ⟧/ v = 
    (⟦ A ⟧/ v) ⊓ℤ (⟦ A₁ ⟧/ v)
  ⟦ A +S A₁ ⟧/ v = 
    (⟦ A ⟧/ v) ℤ.+ (⟦ A₁ ⟧/ v)
  ⟦ -S A ⟧/ v = - (⟦ A ⟧/ v)

  ℤisModel :
    (A B : Term) ->
    A ≡ₛ B ->
    (v : ℕ -> ℤ) ->
    (⟦ A ⟧/ v) ≡ (⟦ B ⟧/ v)
  ℤisModel A .A reflₛ v =
    refl
  ℤisModel A B (transₛ {.A} {C} {.B} A=B A=B₁) v =
    trans (ℤisModel A C A=B v) (ℤisModel C B A=B₁ v)
  ℤisModel A B (symₛ A=B) v =
    sym (ℤisModel B A A=B v)
  ℤisModel .A .B (ctxtₛ {A} {B} ● A=B) v =
    ℤisModel A B A=B v
  ℤisModel .x .x (ctxtₛ {A} {B} (CC x) A=B) v =
    refl
  ℤisModel .(varAG x) .(varAG x) (ctxtₛ {A} {B} (varC x) A=B) v =
    refl
  ℤisModel .botAG .botAG (ctxtₛ {A} {B} botC A=B) v =
    refl
  ℤisModel .((_[_] Ctxt A) ⊔S (_[_] Ctxt₁ A)) .((_[_] Ctxt B ) ⊔S (_[_] Ctxt₁ B)) (ctxtₛ {A} {B} (Ctxt ⊔C Ctxt₁) A=B) v =
    cong₂
      (λ x y -> x ⊔ℤ y)
      (ℤisModel (_[_] Ctxt A) (_[_] Ctxt B) (ctxtₛ Ctxt A=B) v)
      (ℤisModel (_[_] Ctxt₁ A) (_[_] Ctxt₁ B) (ctxtₛ Ctxt₁ A=B) v) 
  ℤisModel .((_[_] Ctxt A) +S (_[_] Ctxt₁ A)) .((_[_] Ctxt B ) +S (_[_] Ctxt₁ B)) (ctxtₛ {A} {B} (Ctxt +C Ctxt₁) A=B) v = 
    cong₂
      (λ x y -> x ℤ.+ y)
      (ℤisModel (_[_] Ctxt A) (_[_] Ctxt B) (ctxtₛ Ctxt A=B) v)
      (ℤisModel (_[_] Ctxt₁ A) (_[_] Ctxt₁ B) (ctxtₛ Ctxt₁ A=B) v) 
  ℤisModel .((_[_] Ctxt A) ⊓S (_[_] Ctxt₁ A)) .((_[_] Ctxt B) ⊓S (_[_] Ctxt₁ B)) (ctxtₛ {A} {B} (Ctxt ⊓C Ctxt₁) A=B) v = 
    cong₂
      (λ x y -> x ⊓ℤ y)
      (ℤisModel (_[_] Ctxt A) (_[_] Ctxt B) (ctxtₛ Ctxt A=B) v)
      (ℤisModel (_[_] Ctxt₁ A) (_[_] Ctxt₁ B) (ctxtₛ Ctxt₁ A=B) v) 
  ℤisModel .(-S (_[_] Ctxt A)) .(-S (_[_] Ctxt B)) (ctxtₛ {A} {B} (-C Ctxt) A=B) v = 
    cong
      (λ x -> - x)
      (ℤisModel (_[_] Ctxt A) (_[_] Ctxt B) (ctxtₛ Ctxt A=B) v)
  ℤisModel .B .C (substₛ {varAG zero} {B} {C} {zero} A=B) v =
    ℤisModel B C A=B v
  ℤisModel .(varAG 0) .(varAG 0) (substₛ {varAG zero} {B} {C} {Nat.suc k} A=B) v =
    refl
  ℤisModel .(varAG (Nat.suc x)) .(varAG (Nat.suc x)) (substₛ {varAG (Nat.suc x)} {B} {C} {zero} A=B) v =
    refl
  ℤisModel .(varAG x [ B / k ]) .(varAG x [ C / k ]) (substₛ {varAG (Nat.suc x)} {B} {C} {Nat.suc k} A=B) v =
    ℤisModel (varAG x [ B / k ]) (varAG x [ C / k ]) (substₛ {varAG x} {B} {C} {k} A=B) v
  ℤisModel .botAG .botAG (substₛ {botAG} {B} {C} {k} A=B) v =
    refl
  ℤisModel .((A [ B / k ]) ⊔S (A₁ [ B / k ])) .((A [ C / k ]) ⊔S (A₁ [ C / k ])) (substₛ {A ⊔S A₁} {B} {C} {k} A=B) v =
    cong₂
      (λ x y -> x ⊔ℤ y)
      (ℤisModel (A [ B / k ]) (A [ C / k ]) (substₛ {A} {B} {C} {k} A=B) v)
      (ℤisModel (A₁ [ B / k ]) (A₁ [ C / k ]) (substₛ {A₁} {B} {C} {k} A=B) v)
  ℤisModel .((A [ B / k ]) +S (A₁ [ B / k ])) .((A [ C / k ]) +S (A₁ [ C / k ])) (substₛ {A +S A₁} {B} {C} {k} A=B) v = 
    cong₂
      (λ x y -> x ℤ.+ y)
      (ℤisModel (A [ B / k ]) (A [ C / k ]) (substₛ {A} {B} {C} {k} A=B) v)
      (ℤisModel (A₁ [ B / k ]) (A₁ [ C / k ]) (substₛ {A₁} {B} {C} {k} A=B) v)
  ℤisModel .((A [ B / k ]) ⊓S (A₁ [ B / k ])) .((A [ C / k ]) ⊓S (A₁ [ C / k ])) (substₛ {A ⊓S A₁} {B} {C} {k} A=B) v = 
    cong₂
      (λ x y -> x ⊓ℤ y)
      (ℤisModel (A [ B / k ]) (A [ C / k ]) (substₛ {A} {B} {C} {k} A=B) v)
      (ℤisModel (A₁ [ B / k ]) (A₁ [ C / k ]) (substₛ {A₁} {B} {C} {k} A=B) v)
  ℤisModel .(-S (A [ B / k ])) .(-S (A [ C / k ])) (substₛ { -S A} {B} {C} {k} A=B) v = 
    cong
      (λ x -> - x)
      (ℤisModel (A [ B / k ]) (A [ C / k ]) (substₛ {A} {B} {C} {k} A=B) v)
  ℤisModel (A +S (B +S C)) ((.A +S .B) +S .C) asso-+S v =
    sym (ℤ.+-assoc (⟦ A ⟧/ v) (⟦ B ⟧/ v) (⟦ C ⟧/ v))
  ℤisModel (A +S B) .(B +S A) commu-+S v =
    ℤ.+-comm (⟦ A ⟧/ v) (⟦ B ⟧/ v)
  ℤisModel .(B +S botAG) B neutral-+S v =
    ℤ.+-identityʳ (⟦ B ⟧/ v)
  ℤisModel (A +S (-S .A)) .botAG opp-+S v =
    +-inverseʳ (⟦ A ⟧/ v)
  ℤisModel (A ⊔S (B ⊔S C)) .((_ ⊔S _) ⊔S _) asso-⊔S v =
    asso-⊔ℤ
      (⟦ A ⟧/ v)
      (⟦ B ⟧/ v)
      (⟦ C ⟧/ v)
  ℤisModel (A ⊔S B) .(_ ⊔S _) commu-⊔S v =
    commu-⊔ℤ
      (⟦ A ⟧/ v)
      (⟦ B ⟧/ v)
  ℤisModel (.B ⊔S (.B ⊓S A)) B abso-⊔S v =
    abso-⊔ℤ
      (⟦ B ⟧/ v)
      (⟦ A ⟧/ v)
  ℤisModel (A ⊓S (B ⊓S C)) .((_ ⊓S _) ⊓S _) asso-⊓S v =
    asso-⊓ℤ
      (⟦ A ⟧/ v)
      (⟦ B ⟧/ v)
      (⟦ C ⟧/ v)
  ℤisModel (A ⊓S B) .(_ ⊓S _) commu-⊓S v =
    commu-⊓ℤ
      (⟦ A ⟧/ v)
      (⟦ B ⟧/ v)
  ℤisModel (.B ⊓S .B ⊔S A) B abso-⊓S v =
    abso-⊓ℤ
      (⟦ B ⟧/ v)
      (⟦ A ⟧/ v)
  ℤisModel ((A ⊓S B +S C) ⊓S (.B +S .C)) .(_ ⊓S _ +S _) compa-+S v =
    compa-+
      (⟦ A ⟧/ v)
      (⟦ B ⟧/ v)
      (⟦ C ⟧/ v)
