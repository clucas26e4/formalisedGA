module Print where

  {- STDLIB -}
  open import Data.String
  open import Data.Nat.Show
  open import IO
  import IO.Primitive as Prim
  open import Data.Unit
  
  {- Syntax -}
  open import Syntax.AGFor
  open import Syntax.AGList
  open import Syntax.AGSeq
  open import Syntax.AGHSeq
  open import Syntax.Preproof
  open import Syntax.Preproof.Create
  
  {- Semantic -}
  open import Semantic.SemEquality
  open import Semantic.SemEquality.Properties

  ForToString :
    (A : AGFor) ->
    String
  ForToString (varAG x) = "A_" ++ (Data.Nat.Show.show x)
  ForToString botAG = "0"
  ForToString (A ⊔S A₁) = "(" ++ ForToString A ++ " \\sqcup " ++ ForToString A₁ ++ " )"
  ForToString (A ⊓S A₁) = "(" ++ ForToString A ++ " \\sqcap " ++ ForToString A₁ ++ " )"
  ForToString (A +S A₁) = "(" ++ ForToString A ++ " + " ++ ForToString A₁ ++ " )"
  ForToString (-S A) = "(- " ++ ForToString A ++ ")"

  ListToString :
    (Γ : AGList) ->
    String
  ListToString [] = 
    ""
  ListToString (Γ ∷ A) = 
    ListToString Γ ++ " , " ++ ForToString A

  SeqToString :
    (H : AGSeq) ->
    String
  SeqToString (T , D) = 
    ListToString T ++ " \\vdash " ++ ListToString D

  HSeqToString :
    (G : AGHSeq) ->
    String
  HSeqToString (head H) = 
    SeqToString H
  HSeqToString (G ∣ H) = 
    HSeqToString G ++ " | " ++ SeqToString H

  PreproofToString :
    {G : AGHSeq} ->
    (pp : Preproof G) ->
    String
  PreproofToString (leaf G) =
    HSeqToString G
  PreproofToString (PreZ-L G Γ Δ pp) =
    "\\infer[0-L]{" ++ HSeqToString (G ∣ (Γ ∷ botAG , Δ)) ++ "}{" ++ PreproofToString pp ++ "}"
  PreproofToString (PreZ-R G Γ Δ pp) =
    "\\infer[0-R]{" ++ HSeqToString (G ∣ (Γ , Δ ∷ botAG)) ++ "}{" ++ PreproofToString pp ++ "}"
  PreproofToString (Preminus-L G Γ Δ A pp) = 
    "\\infer[minus-L]{" ++ HSeqToString (G ∣ (Γ ∷ (-S A) , Δ)) ++ "}{" ++ PreproofToString pp ++ "}"
  PreproofToString (Preminus-R G Γ Δ A pp) = 
    "\\infer[minus-R]{" ++ HSeqToString (G ∣ (Γ , Δ ∷ (-S A))) ++ "}{" ++ PreproofToString pp ++ "}"
  PreproofToString (Preplus-L G Γ Δ A B pp) = 
    "\\infer[+-L]{" ++ HSeqToString (G ∣ (Γ ∷ (A +S B) , Δ)) ++ "}{" ++ PreproofToString pp ++ "}"
  PreproofToString (Preplus-R G Γ Δ A B pp) = 
    "\\infer[+-R]{" ++ HSeqToString (G ∣ (Γ , Δ ∷ (A +S B))) ++ "}{" ++ PreproofToString pp ++ "}"
  PreproofToString (Premax-L G Γ Δ A B pp pp₁) = 
    "\\infer[\\sqcup-L]{" ++ HSeqToString (G ∣ (Γ ∷ (A ⊔S B) , Δ)) ++ "}{" ++ PreproofToString pp ++ " & " ++ PreproofToString pp₁ ++ "}"
  PreproofToString (Premax-R G Γ Δ A B pp) = 
    "\\infer[\\sqcup-R]{" ++ HSeqToString (G ∣ (Γ , Δ ∷ (A ⊔S B))) ++ "}{" ++ PreproofToString pp ++ "}"
  PreproofToString (Premin-L G Γ Δ A B pp) = 
    "\\infer[\\sqcup-R]{" ++ HSeqToString (G ∣ (Γ ∷ (A ⊓S B), Δ)) ++ "}{" ++ PreproofToString pp ++ "}"
  PreproofToString (Premin-R G Γ Δ A B pp pp₁) = 
    "\\infer[\\sqcap-R]{" ++ HSeqToString (G ∣ (Γ , Δ ∷ (A ⊓S B))) ++ "}{" ++ PreproofToString pp ++ " & " ++ PreproofToString pp₁ ++ "}"
  PreproofToString (PreZ-L-head Γ Δ pp) =
    "\\infer[0-L]{" ++ HSeqToString (head (Γ ∷ botAG , Δ)) ++ "}{" ++ PreproofToString pp ++ "}"
  PreproofToString (PreZ-R-head Γ Δ pp) =
    "\\infer[0-R]{" ++ HSeqToString (head (Γ , Δ ∷ botAG)) ++ "}{" ++ PreproofToString pp ++ "}"
  PreproofToString (Preminus-L-head Γ Δ A pp) = 
    "\\infer[minus-L]{" ++ HSeqToString (head (Γ ∷ (-S A) , Δ)) ++ "}{" ++ PreproofToString pp ++ "}"
  PreproofToString (Preminus-R-head Γ Δ A pp) = 
    "\\infer[minus-R]{" ++ HSeqToString (head (Γ , Δ ∷ (-S A))) ++ "}{" ++ PreproofToString pp ++ "}"
  PreproofToString (Preplus-L-head Γ Δ A B pp) = 
    "\\infer[+-L]{" ++ HSeqToString (head (Γ ∷ (A +S B) , Δ)) ++ "}{" ++ PreproofToString pp ++ "}"
  PreproofToString (Preplus-R-head Γ Δ A B pp) = 
    "\\infer[+-R]{" ++ HSeqToString (head (Γ , Δ ∷ (A +S B))) ++ "}{" ++ PreproofToString pp ++ "}"
  PreproofToString (Premax-L-head Γ Δ A B pp pp₁) = 
    "\\infer[\\sqcup-L]{" ++ HSeqToString (head (Γ ∷ (A ⊔S B) , Δ)) ++ "}{" ++ PreproofToString pp ++ " & " ++ PreproofToString pp₁ ++ "}"
  PreproofToString (Premax-R-head Γ Δ A B pp) = 
    "\\infer[\\sqcup-R]{" ++ HSeqToString (head (Γ , Δ ∷ (A ⊔S B))) ++ "}{" ++ PreproofToString pp ++ "}"
  PreproofToString (Premin-L-head Γ Δ A B pp) = 
    "\\infer[\\sqcup-R]{" ++ HSeqToString (head (Γ ∷ (A ⊓S B), Δ)) ++ "}{" ++ PreproofToString pp ++ "}"
  PreproofToString (Premin-R-head Γ Δ A B pp pp₁) = 
    "\\infer[\\sqcap-R]{" ++ HSeqToString (head (Γ , Δ ∷ (A ⊓S B))) ++ "}{" ++ PreproofToString pp ++ " & " ++ PreproofToString pp₁ ++ "}"
  PreproofToString (Preseq-exchange G Γ Γ' Δ Δ' x x₁ pp) = 
    PreproofToString pp
  PreproofToString (Preseq-exchange-head Γ Γ' Δ Δ' x x₁ pp) =
    PreproofToString pp
  PreproofToString (Prehseq-exchange G G' x pp) =
    PreproofToString pp

  EqToString :
    {A B : AGFor} →
    A ≡ₛ B ->
    String
  EqToString {A} {.A} reflₛ =
    "\\infer[refl]{\\mathbbm{A}\\vdash " ++ ForToString A ++ "=" ++ ForToString A ++ "}{}" 
  EqToString {A} {B} (transₛ A=B A=B₁) =
    "\\infer[trans]{\\mathbbm{A}\\vdash " ++ ForToString A ++ "=" ++ ForToString B ++ "}{" ++ EqToString A=B ++ " & " ++ EqToString A=B₁ ++ "}"
  EqToString {A} {B} (symₛ A=B) =
    "\\infer[sym]{\\mathbbm{A}\\vdash " ++ ForToString A ++ "=" ++ ForToString B ++ "}{" ++ EqToString A=B ++ "}"
  EqToString (ctxtₛ {A} {B} Ctxt A=B) =
    "\\infer[ctxt]{\\mathbbm{A}\\vdash " ++ ForToString (Ctxt [ A ]) ++ "=" ++ ForToString (Ctxt [ B ]) ++ "}{" ++ EqToString A=B ++ "}"
  EqToString (substₛ {A'} {A} {B} {k} A=B) =
    "\\infer[subst]{\\mathbbm{A}\\vdash " ++ ForToString (A' [ A / k ]) ++ "=" ++ ForToString (A' [ B / k ]) ++ "}{" ++ EqToString A=B ++ "}"
  EqToString {(A +S (B +S C))} {.((_ +S _) +S _)} asso-+S =
    "\\infer[ax]{\\mathbbm{A}\\vdash " ++ ForToString (A +S (B +S C)) ++ "=" ++ ForToString ((A +S B) +S C) ++ "}{}"
  EqToString {(A +S B)} {.(_ +S _)} commu-+S = 
    "\\infer[ax]{\\mathbbm{A}\\vdash " ++ ForToString (A +S B) ++ "=" ++ ForToString (B +S A) ++ "}{}"
  EqToString {.(B +S botAG)} {B} neutral-+S = 
    "\\infer[ax]{\\mathbbm{A}\\vdash " ++ ForToString (B +S botAG) ++ "=" ++ ForToString B ++ "}{}"
  EqToString {(B +S (-S .B))} {.botAG} opp-+S = 
    "\\infer[ax]{\\mathbbm{A}\\vdash " ++ ForToString (B -S B) ++ "=" ++ ForToString botAG ++ "}{}"
  EqToString {(A ⊔S (B ⊔S C))} {.((_ ⊔S _) ⊔S _)} asso-⊔S = 
    "\\infer[ax]{\\mathbbm{A}\\vdash " ++ ForToString (A ⊔S (B ⊔S C)) ++ "=" ++ ForToString ((A ⊔S B) ⊔S C) ++ "}{}"
  EqToString {(A ⊔S B)} {.(_ ⊔S _)} commu-⊔S = 
    "\\infer[ax]{\\mathbbm{A}\\vdash " ++ ForToString (A ⊔S B) ++ "=" ++ ForToString (B ⊔S A) ++ "}{}"
  EqToString {(.B ⊔S (.B ⊓S A))} {B} abso-⊔S = "\\infer[trans]{\\mathbbm{A}\\vdash" ++ ForToString (B ⊔S (B ⊓S A)) ++ "=" ++ ForToString B ++ "}{}"
  EqToString {(A ⊓S (B ⊓S C))} {.((_ ⊓S _) ⊓S _)} asso-⊓S = 
    "\\infer[ax]{\\mathbbm{A}\\vdash " ++ ForToString (A ⊓S (B ⊓S C)) ++ "=" ++ ForToString ((A ⊓S B) ⊓S C) ++ "}{}"
  EqToString {(A ⊓S B)} {.(_ ⊓S _)} commu-⊓S = 
    "\\infer[ax]{\\mathbbm{A}\\vdash " ++ ForToString (A ⊓S B) ++ "=" ++ ForToString (B ⊓S A) ++ "}{}"
  EqToString {(.B ⊓S .B ⊔S A)} {B} abso-⊓S = 
    "\\infer[ax]{\\mathbbm{A}\\vdash " ++ ForToString (B ⊓S B ⊔S A) ++ "=" ++ ForToString B ++ "}{}"
  EqToString {((A ⊓S B +S C) ⊓S (.B +S .C))} {.(_ ⊓S _ +S _)} compa-+S = 
    "\\infer[ax]{\\mathbbm{A}\\vdash " ++ ForToString (A ⊓S B +S C) ++ "<" ++ ForToString (B +S C) ++ "}{}"

  main : Prim.IO ⊤
  main = run (writeFile "test" (EqToString (≤S-refl-cong {varAG 1} {varAG 2})))
