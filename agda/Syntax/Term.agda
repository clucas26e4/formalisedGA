{-                                                  -
 -                                                  -
 -     Module of definition of a formula            -
 -                                                  -
 -                                                  -}

module Syntax.Term where

  {- STDLIB -}
  open import Data.Nat

  {- Syntax -}

  {- Semantic -}

  data Term : Set where
    varAG :
      ℕ ->
      Term
    botAG :
      Term
    _⊔S_ :
      (A : Term) ->
      (B : Term) ->
      Term
    _+S_ :
      (A : Term) ->
      (B : Term) ->
      Term
    _⊓S_ :
      (A : Term) ->
      (B : Term) ->
      Term
    -S_ :
      (A : Term) ->
      Term

  infix 20 _+S_
  infix 25 _⊓S_
  infix 30 _⊔S_

  nbOpFor :
    (F : Term) ->
    ℕ
  nbOpFor botAG =
    1
  nbOpFor (varAG k) =
    0
  nbOpFor (A ⊔S B) =
    1 + (nbOpFor A + nbOpFor B)
  nbOpFor (A +S B) =
    1 + (nbOpFor A + nbOpFor B)
  nbOpFor (A ⊓S B) =
    1 + (nbOpFor A + nbOpFor B)
  nbOpFor (-S A) =
    1 + nbOpFor A

  nbSymbFor :
    (F : Term) ->
    ℕ
  nbSymbFor (varAG x) =
    1
  nbSymbFor botAG =
    1
  nbSymbFor (A ⊔S A₁) =
    1 + nbSymbFor A + nbSymbFor A₁
  nbSymbFor (A +S A₁) =
    1 + nbSymbFor A + nbSymbFor A₁
  nbSymbFor (A ⊓S A₁) = 
    1 + nbSymbFor A + nbSymbFor A₁
  nbSymbFor (-S A) = 
    1 + nbSymbFor A
