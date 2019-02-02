{-# OPTIONS --cubical --no-exact-split --safe #-}
module Cubical.Data.Nat.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat.Base

open import Cubical.Data.Empty
open import Cubical.Data.Sum

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)

-- Addition is associative
+-assoc : ∀ m n o → m + (n + o) ≡ (m + n) + o
+-assoc zero _ _    = refl
+-assoc (suc m) n o = cong suc (+-assoc m n o)

znots : {n : ℕ} → ¬ (0 ≡ suc n)
znots eq = subst (caseNat ℕ ⊥) eq 0

snotz : {n : ℕ} → ¬ (suc n ≡ 0)
snotz eq = subst (caseNat ⊥ ℕ) eq 0

injSuc : {m n : ℕ} → suc m ≡ suc n → m ≡ n
injSuc p = cong predℕ p

discreteℕ : Discrete ℕ
discreteℕ zero zero = yes refl
discreteℕ zero (suc n) = no znots
discreteℕ (suc m) zero = no snotz
discreteℕ (suc m) (suc n) with discreteℕ m n
... | yes p = yes (cong suc p)
... | no p = no (λ x → p (injSuc x))

isSetℕ : isSet ℕ
isSetℕ = Discrete→isSet discreteℕ
