{-# OPTIONS --cubical --safe #-}
module Cubical.Data.DiffInt.Base where

open import Cubical.HITs.SetQuotients.Base
open import Cubical.Data.Nat

open import Cubical.Foundations.HLevels

open import Cubical.Core.Prelude
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq
open import Cubical.Relation.Binary.Base

open import Cubical.Core.Glue
open import Cubical.Foundations.Equiv

rel : (ℕ × ℕ) → (ℕ × ℕ) → Σ Set isProp
rel (a₀ , b₀) (a₁ , b₁) =
  (x ≡ y), (isSetℕ x y)
  where
    x = a₀ + b₁
    y = a₁ + b₀

ℤ = (ℕ × ℕ) / rel

relIsEquiv : BinaryRelation.isEquiv rel
relIsEquiv = BinaryRelation.Equiv isRefl isSym isTrans
  where
    isRefl : BinaryRelation.isRefl rel
    isRefl = refl

    isSym : BinaryRelation.isSym rel
    isSym = sym

    isTrans : BinaryRelation.isTrans rel
    isTrans {a = (a0 , a1)} {b = (b0 , b1 )} {c = (c0 , c1)} p0 p1 =
      +-inj (b0 + b1) ((b0 + b1) + (a0 + c1) ≡⟨ +-assoc (b0 + b1) a0 c1  ⟩
            ((b0 + b1) + a0) + c1 ≡⟨ cong (λ x → x + a0 + c1) (+-sym b0 b1)⟩
            ((b1 + b0) + a0) + c1 ≡⟨ cong (λ x → x + c1) (+-sym (b1 + b0) a0) ⟩
            (a0 + (b1 + b0)) + c1 ≡⟨ cong (λ x → x + c1) (+-assoc a0 b1 b0) ⟩
            (a0 + b1) + b0 + c1 ≡⟨ sym (+-assoc (a0 + b1) b0 c1) ⟩
            (a0 + b1) + (b0 + c1) ≡⟨ +-cong p0 p1 ⟩
            (b0 + a1) + (c0 + b1) ≡⟨ sym (+-assoc b0 a1 (c0 + b1))⟩
            b0 + (a1 + (c0 + b1)) ≡⟨ cong (λ x → b0 + (a1 + x)) (+-sym c0 b1)⟩
            b0 + (a1 + (b1 + c0)) ≡⟨ cong (λ x → b0 + x) (+-sym a1 (b1 + c0)) ⟩
            b0 + ((b1 + c0) + a1) ≡⟨ cong (λ x → b0 + x) (sym (+-assoc b1 c0 a1))⟩
            b0 + (b1 + (c0 + a1)) ≡⟨ +-assoc b0 b1 (c0 + a1)⟩
            (b0 + b1) + (c0 + a1) ∎ )
