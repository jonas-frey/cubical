{-

This file contains:

- Definition of set quotients and the universal property

-}
{-# OPTIONS --cubical --safe #-}
module Cubical.HITs.SetQuotients where

open import Cubical.Core.Prelude
open import Cubical.Core.PropositionalTruncation
open import Cubical.HITs.SetTruncation
open import Cubical.Core.Glue
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.NTypes

private
  variable
    ℓ : Level
    A : Set ℓ
    R : A → A → hProp


-- Set quotients as a higher inductive type:
data _/_ {ℓ} (A : Set ℓ) (R : A → A → hProp {ℓ}) : Set ℓ where
  [_] : (a : A) → A / R
  eq/ : (a b : A) → (r : fst (R a b)) → [ a ] ≡ [ b ]
  squash/ : (x y : A / R) → (p q : x ≡ y) → p ≡ q

elimEq/ : {B : A / R → Set ℓ} →
          ((x : A / R ) → isProp (B x)) →
          {x y : A / R} →
          (eq : x ≡ y) →
          (bx : B x) →
          (by : B y) →
          PathP (λ i → B (eq i)) bx by
elimEq/ {A = A} {B = B} Bprop {x = x} =
  J (λ y eq → ∀ bx by → PathP (λ i → B (eq i)) bx by) (λ bx by → Bprop x bx by)


elimSetQuotientsProp : {B : A / R → Set ℓ} →
                       ((x : A / R ) → isProp (B x)) →
                       (f : (a : A) → B ( [ a ])) →
                       (x : A / R) → B x
elimSetQuotientsProp Bprop f [ x ] = f x
elimSetQuotientsProp Bprop f (squash/ x y p q i j) =
  elimSquash₀ (λ x → isProp→isSet (Bprop x)) (squash/ x y p q)
              (g x) (g y) (cong g p) (cong g q) i j
    where
    g = elimSetQuotientsProp Bprop f
elimSetQuotientsProp Bprop f (eq/ a b r i) = elimEq/ Bprop (eq/ a b r) (f a) (f b) i

-- lemma 6.10.2 in hott book
-- TODO: defined truncated Sigma as ∃
[]surjective : (x : A / R) → ∥ Σ[ a ∈ A ] [ a ] ≡ x ∥
[]surjective = elimSetQuotientsProp (λ x → squash) (λ a → ∣ a , refl ∣)


elimSetQuotients : {B : A / R → Set ℓ} →
                   (Bset : (x : A / R) → isSet (B x)) → 
                   (f : (a : A) → (B [ a ])) →
                   (feq : (a b : A) (r : fst (R a b)) →
                          PathP (λ i → B (eq/ a b r i)) (f a) (f b)) → 
                   (x : A / R) → B x
elimSetQuotients Bset f feq [ a ] = f a
elimSetQuotients Bset f feq (eq/ a b r i) = feq a b r i
elimSetQuotients Bset f feq (squash/ x y p q i j) =
  elimSquash₀ Bset (squash/ x y p q)
              (g x) (g y) (cong g p) (cong g q) i j
    where
      g = elimSetQuotients Bset f feq

setQuotUniversal : {B : Set ℓ} (Bset : isSet B) →
                   (A / R → B) ≃ (Σ[ f ∈ (A → B) ] ((a b : A) → fst (R a b) → f a ≡ f b))
setQuotUniversal Bset = isoToEquiv intro elim leftInv rightInv
  where
  intro = λ g →  (λ a → g [ a ]) , λ a b r i → g (eq/ a b r i)
  elim = λ h → elimSetQuotients (λ x → Bset) (fst h) (snd h)

  leftInv : ∀ h → intro (elim h) ≡ h
  leftInv h = refl

  rightInv : ∀ g → elim (intro g) ≡ g
  rightInv = λ g → funExt (λ x → elimPropTrunc {P = λ sur → elim (intro g) x ≡ g x}
    (λ sur → Bset (elim (intro g) x) (g x))
    (λ sur → compPath (cong (elim (intro g)) (sym (snd sur))) (cong g (snd sur))) ([]surjective x)
    )


