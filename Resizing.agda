{-# OPTIONS --cubical --safe #-}
module Resizing where

open import Agda.Primitive
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

private
  variable
    ℓ ℓ' ℓ'' : Level


{-

Proposition Resizing

-}

record Resizing : SSetω where
  field
    resize     : (ℓ ℓ' : Level) → hProp ℓ → hProp ℓ'
    prop-equiv : (P : hProp ℓ) → P .fst ≃ resize ℓ ℓ' P .fst


{-

Weak Propositional Truncation

-}

record isWeakPropTrunc (X : Type ℓ) (∥X∥ : Type ℓ') : SSetω where
  field
    ∣_∣ : X → ∥X∥
    squash : (x y : ∥X∥) → x ≡ y
    elim :
      {P : ∥X∥ → Type ℓ''}
      (p : (x : X) → P ∣ x ∣)
      (h : isPropDep P)
      (x : ∥X∥) → P x
    -- Since the fibers of `P` are all h-propositions, the weak β-rule is admissible.

-- Some properties

toProp : {X : Type ℓ} {Y : Type ℓ'} → isWeakPropTrunc X Y → hProp ℓ'
toProp ispt = _ , squash
  where open isWeakPropTrunc ispt

PropTrucEquiv : {X : Type ℓ} {Y : Type ℓ'} → isProp X → isWeakPropTrunc X Y → X ≃ Y
PropTrucEquiv {X = X} {Y} h ispt = propBiimpl→Equiv h squash ∣_∣ back
  where
  open isWeakPropTrunc ispt
  back : Y → X
  back = elim (λ x → x) (isOfHLevel→isOfHLevelDep 1 (λ _ → h))

isWeakPropTruncPresEquiv :
  {X : Type ℓ} {A : Type ℓ'} {B : Type ℓ''} → A ≃ B → isWeakPropTrunc X A → isWeakPropTrunc X B
isWeakPropTruncPresEquiv {X = X} {A} {B} e ispt = ispt'
  where
  open isWeakPropTrunc ispt
  isprop : isProp B
  isprop = isOfHLevelRespectEquiv 1 e squash
  ispt' : isWeakPropTrunc X B
  ispt' .∣_∣ x = e .fst ∣ x ∣
  ispt' .squash = isprop
  ispt' .elim {P = P} p h b =
    subst P (isprop _ _)
      (elim {P = (λ a → P (e .fst a))} p (λ _ _ _ → h _ _ _) (invEq e b))


{-

Existence of (Resizable) Weak Propositional Truncation

-}

record ∃WeakPropTruc : SSetω where
  field
    ∥_∥ : Type ℓ → Type ℓ
    ispt : {X : Type ℓ} → isWeakPropTrunc X ∥ X ∥

record ∃ResWeakPropTruc : SSetω where
  field
    ∥_∥ : Type ℓ → Type ℓ'
    ispt : {X : Type ℓ} → isWeakPropTrunc {ℓ' = ℓ'} X ∥ X ∥


{-

Equivalence between Resizing Axioms

-}

open Resizing
open ∃WeakPropTruc
open ∃ResWeakPropTruc

∃ResWeakPropTruc→∃WeakPropTruc : ∃ResWeakPropTruc → ∃WeakPropTruc
∃ResWeakPropTruc→∃WeakPropTruc h .∥_∥  = h .∥_∥
∃ResWeakPropTruc→∃WeakPropTruc h .ispt = h .ispt

∃ResWeakPropTruc→Resizing : ∃ResWeakPropTruc → Resizing
∃ResWeakPropTruc→Resizing h .resize ℓ ℓ' P = toProp (h .ispt)
∃ResWeakPropTruc→Resizing h .prop-equiv  P = PropTrucEquiv (P .snd) (h .ispt)

Resizing+∃WeakPropTruc→∃ResWeakPropTruc : Resizing → ∃WeakPropTruc → ∃ResWeakPropTruc
Resizing+∃WeakPropTruc→∃ResWeakPropTruc r h .∥_∥ _ = r .resize _ _ (toProp (h .ispt)) .fst
Resizing+∃WeakPropTruc→∃ResWeakPropTruc r h .ispt  = isWeakPropTruncPresEquiv (r .prop-equiv _) (h .ispt)
