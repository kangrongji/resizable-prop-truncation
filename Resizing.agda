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
    ∣_∣    : X → ∥X∥
    squash : (x y : ∥X∥) → x ≡ y
    elim   :
      {ℓ'' : Level}
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
PropTrucEquiv {X = X} {Y} h ispt = propBiimpl→Equiv h squash ∣_∣ backward
  where
  open isWeakPropTrunc ispt
  backward : Y → X
  backward = elim (λ x → x) (isOfHLevel→isOfHLevelDep 1 (λ _ → h))

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

record ∃WeakPT : SSetω where
  field
    ∥_∥  : Type ℓ → Type ℓ
    ispt : {X : Type ℓ} → isWeakPropTrunc X ∥ X ∥

record ∃ResWeakPT : SSetω where
  field
    ∥_∥  : {ℓ ℓ' : Level} → Type ℓ → Type ℓ'
    ispt : {ℓ ℓ' : Level} {X : Type ℓ} → isWeakPropTrunc {ℓ' = ℓ'} X ∥ X ∥


{-

Weak PropTruncation + Resizing = Resizable Weak PropTruncation

-}

open Resizing
open ∃WeakPT
open ∃ResWeakPT

∃ResWeakPT→∃WeakPT : ∃ResWeakPT → ∃WeakPT
∃ResWeakPT→∃WeakPT h .∥_∥  = h .∥_∥
∃ResWeakPT→∃WeakPT h .ispt = h .ispt

∃ResWeakPT→Resizing : ∃ResWeakPT → Resizing
∃ResWeakPT→Resizing h .resize ℓ ℓ' P = toProp (h .ispt)
∃ResWeakPT→Resizing h .prop-equiv  P = PropTrucEquiv (P .snd) (h .ispt)

Resizing+∃WeakPT→∃ResWeakPT : Resizing → ∃WeakPT → ∃ResWeakPT
Resizing+∃WeakPT→∃ResWeakPT r h .∥_∥ _ = r .resize _ _ (toProp (h .ispt)) .fst
Resizing+∃WeakPT→∃ResWeakPT r h .ispt  = isWeakPropTruncPresEquiv (r .prop-equiv _) (h .ispt)
