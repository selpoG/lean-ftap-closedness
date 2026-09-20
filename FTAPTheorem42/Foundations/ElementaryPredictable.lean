/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.ElementaryStrategy
import Mathlib.Probability.Process.Stopping

/-!
# Predictable elementary strategies

This module equips the elementary interval calculus with a filtration.  A
block carries two finite stopping times and a coefficient measurable at its
starting stopping time.  The post-stopping tail of such a block is again
predictable: its new starting time is the maximum of the old start and the
cutoff, so both the old coefficient and an event known at the cutoff are
measurable at the new start.

We deliberately do not claim that the raw blockwise `stopped` operation
preserves this structure.  If the cutoff occurs before the original start,
the new start is earlier and the unchanged coefficient need not be measurable
there.  The stopped gain needed for pasting is instead represented
algebraically as the original strategy minus its predictable post-stopping
tail.
-/

open MeasureTheory

namespace FTAPTheorem42

variable {Ω Time : Type*} [MeasurableSpace Ω] [LinearOrder Time]

/--
An elementary interval whose endpoints are finite stopping times and whose
coefficient is known at the starting stopping time.
-/
structure PredictableElementaryInterval
    (ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)) where
  interval : ElementaryInterval Ω Time
  startStopping :
    IsStoppingTime ℱ
      (fun ω => (interval.startTime ω : WithTop Time))
  stopStopping :
    IsStoppingTime ℱ
      (fun ω => (interval.stopTime ω : WithTop Time))
  coefficient_measurable :
    Measurable[startStopping.measurableSpace]
      interval.coefficient

namespace PredictableElementaryInterval

attribute [local instance] Classical.propDecidable

variable {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}

theorem ext
    {B C : PredictableElementaryInterval ℱ}
    (h : B.interval = C.interval) : B = C := by
  cases B with
  | mk Bi Bs Bt Bm =>
    cases C with
    | mk Ci Cs Ct Cm =>
      simp only at h
      subst Ci
      rfl

/--
Retain the part of a predictable block after a finite stopping time.

The coefficient remains measurable because the new start is later than both
the original start and the cutoff.
-/
noncomputable def after
    (B : PredictableElementaryInterval ℱ)
    (τ : Ω → Time)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop Time))) :
    PredictableElementaryInterval ℱ := by
  let hstart :
      IsStoppingTime ℱ
        (fun ω =>
          ((max (B.interval.startTime ω) (τ ω) : Time) :
            WithTop Time)) := by
    simpa only [WithTop.coe_max] using B.startStopping.max hτ
  let hstop :
      IsStoppingTime ℱ
        (fun ω =>
          ((max (B.interval.stopTime ω) (τ ω) : Time) :
            WithTop Time)) := by
    simpa only [WithTop.coe_max] using B.stopStopping.max hτ
  refine
    { interval := B.interval.after τ
      startStopping := hstart
      stopStopping := hstop
      coefficient_measurable := ?_ }
  have hle :
      (fun ω => (B.interval.startTime ω : WithTop Time)) ≤
        fun ω =>
          ((max (B.interval.startTime ω) (τ ω) : Time) :
            WithTop Time) := by
    intro ω
    exact WithTop.coe_le_coe.mpr
      (le_max_left (B.interval.startTime ω) (τ ω))
  exact B.coefficient_measurable.mono
    (B.startStopping.measurableSpace_mono hstart hle) le_rfl

/--
Retain the post-`τ` tail on an event known at `τ`, and use the zero
coefficient off that event.
-/
noncomputable def restrictAfter
    (B : PredictableElementaryInterval ℱ)
    (τ : Ω → Time)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop Time)))
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s) :
    PredictableElementaryInterval ℱ := by
  let hstart :
      IsStoppingTime ℱ
        (fun ω =>
          ((max (B.interval.startTime ω) (τ ω) : Time) :
            WithTop Time)) := by
    simpa only [WithTop.coe_max] using B.startStopping.max hτ
  let hstop :
      IsStoppingTime ℱ
        (fun ω =>
          ((max (B.interval.stopTime ω) (τ ω) : Time) :
            WithTop Time)) := by
    simpa only [WithTop.coe_max] using B.stopStopping.max hτ
  refine
    { interval :=
        (B.interval.after τ).mulCoefficient
          (fun ω => if ω ∈ s then 1 else 0)
      startStopping := hstart
      stopStopping := hstop
      coefficient_measurable := ?_ }
  have hstart_le :
      (fun ω => (B.interval.startTime ω : WithTop Time)) ≤
        fun ω =>
          ((max (B.interval.startTime ω) (τ ω) : Time) :
            WithTop Time) := by
    intro ω
    exact WithTop.coe_le_coe.mpr
      (le_max_left (B.interval.startTime ω) (τ ω))
  have hτ_le :
      (fun ω => (τ ω : WithTop Time)) ≤
        fun ω =>
          ((max (B.interval.startTime ω) (τ ω) : Time) :
            WithTop Time) := by
    intro ω
    exact WithTop.coe_le_coe.mpr
      (le_max_right (B.interval.startTime ω) (τ ω))
  have hcoeff :
      Measurable[hstart.measurableSpace]
        B.interval.coefficient :=
    B.coefficient_measurable.mono
      (B.startStopping.measurableSpace_mono hstart hstart_le) le_rfl
  have hs' : MeasurableSet[hstart.measurableSpace] s :=
    hτ.measurableSpace_mono hstart hτ_le s hs
  exact (Measurable.ite hs' measurable_const measurable_const).mul hcoeff

@[simp]
theorem after_interval
    (B : PredictableElementaryInterval ℱ)
    (τ : Ω → Time)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop Time))) :
    (B.after τ hτ).interval = B.interval.after τ :=
  rfl

@[simp]
theorem restrictAfter_interval
    (B : PredictableElementaryInterval ℱ)
    (τ : Ω → Time)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop Time)))
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s) :
    (B.restrictAfter τ hτ s hs).interval =
      (B.interval.after τ).mulCoefficient
        (fun ω => if ω ∈ s then 1 else 0) :=
  rfl

/-- Negate the coefficient of a predictable block. -/
noncomputable def neg
    (B : PredictableElementaryInterval ℱ) :
    PredictableElementaryInterval ℱ where
  interval := B.interval.neg
  startStopping := by
    simpa only [ElementaryInterval.neg,
      ElementaryInterval.mulCoefficient] using B.startStopping
  stopStopping := by
    simpa only [ElementaryInterval.neg,
      ElementaryInterval.mulCoefficient] using B.stopStopping
  coefficient_measurable := by
    change
      Measurable[B.startStopping.measurableSpace]
        (fun ω => (-1) * B.interval.coefficient ω)
    exact B.coefficient_measurable.const_mul (-1)

@[simp]
theorem neg_interval
    (B : PredictableElementaryInterval ℱ) :
    B.neg.interval = B.interval.neg :=
  rfl

/-- Multiply the coefficient of a predictable block by a positive scalar. -/
noncomputable def posSMul
    (c : ℝ) (_hc : 0 < c)
    (B : PredictableElementaryInterval ℱ) :
    PredictableElementaryInterval ℱ where
  interval := B.interval.mulCoefficient (fun _ => c)
  startStopping := B.startStopping
  stopStopping := B.stopStopping
  coefficient_measurable :=
    B.coefficient_measurable.const_mul c

@[simp]
theorem posSMul_interval
    (c : ℝ) (hc : 0 < c)
    (B : PredictableElementaryInterval ℱ) :
    (B.posSMul c hc).interval =
      B.interval.mulCoefficient (fun _ => c) :=
  rfl

end PredictableElementaryInterval

/-- A finite sum of predictable elementary interval blocks. -/
abbrev PredictableElementaryStrategy
    (ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)) :=
  List (PredictableElementaryInterval ℱ)

namespace PredictableElementaryStrategy

attribute [local instance] Classical.propDecidable

variable {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}

/-- Forget the filtered measurability proofs of a predictable strategy. -/
def toElementary
    (H : PredictableElementaryStrategy ℱ) :
    ElementaryStrategy Ω Time :=
  H.map PredictableElementaryInterval.interval

@[simp]
theorem toElementary_append
    (H K : PredictableElementaryStrategy ℱ) :
    toElementary (H ++ K) =
      toElementary H ++ toElementary K :=
  List.map_append

/-- Retain the predictable post-`τ` tail of every block. -/
noncomputable def after
    (H : PredictableElementaryStrategy ℱ)
    (τ : Ω → Time)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop Time))) :
    PredictableElementaryStrategy ℱ :=
  H.map fun B => B.after τ hτ

/-- Retain the predictable post-`τ` tail on an event known at `τ`. -/
noncomputable def restrictAfter
    (H : PredictableElementaryStrategy ℱ)
    (τ : Ω → Time)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop Time)))
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s) :
    PredictableElementaryStrategy ℱ :=
  H.map fun B => B.restrictAfter τ hτ s hs

/-- Negate every coefficient of a predictable strategy. -/
noncomputable def neg
    (H : PredictableElementaryStrategy ℱ) :
    PredictableElementaryStrategy ℱ :=
  H.map PredictableElementaryInterval.neg

/-- Multiply every coefficient by a positive scalar. -/
noncomputable def posSMul
    (c : ℝ) (hc : 0 < c)
    (H : PredictableElementaryStrategy ℱ) :
    PredictableElementaryStrategy ℱ :=
  H.map fun B => B.posSMul c hc

/--
Stop a predictable elementary strategy at a finite stopping time.

Algebraically this is the original strategy minus its predictable post-`τ`
tail.  This avoids the generally non-predictable raw blockwise stopping
operation.
-/
noncomputable def stopAt
    (H : PredictableElementaryStrategy ℱ)
    (τ : Ω → Time)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop Time))) :
    PredictableElementaryStrategy ℱ :=
  H ++ (H.after τ hτ).neg

@[simp]
theorem toElementary_after
    (H : PredictableElementaryStrategy ℱ)
    (τ : Ω → Time)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop Time))) :
    toElementary (H.after τ hτ) =
      ElementaryStrategy.after (toElementary H) τ := by
  induction H with
  | nil => rfl
  | cons B H ih =>
      change
        (B.after τ hτ).interval ::
            toElementary (after H τ hτ) =
          B.interval.after τ ::
            ElementaryStrategy.after (toElementary H) τ
      rw [PredictableElementaryInterval.after_interval, ih]

@[simp]
theorem toElementary_restrictAfter
    (H : PredictableElementaryStrategy ℱ)
    (τ : Ω → Time)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop Time)))
    (s : Set Ω) (hs : MeasurableSet[hτ.measurableSpace] s) :
    toElementary (H.restrictAfter τ hτ s hs) =
      ElementaryStrategy.restrict s
        (ElementaryStrategy.after (toElementary H) τ) := by
  induction H with
  | nil => rfl
  | cons B H ih =>
      change
        (B.restrictAfter τ hτ s hs).interval ::
            toElementary (restrictAfter H τ hτ s hs) =
          (B.interval.after τ).mulCoefficient
              (fun ω => if ω ∈ s then 1 else 0) ::
            ElementaryStrategy.restrict s
              (ElementaryStrategy.after (toElementary H) τ)
      rw [PredictableElementaryInterval.restrictAfter_interval, ih]

@[simp]
theorem toElementary_neg
    (H : PredictableElementaryStrategy ℱ) :
    toElementary H.neg =
      ElementaryStrategy.neg (toElementary H) := by
  induction H with
  | nil => rfl
  | cons B H ih =>
      change
        B.neg.interval :: toElementary (neg H) =
          B.interval.neg :: ElementaryStrategy.neg (toElementary H)
      rw [PredictableElementaryInterval.neg_interval, ih]

@[simp]
theorem toElementary_posSMul
    (c : ℝ) (hc : 0 < c)
    (H : PredictableElementaryStrategy ℱ) :
    toElementary (H.posSMul c hc) =
      ElementaryStrategy.mulCoefficient
        (fun _ => c) (toElementary H) := by
  induction H with
  | nil => rfl
  | cons B H ih =>
      change
        (B.posSMul c hc).interval ::
            toElementary (posSMul c hc H) =
          B.interval.mulCoefficient (fun _ => c) ::
            ElementaryStrategy.mulCoefficient
              (fun _ => c) (toElementary H)
      rw [PredictableElementaryInterval.posSMul_interval, ih]

@[simp]
theorem toElementary_stopAt
    (H : PredictableElementaryStrategy ℱ)
    (τ : Ω → Time)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop Time))) :
    toElementary (H.stopAt τ hτ) =
      toElementary H ++
        ElementaryStrategy.neg
          (ElementaryStrategy.after (toElementary H) τ) := by
  unfold stopAt
  rw [toElementary_append, toElementary_neg, toElementary_after]

theorem gain_stopAt
    (S : Time → Ω → ℝ)
    (H : PredictableElementaryStrategy ℱ)
    (τ : Ω → Time)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop Time)))
    (t : Time) (ω : Ω) :
    ElementaryStrategy.gain S
        (toElementary (H.stopAt τ hτ)) t ω =
      ElementaryStrategy.gain S (toElementary H)
        (min t (τ ω)) ω := by
  rw [toElementary_stopAt, ElementaryStrategy.gain_append,
    ElementaryStrategy.gain_neg, ElementaryStrategy.gain_after]
  ring

end PredictableElementaryStrategy

end FTAPTheorem42
