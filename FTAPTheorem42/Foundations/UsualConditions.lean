/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Process.Filtration

/-!
# Usual conditions for a filtration

The continuous-time stochastic part needs a right-continuous filtration whose
time-zero sigma algebra contains every null set.  Mathlib already supplies
`Filtration.IsRightContinuous`; this file packages it with completeness at
time zero and proves that the package is invariant under equivalent measures.
-/

open MeasureTheory

namespace FTAPTheorem42

variable {Ω Time : Type*} [MeasurableSpace Ω]
  [PartialOrder Time] [Zero Time]

namespace Filtration

/--
The filtration contains all `μ`-null sets at time zero.

Since `μ` is an outer measure on every set, this formulation includes every
subset of a measurable null set, as required by the usual conditions.
-/
def ContainsNullSetsAtZero
    (μ : Measure Ω)
    (ℱ : MeasureTheory.Filtration Time
      (inferInstance : MeasurableSpace Ω)) : Prop :=
  ∀ s : Set Ω, μ s = 0 → MeasurableSet[ℱ 0] s

/-- Right continuity together with completeness at time zero. -/
structure UsualConditions
    (μ : Measure Ω)
    (ℱ : MeasureTheory.Filtration Time
      (inferInstance : MeasurableSpace Ω)) : Prop where
  rightContinuous : ℱ.IsRightContinuous
  containsNullSetsAtZero : ContainsNullSetsAtZero μ ℱ

theorem UsualConditions.measurableSet_of_null
    {μ : Measure Ω}
    {ℱ : MeasureTheory.Filtration Time
      (inferInstance : MeasurableSpace Ω)}
    (h : UsualConditions μ ℱ) {t : Time} (hzero : 0 ≤ t)
    {s : Set Ω} (hs : μ s = 0) :
    MeasurableSet[ℱ t] s :=
  ℱ.mono hzero s (h.containsNullSetsAtZero s hs)

/-- The ambient measure space is complete under the usual conditions. -/
theorem UsualConditions.measure_isComplete
    {μ : Measure Ω}
    {ℱ : MeasureTheory.Filtration Time
      (inferInstance : MeasurableSpace Ω)}
    (h : UsualConditions μ ℱ) : μ.IsComplete := by
  rw [Measure.isComplete_iff]
  intro s hs
  exact measurableSet_of_filtration
    (h.containsNullSetsAtZero s hs)

/--
Completeness at time zero transfers from `μ` to `ν` when every `ν`-null set
is `μ`-null.
-/
theorem ContainsNullSetsAtZero.mono_ac
    {μ ν : Measure Ω}
    {ℱ : MeasureTheory.Filtration Time
      (inferInstance : MeasurableSpace Ω)}
    (h : ContainsNullSetsAtZero μ ℱ) (hμν : μ ≪ ν) :
    ContainsNullSetsAtZero ν ℱ := by
  intro s hs
  exact h s (hμν hs)

/-- The usual conditions transfer along absolute continuity in this direction. -/
theorem UsualConditions.mono_ac
    {μ ν : Measure Ω}
    {ℱ : MeasureTheory.Filtration Time
      (inferInstance : MeasurableSpace Ω)}
    (h : UsualConditions μ ℱ) (hμν : μ ≪ ν) :
    UsualConditions ν ℱ where
  rightContinuous := h.rightContinuous
  containsNullSetsAtZero := h.containsNullSetsAtZero.mono_ac hμν

/-- For equivalent measures, the usual conditions are equivalent. -/
theorem usualConditions_iff_of_mutuallyAbsolutelyContinuous
    {μ ν : Measure Ω}
    {ℱ : MeasureTheory.Filtration Time
      (inferInstance : MeasurableSpace Ω)}
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    UsualConditions μ ℱ ↔ UsualConditions ν ℱ := by
  constructor
  · exact fun h => h.mono_ac hμν
  · exact fun h => h.mono_ac hνμ

end Filtration

end FTAPTheorem42
