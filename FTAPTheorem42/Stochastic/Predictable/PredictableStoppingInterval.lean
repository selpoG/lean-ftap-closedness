/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Predictable.PredictableStoppingGraph
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableStrategyAlgebra

/-!
# Predictable stochastic intervals

For a finite stopping time `τ`, the stochastic interval `(0, τ]` is a
predictable subset of time--sample space.  This is the interval used to stop
and rescale the integrands in the proof of Lemma 4.7.
-/

open MeasureTheory Set
open scoped NNReal

namespace FTAPTheorem42

variable {Ω : Type*}

/-- The predictable lift of an event at a possibly infinite stopping time.
Its section is the set strictly after the stopping time. -/
def stoppingTimeEventPredictableLiftTop
    (τ : Ω → WithTop ℝ≥0) (B : Set Ω) : Set (ℝ≥0 × Ω) :=
  ⋃ q : ℚ, Set.Ioi (Real.toNNReal q) ×ˢ
    (B ∩ {ω | τ ω ≤ (Real.toNNReal q : WithTop ℝ≥0)})

/-- The stochastic interval `(0, τ]` for a possibly infinite random time. -/
def stochasticIntervalIocZeroTop
    (τ : Ω → WithTop ℝ≥0) : Set (ℝ≥0 × Ω) :=
  (Set.Ioi 0 ×ˢ Set.univ) \ stoppingTimeEventPredictableLiftTop τ Set.univ

/-- The top-valued rational lift is precisely the set strictly after the
random time. -/
theorem mem_stoppingTimeEventPredictableLiftTop_univ_iff
    (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    (t, ω) ∈ stoppingTimeEventPredictableLiftTop τ Set.univ ↔
      τ ω < (t : WithTop ℝ≥0) := by
  simp only [stoppingTimeEventPredictableLiftTop, Set.mem_iUnion,
    Set.mem_prod, Set.mem_Ioi, Set.mem_inter_iff, Set.mem_univ, true_and]
  constructor
  · rintro ⟨q, hqt, hτq⟩
    exact hτq.trans_lt (WithTop.coe_lt_coe.mpr hqt)
  · intro hτt
    have hτne : τ ω ≠ ⊤ := ne_top_of_lt hτt
    lift τ ω to ℝ≥0 using hτne with s hs
    have hst : s < t := by
      apply WithTop.coe_lt_coe.mp
      simpa only [hs] using hτt
    obtain ⟨q, -, hsq, hqt⟩ :=
      (NNReal.lt_iff_exists_rat_btwn s t).1 hst
    refine ⟨q, hqt, ?_⟩
    change τ ω ≤ (Real.toNNReal q : WithTop ℝ≥0)
    rw [← hs]
    exact WithTop.coe_le_coe.mpr hsq.le

/-- The rational lift at a possibly infinite stopping time is predictable. -/
theorem IsStoppingTime.measurableSet_stoppingTimeEventPredictableLiftTop
    [m0 : MeasurableSpace Ω]
    {ℱ : Filtration ℝ≥0 m0} {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime ℱ τ)
    {B : Set Ω} (hB : MeasurableSet[hτ.measurableSpace] B) :
    MeasurableSet[ℱ.predictable]
      (stoppingTimeEventPredictableLiftTop τ B) := by
  unfold stoppingTimeEventPredictableLiftTop
  apply MeasurableSet.iUnion
  intro q
  apply measurableSet_predictable_Ioi_prod
  exact (hτ.measurableSet B).1 hB |>.2 (Real.toNNReal q)

/-- The stochastic interval `(0, τ]` is predictable also when `τ` may be
infinite. -/
theorem IsStoppingTime.measurableSet_stochasticIntervalIocZeroTop
    [m0 : MeasurableSpace Ω]
    {ℱ : Filtration ℝ≥0 m0} {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime ℱ τ) :
    MeasurableSet[ℱ.predictable] (stochasticIntervalIocZeroTop τ) := by
  apply (measurableSet_predictable_Ioi_prod
      (show MeasurableSet[ℱ 0] Set.univ from MeasurableSet.univ)).diff
  exact IsStoppingTime.measurableSet_stoppingTimeEventPredictableLiftTop hτ
    (MeasurableSet.univ : MeasurableSet[hτ.measurableSpace] Set.univ)

@[simp]
theorem mem_stochasticIntervalIocZeroTop_iff
    (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    (t, ω) ∈ stochasticIntervalIocZeroTop τ ↔
      0 < t ∧ (t : WithTop ℝ≥0) ≤ τ ω := by
  rw [stochasticIntervalIocZeroTop, Set.mem_sdiff,
    mem_stoppingTimeEventPredictableLiftTop_univ_iff]
  simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_univ, and_true, not_lt]

/-- The predictable stochastic interval `(0, τ]`.  The rational union in
`stoppingTimeEventPredictableLift` represents the complementary condition
`τ ω < t`. -/
def stochasticIntervalIocZero (τ : Ω → ℝ≥0) : Set (ℝ≥0 × Ω) :=
  (Set.Ioi 0 ×ˢ Set.univ) \ stoppingTimeEventPredictableLift τ Set.univ

/-- The rational predictable lift of the whole sample space is precisely the
set strictly after a finite random time. -/
theorem mem_stoppingTimeEventPredictableLift_univ_iff
    (τ : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    (t, ω) ∈ stoppingTimeEventPredictableLift τ Set.univ ↔ τ ω < t := by
  simp only [stoppingTimeEventPredictableLift, Set.mem_iUnion, Set.mem_prod,
    Set.mem_Ioi, Set.mem_inter_iff, Set.mem_univ, true_and]
  constructor
  · rintro ⟨q, hqt, hτq⟩
    exact hτq.trans_lt hqt
  · intro hτt
    obtain ⟨q, -, hτq, hqt⟩ :=
      (NNReal.lt_iff_exists_rat_btwn (τ ω) t).1 hτt
    exact ⟨q, hqt, hτq.le⟩

/-- The rational lift of an event known at `τ` is predictable. -/
theorem IsStoppingTime.measurableSet_stoppingTimeEventPredictableLift
    [m0 : MeasurableSpace Ω]
    {ℱ : Filtration ℝ≥0 m0} {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    {B : Set Ω} (hB : MeasurableSet[hτ.measurableSpace] B) :
    MeasurableSet[ℱ.predictable] (stoppingTimeEventPredictableLift τ B) := by
  unfold stoppingTimeEventPredictableLift
  apply MeasurableSet.iUnion
  intro q
  apply measurableSet_predictable_Ioi_prod
  have hBq := (hτ.measurableSet B).1 hB |>.2 (Real.toNNReal q)
  simpa only [WithTop.coe_le_coe] using hBq

/-- The stochastic interval `(0, τ]` of a finite stopping time is
predictable. -/
theorem IsStoppingTime.measurableSet_stochasticIntervalIocZero
    [m0 : MeasurableSpace Ω]
    {ℱ : Filtration ℝ≥0 m0} {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) :
    MeasurableSet[ℱ.predictable] (stochasticIntervalIocZero τ) := by
  apply (measurableSet_predictable_Ioi_prod
      (show MeasurableSet[ℱ 0] Set.univ from MeasurableSet.univ)).diff
  exact IsStoppingTime.measurableSet_stoppingTimeEventPredictableLift hτ
    (MeasurableSet.univ : MeasurableSet[hτ.measurableSpace] Set.univ)

@[simp]
theorem mem_stochasticIntervalIocZero_iff
    (τ : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    (t, ω) ∈ stochasticIntervalIocZero τ ↔ 0 < t ∧ t ≤ τ ω := by
  rw [stochasticIntervalIocZero, Set.mem_sdiff,
    mem_stoppingTimeEventPredictableLift_univ_iff]
  simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_univ, and_true, not_lt]

end FTAPTheorem42
