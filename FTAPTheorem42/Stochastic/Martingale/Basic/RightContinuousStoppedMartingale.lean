/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.HahnStopping
import FTAPTheorem42.Stochastic.Martingale.Basic.BoundedStoppingOptionalSampling
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-!
# Stopping a right-continuous martingale

This file upgrades the bounded optional-sampling result to the process-level
statement needed to synchronize continuous-time localizers.  No countability
assumption is imposed on the stopping time; right continuity supplies the
measurability and integrability of its stopped values.
-/

open Filter MeasureTheory Set Topology
open scoped MeasureTheory NNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace RightContinuousStoppedMartingale

/-- A strongly adapted right-continuous process remains strongly adapted
after stopping at an arbitrary stopping time. -/
theorem StronglyAdapted.stoppedProcess_of_rightContinuous
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {M : ℝ≥0 → Ω → ℝ} (hM : StronglyAdapted ℱ M)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    (hMRight : ∀ ω t,
      ContinuousWithinAt (M · ω) (Set.Ici t) t) :
    StronglyAdapted ℱ (MeasureTheory.stoppedProcess M τ) := by
  intro t
  have hsample :=
    StoppingTimeRightApproximation.stronglyMeasurable_sample_of_boundedStoppingTime_filtration
      hM (boundedTime_isStoppingTime hτ t)
      (boundedTime_le t τ) hMRight
  simpa only [sample_boundedTime_eq_stoppedProcess] using hsample

omit [MeasurableSpace Ω] in
/-- Stopping preserves pathwise right continuity. -/
theorem stoppedProcess_rightContinuous
    (M : ℝ≥0 → Ω → ℝ) {τ : Ω → WithTop ℝ≥0}
    (hMRight : ∀ ω t,
      ContinuousWithinAt (M · ω) (Set.Ici t) t) :
    ∀ ω t, ContinuousWithinAt
      (MeasureTheory.stoppedProcess M τ · ω) (Set.Ici t) t := by
  intro ω t
  by_cases hτTop : τ ω = ⊤
  · have heq : (fun u => MeasureTheory.stoppedProcess M τ u ω) =
        fun u => M u ω := by
      funext u
      rw [MeasureTheory.stoppedProcess_eq_of_le]
      simp only [hτTop, le_top]
    rw [heq]
    exact hMRight ω t
  · lift τ ω to ℝ≥0 using hτTop with s hs
    have heq : (fun u => MeasureTheory.stoppedProcess M τ u ω) =
        fun u => M (min u s) ω := by
      funext u
      simp only [MeasureTheory.stoppedProcess]
      rw [← hs, ← WithTop.coe_min,
        WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
    rw [heq]
    apply (hMRight ω (min t s)).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact (ContinuousAt.continuousWithinAt
        (continuousAt_id.min (continuousAt_const :
          ContinuousAt (fun _ : ℝ≥0 => s) t))).tendsto
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact min_le_min_right s hu

omit [MeasurableSpace Ω] in
/-- Multiplication by a fixed event indicator preserves pathwise right
continuity. -/
theorem indicator_rightContinuous
    (X : ℝ≥0 → Ω → ℝ) (B : Set Ω)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t) :
    ∀ ω t, ContinuousWithinAt
      (fun u => B.indicator (X u) ω) (Set.Ici t) t := by
  intro ω t
  by_cases hω : ω ∈ B
  · simpa only [Set.indicator_of_mem hω] using hXRight ω t
  · simpa only [Set.indicator_of_notMem hω] using
      (continuousWithinAt_const :
        ContinuousWithinAt (fun _ : ℝ≥0 => (0 : ℝ)) (Set.Ici t) t)

/-- The continuation time agrees with `min j τ` after time `i` and is
globally bounded below by `i`, which permits deterministic-time optional
sampling. -/
noncomputable def continuationTime
    (i j : ℝ≥0) (τ : Ω → WithTop ℝ≥0) : Ω → ℝ≥0 :=
  fun ω => max i (boundedTime j τ ω)

theorem continuationTime_isStoppingTime
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    (i j : ℝ≥0) :
    IsStoppingTime ℱ
      (fun ω => (continuationTime i j τ ω : WithTop ℝ≥0)) := by
  have hmax := (isStoppingTime_const ℱ i).max
    (boundedTime_isStoppingTime hτ j)
  simpa only [continuationTime, WithTop.coe_max] using hmax

omit [MeasurableSpace Ω] in
theorem le_continuationTime
    (i j : ℝ≥0) (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    i ≤ continuationTime i j τ ω :=
  le_max_left _ _

omit [MeasurableSpace Ω] in
theorem continuationTime_le
    {i j : ℝ≥0} (hij : i ≤ j) (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    continuationTime i j τ ω ≤ j :=
  max_le hij (boundedTime_le j τ ω)

/-- A right-continuous martingale stopped at an arbitrary continuous-time
stopping time is again a martingale. -/
theorem Martingale.stoppedProcess_of_rightContinuous
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [SigmaFiniteFiltration μ ℱ]
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ μ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    (hMRight : ∀ ω t,
      ContinuousWithinAt (M · ω) (Set.Ici t) t) :
    Martingale (MeasureTheory.stoppedProcess M τ) ℱ μ := by
  refine ⟨StronglyAdapted.stoppedProcess_of_rightContinuous
    hM.stronglyAdapted hτ hMRight, ?_⟩
  intro i j hij
  let A : Set Ω := {ω | τ ω ≤ (i : WithTop ℝ≥0)}
  let X : Ω → ℝ := MeasureTheory.stoppedProcess M τ i
  let Y : Ω → ℝ := MeasureTheory.stoppedProcess M τ j
  let π : Ω → ℝ≥0 := continuationTime i j τ
  let Z : Ω → ℝ := fun ω => M (π ω) ω
  have hA : MeasurableSet[ℱ i] A := by
    simpa only [A] using hτ.measurableSet_le i
  have hπStop : IsStoppingTime ℱ (fun ω => (π ω : WithTop ℝ≥0)) := by
    simpa only [π] using continuationTime_isStoppingTime hτ i j
  have hπLower : ∀ ω, i ≤ π ω := by
    intro ω
    exact le_continuationTime i j τ ω
  have hπUpper : ∀ ω, π ω ≤ j := by
    intro ω
    exact continuationTime_le hij τ ω
  have hXInt : Integrable X μ := by
    change Integrable (fun ω => M (boundedTime i τ ω) ω) μ
    exact FTAPTheorem42.Martingale.integrable_sample_of_boundedStoppingTime hM
      (boundedTime_isStoppingTime hτ i) (boundedTime_le i τ) hMRight
  have hZInt : Integrable Z μ := by
    exact FTAPTheorem42.Martingale.integrable_sample_of_boundedStoppingTime hM
      hπStop hπUpper hMRight
  have hXMeas : StronglyMeasurable[ℱ i] X := by
    exact StronglyAdapted.stoppedProcess_of_rightContinuous
      hM.stronglyAdapted hτ hMRight i
  have hcondX : μ[X | ℱ i] = X :=
    condExp_of_stronglyMeasurable (ℱ.le i) hXMeas hXInt
  have hcondZ : μ[Z | ℱ i] =ᵐ[μ] fun ω => M i ω := by
    have hconstRange :
        (Set.range fun _ : Ω => (i : WithTop ℝ≥0)).Countable := by
      apply Set.Countable.mono ?_ (Set.countable_singleton (i : WithTop ℝ≥0))
      rintro _ ⟨ω, rfl⟩
      exact Set.mem_singleton _
    have hOptional :=
      FTAPTheorem42.Martingale.condExp_sampled_ae_eq_of_countableRange_lower hM
      (isStoppingTime_const ℱ i) hπStop
      hconstRange
      hπLower hπUpper hMRight
    simpa only [IsStoppingTime.measurableSpace_const, Z, π] using hOptional
  have hYDecomp : Y = A.indicator X + Aᶜ.indicator Z := by
    funext ω
    change Y ω = A.indicator X ω + Aᶜ.indicator Z ω
    by_cases hω : ω ∈ A
    · have hτi : τ ω ≤ (i : WithTop ℝ≥0) := hω
      have hτj : τ ω ≤ (j : WithTop ℝ≥0) := hτi.trans (by exact_mod_cast hij)
      have hωc : ω ∉ Aᶜ := by simpa only [Set.mem_compl_iff, not_not]
      rw [Set.indicator_of_mem hω, Set.indicator_of_notMem hωc, add_zero]
      dsimp only [X, Y]
      rw [MeasureTheory.stoppedProcess_eq_of_ge hτj,
        MeasureTheory.stoppedProcess_eq_of_ge hτi]
    · have hiτ : (i : WithTop ℝ≥0) < τ ω := lt_of_not_ge hω
      have hπEq : π ω = boundedTime j τ ω := by
        apply max_eq_right
        exact WithTop.coe_le_coe.mp <| by
          rw [coe_boundedTime]
          exact le_min (by exact_mod_cast hij) hiτ.le
      have hωc : ω ∈ Aᶜ := by simpa only [Set.mem_compl_iff]
      rw [Set.indicator_of_notMem hω, Set.indicator_of_mem hωc, zero_add]
      dsimp only [Y, Z]
      rw [hπEq]
      exact (sample_boundedTime_eq_stoppedProcess M τ j ω).symm
  have hXEqMiOnCompl : Aᶜ.indicator (fun ω => M i ω) = Aᶜ.indicator X := by
    funext ω
    by_cases hω : ω ∈ Aᶜ
    · have hωc : ω ∈ Aᶜ := hω
      change ¬τ ω ≤ (i : WithTop ℝ≥0) at hω
      have hnot : ¬τ ω ≤ (i : WithTop ℝ≥0) := hω
      have hiτ : (i : WithTop ℝ≥0) ≤ τ ω := (lt_of_not_ge hnot).le
      rw [Set.indicator_of_mem hωc, Set.indicator_of_mem hωc]
      dsimp only [X]
      rw [MeasureTheory.stoppedProcess_eq_of_le hiτ]
    · simp only [Set.indicator_of_notMem hω]
  change μ[Y | ℱ i] =ᵐ[μ] X
  rw [hYDecomp]
  calc
    μ[A.indicator X + Aᶜ.indicator Z | ℱ i] =ᵐ[μ]
        μ[A.indicator X | ℱ i] + μ[Aᶜ.indicator Z | ℱ i] :=
      condExp_add (hXInt.indicator (ℱ.le i A hA))
        (hZInt.indicator (ℱ.le i Aᶜ hA.compl)) (ℱ i)
    _ =ᵐ[μ] A.indicator μ[X | ℱ i] + Aᶜ.indicator μ[Z | ℱ i] :=
      (condExp_indicator hXInt hA).fun_add
        (condExp_indicator hZInt hA.compl)
    _ =ᵐ[μ] A.indicator X + Aᶜ.indicator (fun ω => M i ω) := by
      filter_upwards [hcondZ] with ω hZω
      change A.indicator μ[X | ℱ i] ω + Aᶜ.indicator μ[Z | ℱ i] ω =
        A.indicator X ω + Aᶜ.indicator (fun ω => M i ω) ω
      by_cases hωA : ω ∈ A
      · have hωAc : ω ∉ Aᶜ := by
          simpa only [Set.mem_compl_iff, not_not]
        rw [Set.indicator_of_mem hωA, Set.indicator_of_notMem hωAc,
          Set.indicator_of_mem hωA, Set.indicator_of_notMem hωAc,
          add_zero, congrFun hcondX ω]
        simp
      · have hωAc : ω ∈ Aᶜ := by simpa only [Set.mem_compl_iff]
        rw [Set.indicator_of_notMem hωA, Set.indicator_of_mem hωAc,
          Set.indicator_of_notMem hωA, Set.indicator_of_mem hωAc,
          zero_add, hZω]
        simp
    _ =ᵐ[μ] X := by
      rw [hXEqMiOnCompl]
      exact Filter.Eventually.of_forall fun ω =>
        congrFun (Set.indicator_self_add_compl A X) ω

end RightContinuousStoppedMartingale

/-- Deterministic stopping preserves a right-continuous martingale. -/
theorem martingale_deterministicallyStopped
    {mu : Measure Ω} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    [SigmaFiniteFiltration mu F]
    {M : Process Ω} (hM : Martingale M F mu)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) :
    Martingale (deterministicallyStoppedProcess M T) F mu := by
  exact
    RightContinuousStoppedMartingale.Martingale.stoppedProcess_of_rightContinuous
      hM (isStoppingTime_const F T) hMRight

end FTAPTheorem42
