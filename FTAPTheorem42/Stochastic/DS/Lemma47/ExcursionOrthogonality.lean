/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.DS.Lemma47.ExcursionMartingale
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Orthogonality along the Lemma 4.7 excursion clock

Successive bounded stopping-time samples of a square-integrable martingale
have orthogonal increments.  This file proves the stopping-time Pythagoras
identity needed after predictable Hahn restriction.  It is independent of
the stochastic-integral restriction calculus.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal MeasureTheory NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace Lemma47ExcursionStopping

/-- An excursion sample is measurable in the sigma algebra of its own
stopping time. -/
theorem stronglyMeasurable_sample_measurableSpace
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [ℱ.IsRightContinuous]
    {X : Process Ω} (hX : StronglyAdapted ℱ X)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (T : ℝ≥0) (n : ℕ) :
    StronglyMeasurable[
      (time_isStoppingTime hX hXRight T n).measurableSpace]
      (sample X T n) := by
  let hτ := time_isStoppingTime hX hXRight T n
  have hProgressive : IsStronglyProgressive ℱ X :=
    StronglyAdapted.isStronglyProgressive_of_rightContinuous hX hXRight
  have hStoppedEq : MeasureTheory.stoppedValue X
      (fun ω => (time X T n ω : WithTop ℝ≥0)) = sample X T n := by
    funext ω
    unfold sample MeasureTheory.stoppedValue
    rw [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
  rw [← hStoppedEq]
  exact (MeasureTheory.measurable_stoppedValue hProgressive hτ).stronglyMeasurable

/-- The next excursion increment has conditional mean zero at the current
excursion time. -/
theorem condExp_increment_ae_eq_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [ℱ.IsRightContinuous] [SigmaFiniteFiltration μ ℱ]
    {X : Process Ω} (hX : Martingale X ℱ μ)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (T : ℝ≥0) (n : ℕ) :
    μ[increment X T n |
      (time_isStoppingTime hX.stronglyAdapted hXRight T n).measurableSpace]
        =ᵐ[μ] 0 := by
  let hτ := time_isStoppingTime hX.stronglyAdapted hXRight T n
  have hCurrentMeas : StronglyMeasurable[hτ.measurableSpace]
      (sample X T n) :=
    stronglyMeasurable_sample_measurableSpace
      hX.stronglyAdapted hXRight T n
  have hCurrentInt := integrable_sample hX hXRight T n
  have hCurrentSelf :
      μ[sample X T n | hτ.measurableSpace] = sample X T n :=
    condExp_of_stronglyMeasurable (μ := μ) hτ.measurableSpace_le
      hCurrentMeas hCurrentInt
  have hNext :
      μ[sample X T (n + 1) | hτ.measurableSpace] =ᵐ[μ]
        sample X T n := by
    simpa only [hτ] using
      (condExp_sample_succ_ae_eq_sample hX hXRight T n)
  filter_upwards [
    condExp_sub (integrable_sample hX hXRight T (n + 1))
      hCurrentInt hτ.measurableSpace,
    hNext] with ω hsub hnext
  change μ[sample X T (n + 1) - sample X T n |
      hτ.measurableSpace] ω = 0
  rw [hsub]
  change μ[sample X T (n + 1) | hτ.measurableSpace] ω -
      μ[sample X T n | hτ.measurableSpace] ω = 0
  rw [hnext, congrFun hCurrentSelf ω, sub_self]

/-- Difference between the `k`-th sample and the initial sample. -/
noncomputable def accumulatedIncrement
    (X : Process Ω) (T : ℝ≥0) (k : ℕ) : Ω → ℝ :=
  fun ω => sample X T k ω - sample X T 0 ω

omit [MeasurableSpace Ω] in
theorem accumulatedIncrement_succ
    (X : Process Ω) (T : ℝ≥0) (k : ℕ) :
    accumulatedIncrement X T (k + 1) =
      accumulatedIncrement X T k + increment X T k := by
  funext ω
  simp only [accumulatedIncrement, increment, Pi.add_apply]
  ring

/-- The accumulated increment is square-integrable whenever every unit
excursion has a square-integrable jump envelope. -/
theorem accumulatedIncrement_memLp_two
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [ℱ.IsRightContinuous]
    {X : Process Ω} (hX : StronglyAdapted ℱ X)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (hXLeft : ProcessHasLeftLimits X)
    (T : ℝ≥0) (J : ℕ → Ω → ℝ)
    (hJ : ∀ n ω, 0 ≤ J n ω)
    (hJMem : ∀ n, MemLp (J n) (2 : ℝ≥0∞) μ)
    (hJump : ∀ n, ∀ᵐ ω ∂μ, ∀ t,
      |processLeftJump (displacementAfter X (time X T n)) t ω| ≤ J n ω)
    (k : ℕ) :
    MemLp (accumulatedIncrement X T k) (2 : ℝ≥0∞) μ := by
  induction k with
  | zero =>
      have hzero : accumulatedIncrement X T 0 = 0 := by
        funext ω
        simp [accumulatedIncrement]
      rw [hzero]
      exact MemLp.zero
  | succ k ih =>
      rw [accumulatedIncrement_succ]
      exact ih.add (increment_memLp_two hX hXRight hXLeft
        T J hJ hJMem hJump k)

/-- The accumulated past is measurable at the current excursion stopping
time. -/
theorem stronglyMeasurable_accumulatedIncrement_measurableSpace
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [ℱ.IsRightContinuous]
    {X : Process Ω} (hX : StronglyAdapted ℱ X)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (T : ℝ≥0) (k : ℕ) :
    StronglyMeasurable[
      (time_isStoppingTime hX hXRight T k).measurableSpace]
      (accumulatedIncrement X T k) := by
  let hk := time_isStoppingTime hX hXRight T k
  have hCurrent : StronglyMeasurable[hk.measurableSpace]
      (sample X T k) :=
    stronglyMeasurable_sample_measurableSpace hX hXRight T k
  have hInitialRaw :=
    stronglyMeasurable_sample_measurableSpace hX hXRight T 0
  have hInitial : StronglyMeasurable[hk.measurableSpace]
      (sample X T 0) :=
    hInitialRaw.mono
      ((time_isStoppingTime hX hXRight T 0).measurableSpace_mono hk
        (fun ω => by
          rw [time_zero]
          exact bot_le))
  exact hCurrent.sub hInitial

/-- The accumulated past is orthogonal to the next excursion increment. -/
theorem integral_accumulatedIncrement_mul_increment_eq_zero
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [ℱ.IsRightContinuous] [SigmaFiniteFiltration μ ℱ]
    {X : Process Ω} (hX : Martingale X ℱ μ)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (hXLeft : ProcessHasLeftLimits X)
    (T : ℝ≥0) (J : ℕ → Ω → ℝ)
    (hJ : ∀ n ω, 0 ≤ J n ω)
    (hJMem : ∀ n, MemLp (J n) (2 : ℝ≥0∞) μ)
    (hJump : ∀ n, ∀ᵐ ω ∂μ, ∀ t,
      |processLeftJump (displacementAfter X (time X T n)) t ω| ≤ J n ω)
    (k : ℕ) :
    (∫ ω, accumulatedIncrement X T k ω * increment X T k ω ∂μ) = 0 := by
  let hk := time_isStoppingTime hX.stronglyAdapted hXRight T k
  let F := accumulatedIncrement X T k
  let G := increment X T k
  have hFMem := accumulatedIncrement_memLp_two hX.stronglyAdapted
    hXRight hXLeft T J hJ hJMem hJump k
  have hGMem := increment_memLp_two hX.stronglyAdapted hXRight hXLeft
    T J hJ hJMem hJump k
  have hFMeas : StronglyMeasurable[hk.measurableSpace] F :=
    stronglyMeasurable_accumulatedIncrement_measurableSpace
      hX.stronglyAdapted hXRight T k
  have hGInt : Integrable G μ := hGMem.integrable (by norm_num)
  have hFGInt : Integrable (F * G) μ := hFMem.integrable_mul hGMem
  have hCondG : μ[G | hk.measurableSpace] =ᵐ[μ] 0 :=
    condExp_increment_ae_eq_zero (μ := μ) hX hXRight T k
  have hPull : μ[F * G | hk.measurableSpace] =ᵐ[μ]
      F * μ[G | hk.measurableSpace] :=
    condExp_mul_of_stronglyMeasurable_left hFMeas hFGInt hGInt
  calc
    (∫ ω, F ω * G ω ∂μ) =
        ∫ ω, μ[F * G | hk.measurableSpace] ω ∂μ :=
      (integral_condExp hk.measurableSpace_le).symm
    _ = ∫ _ω, (0 : ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hPull, hCondG] with ω hpull hzero
      rw [hpull]
      change F ω * μ[G | hk.measurableSpace] ω = 0
      simpa only [Pi.zero_apply, mul_zero] using congrArg (F ω * ·) hzero
    _ = 0 := by simp

/-- Pythagoras identity for the accumulated stopped-time excursions. -/
theorem integral_sq_accumulatedIncrement_succ
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [ℱ.IsRightContinuous] [SigmaFiniteFiltration μ ℱ]
    {X : Process Ω} (hX : Martingale X ℱ μ)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (hXLeft : ProcessHasLeftLimits X)
    (T : ℝ≥0) (J : ℕ → Ω → ℝ)
    (hJ : ∀ n ω, 0 ≤ J n ω)
    (hJMem : ∀ n, MemLp (J n) (2 : ℝ≥0∞) μ)
    (hJump : ∀ n, ∀ᵐ ω ∂μ, ∀ t,
      |processLeftJump (displacementAfter X (time X T n)) t ω| ≤ J n ω)
    (k : ℕ) :
    (∫ ω, accumulatedIncrement X T (k + 1) ω ^ 2 ∂μ) =
      (∫ ω, accumulatedIncrement X T k ω ^ 2 ∂μ) +
        ∫ ω, increment X T k ω ^ 2 ∂μ := by
  let F := accumulatedIncrement X T k
  let G := increment X T k
  have hFMem := accumulatedIncrement_memLp_two hX.stronglyAdapted
    hXRight hXLeft T J hJ hJMem hJump k
  have hGMem := increment_memLp_two hX.stronglyAdapted hXRight hXLeft
    T J hJ hJMem hJump k
  have hFInt : Integrable (F ^ 2) μ := hFMem.integrable_sq
  have hGInt : Integrable (G ^ 2) μ := hGMem.integrable_sq
  have hFGInt : Integrable (F * G) μ := hFMem.integrable_mul hGMem
  have hCross : (∫ ω, F ω * G ω ∂μ) = 0 :=
    integral_accumulatedIncrement_mul_increment_eq_zero hX hXRight
      hXLeft T J hJ hJMem hJump k
  rw [accumulatedIncrement_succ]
  have hOuterAdd :
      (∫ ω, (F ω ^ 2 + G ω ^ 2) + 2 * (F ω * G ω) ∂μ) =
        (∫ ω, F ω ^ 2 + G ω ^ 2 ∂μ) +
          ∫ ω, 2 * (F ω * G ω) ∂μ := by
    simpa only [Pi.add_apply, Pi.pow_apply, Pi.mul_apply,
      Pi.smul_apply, smul_eq_mul] using
      integral_add (hFInt.add hGInt) (hFGInt.const_mul 2)
  have hInnerAdd :
      (∫ ω, F ω ^ 2 + G ω ^ 2 ∂μ) =
        (∫ ω, F ω ^ 2 ∂μ) + ∫ ω, G ω ^ 2 ∂μ := by
    simpa only [Pi.add_apply, Pi.pow_apply] using integral_add hFInt hGInt
  have hScale :
      (∫ ω, 2 * (F ω * G ω) ∂μ) =
        2 * ∫ ω, F ω * G ω ∂μ := by
    simpa only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul] using
      integral_const_mul (μ := μ) 2 (F * G)
  calc
    (∫ ω, (F ω + G ω) ^ 2 ∂μ) =
        ∫ ω, F ω ^ 2 + G ω ^ 2 + 2 * (F ω * G ω) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by ring
    _ = (∫ ω, F ω ^ 2 ∂μ) + (∫ ω, G ω ^ 2 ∂μ) +
        2 * ∫ ω, F ω * G ω ∂μ := by
      rw [hOuterAdd, hInnerAdd, hScale]
    _ = (∫ ω, F ω ^ 2 ∂μ) + ∫ ω, G ω ^ 2 ∂μ := by
      rw [hCross, mul_zero, add_zero]

/-- The expected square of the first `k` accumulated excursions is at most
`4k` when every excursion jump envelope has `L²` norm at most one. -/
theorem integral_sq_accumulatedIncrement_le_four_mul
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [ℱ.IsRightContinuous] [SigmaFiniteFiltration μ ℱ]
    {X : Process Ω} (hX : Martingale X ℱ μ)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (hXLeft : ProcessHasLeftLimits X)
    (T : ℝ≥0) (J : ℕ → Ω → ℝ)
    (hJ : ∀ n ω, 0 ≤ J n ω)
    (hJMem : ∀ n, MemLp (J n) (2 : ℝ≥0∞) μ)
    (hJump : ∀ n, ∀ᵐ ω ∂μ, ∀ t,
      |processLeftJump (displacementAfter X (time X T n)) t ω| ≤ J n ω)
    (hJNorm : ∀ n, eLpNorm (J n) (2 : ℝ≥0∞) μ ≤ 1)
    (k : ℕ) :
    (∫ ω, accumulatedIncrement X T k ω ^ 2 ∂μ) ≤ 4 * k := by
  induction k with
  | zero => simp [accumulatedIncrement]
  | succ k ih =>
      rw [integral_sq_accumulatedIncrement_succ hX hXRight hXLeft
        T J hJ hJMem hJump k]
      have hIncrement := integral_norm_increment_sq_le_four
        hX.stronglyAdapted hXRight hXLeft T J hJ hJMem hJump k (hJNorm k)
      have hSq : (fun ω => ‖increment X T k ω‖ ^ 2) =
          fun ω => increment X T k ω ^ 2 := by
        funext ω
        simp only [Real.norm_eq_abs, sq_abs]
      rw [hSq] at hIncrement
      norm_num [Nat.cast_succ]
      linarith

end Lemma47ExcursionStopping

end FTAPTheorem42
