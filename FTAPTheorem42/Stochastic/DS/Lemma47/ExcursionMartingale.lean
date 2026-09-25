/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Martingale.Basic.BoundedStoppingOptionalSampling
import FTAPTheorem42.Stochastic.Martingale.Basic.DoobL2Maximal
import FTAPTheorem42.Stochastic.DS.Lemma47.ExcursionStopping
import FTAPTheorem42.Stochastic.DS.Lemma47.Probability

/-!
# Martingale increments on the Lemma 4.7 excursion clock

Bounded optional sampling turns consecutive chronological excursions into
mean-zero increments.  The first-passage overshoot estimate supplies their
`L²` bound from one displacement-jump envelope.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal MeasureTheory NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace Lemma47ExcursionStopping

/-- Value sampled at the `n`-th clamped excursion time. -/
noncomputable def sample
    (X : Process Ω) (T : ℝ≥0) (n : ℕ) : Ω → ℝ :=
  fun ω => X (time X T n ω) ω

/-- Martingale increment across one clamped excursion. -/
noncomputable def increment
    (X : Process Ω) (T : ℝ≥0) (n : ℕ) : Ω → ℝ :=
  fun ω => sample X T (n + 1) ω - sample X T n ω

/-- Event that the `n`-th unit excursion is completed by the clamped
horizon. -/
def completedEvent
    (X : Process Ω) (T : ℝ≥0) (n : ℕ) : Set Ω :=
  {ω | 1 ≤ |increment X T n ω|}

theorem stronglyMeasurable_sample
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [ℱ.IsRightContinuous]
    {X : Process Ω} (hX : StronglyAdapted ℱ X)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (T : ℝ≥0) (n : ℕ) :
    StronglyMeasurable (sample X T n) := by
  exact StoppingTimeRightApproximation.stronglyMeasurable_sample_of_boundedStoppingTime
    hX (time_isStoppingTime hX hXRight T n) (time_le X T n) hXRight

theorem stronglyMeasurable_increment
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [ℱ.IsRightContinuous]
    {X : Process Ω} (hX : StronglyAdapted ℱ X)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (T : ℝ≥0) (n : ℕ) :
    StronglyMeasurable (increment X T n) :=
  (stronglyMeasurable_sample hX hXRight T (n + 1)).sub
    (stronglyMeasurable_sample hX hXRight T n)

omit [MeasurableSpace Ω] in
/-- Earlier completed-excursion events contain later ones.  The key point is
that an incomplete excursion reaches the clamped horizon, which is absorbing
for every subsequent excursion time. -/
theorem completedEvent_antitone
    (X : Process Ω)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (T : ℝ≥0) {n m : ℕ} (hnm : n ≤ m) :
    completedEvent X T m ⊆ completedEvent X T n := by
  intro ω hm
  by_cases heq : n = m
  · simpa only [heq] using hm
  have hlt : n < m := lt_of_le_of_ne hnm heq
  by_contra hn
  have hnsmall : |increment X T n ω| < 1 := lt_of_not_ge hn
  have hnext : time X T (n + 1) ω = T := by
    apply time_succ_eq_horizon_of_abs_sub_lt_one X hXRight T n ω
    exact hnsmall
  have hmTime : time X T m ω = T :=
    time_eq_horizon_of_le_of_eq X T ω (Nat.succ_le_iff.2 hlt) hnext
  have hmSuccTime : time X T (m + 1) ω = T :=
    time_eq_horizon_of_le_of_eq X T ω
      (Nat.succ_le_succ hnm) hnext
  change 1 ≤ |sample X T (m + 1) ω - sample X T m ω| at hm
  unfold sample at hm
  rw [hmTime, hmSuccTime, sub_self, abs_zero] at hm
  norm_num at hm

theorem integrable_sample
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [ℱ.IsRightContinuous] [SigmaFiniteFiltration μ ℱ]
    {X : Process Ω} (hX : Martingale X ℱ μ)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (T : ℝ≥0) (n : ℕ) :
    Integrable (sample X T n) μ := by
  exact Martingale.integrable_sample_of_boundedStoppingTime hX
    (time_isStoppingTime hX.stronglyAdapted hXRight T n)
    (time_le X T n) hXRight

theorem integrable_increment
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [ℱ.IsRightContinuous] [SigmaFiniteFiltration μ ℱ]
    {X : Process Ω} (hX : Martingale X ℱ μ)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (T : ℝ≥0) (n : ℕ) :
    Integrable (increment X T n) μ :=
  (integrable_sample hX hXRight T (n + 1)).sub
    (integrable_sample hX hXRight T n)

/-- Consecutive excursion samples satisfy optional sampling. -/
theorem condExp_sample_succ_ae_eq_sample
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [ℱ.IsRightContinuous] [SigmaFiniteFiltration μ ℱ]
    {X : Process Ω} (hX : Martingale X ℱ μ)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (T : ℝ≥0) (n : ℕ) :
    μ[sample X T (n + 1) |
        (time_isStoppingTime hX.stronglyAdapted hXRight T n).measurableSpace] =ᵐ[μ]
      sample X T n := by
  exact Martingale.condExp_sampled_ae_eq_of_boundedStoppingTimes hX
    (time_isStoppingTime hX.stronglyAdapted hXRight T n)
    (time_isStoppingTime hX.stronglyAdapted hXRight T (n + 1))
    (time_mono X T n) (time_le X T (n + 1)) hXRight

/-- Every martingale excursion increment has expectation zero. -/
theorem integral_increment_eq_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [ℱ.IsRightContinuous] [SigmaFiniteFiltration μ ℱ]
    {X : Process Ω} (hX : Martingale X ℱ μ)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (T : ℝ≥0) (n : ℕ) :
    (∫ ω, increment X T n ω ∂μ) = 0 := by
  let hτ := time_isStoppingTime hX.stronglyAdapted hXRight T n
  have hnextInt := integrable_sample hX hXRight T (n + 1)
  have hcurrentInt := integrable_sample hX hXRight T n
  have hmeans :
      (∫ ω, sample X T (n + 1) ω ∂μ) =
        ∫ ω, sample X T n ω ∂μ := by
    calc
      (∫ ω, sample X T (n + 1) ω ∂μ) =
          ∫ ω, μ[sample X T (n + 1) | hτ.measurableSpace] ω ∂μ :=
        (integral_condExp hτ.measurableSpace_le).symm
      _ = ∫ ω, sample X T n ω ∂μ :=
        integral_congr_ae
          (condExp_sample_succ_ae_eq_sample hX hXRight T n)
  unfold increment
  rw [integral_sub hnextInt hcurrentInt, hmeans, sub_self]

/-- A displacement-jump `L²` envelope gives `L²` membership of every
excursion increment. -/
theorem increment_memLp_two
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [ℱ.IsRightContinuous]
    {X : Process Ω} (hXAdapted : StronglyAdapted ℱ X)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (hXLeft : ProcessHasLeftLimits X)
    (T : ℝ≥0) (J : ℕ → Ω → ℝ)
    (hJ : ∀ n ω, 0 ≤ J n ω)
    (hJMem : ∀ n, MemLp (J n) (2 : ℝ≥0∞) μ)
    (hJump : ∀ n, ∀ᵐ ω ∂μ, ∀ t,
      |processLeftJump (displacementAfter X (time X T n)) t ω| ≤ J n ω)
    (n : ℕ) :
    MemLp (increment X T n) (2 : ℝ≥0∞) μ := by
  have hdom : MemLp (fun ω => (1 : ℝ) + J n ω) (2 : ℝ≥0∞) μ :=
    (memLp_const (μ := μ) (p := (2 : ℝ≥0∞)) (1 : ℝ)).add (hJMem n)
  apply hdom.of_le
  · exact (stronglyMeasurable_increment hXAdapted hXRight T n).aestronglyMeasurable
  · filter_upwards [hJump n] with ω hJumpω
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg zero_le_one (hJ n ω))]
    exact abs_time_succ_sub_time_le_at X hXLeft T J n ω
      (hJ n ω) hJumpω

/-- Quantitative `L²` norm bound for one excursion increment. -/
theorem eLpNorm_increment_le_one_add
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [ℱ.IsRightContinuous]
    {X : Process Ω} (hXAdapted : StronglyAdapted ℱ X)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (hXLeft : ProcessHasLeftLimits X)
    (T : ℝ≥0) (J : ℕ → Ω → ℝ)
    (hJ : ∀ n ω, 0 ≤ J n ω)
    (hJMem : ∀ n, MemLp (J n) (2 : ℝ≥0∞) μ)
    (hJump : ∀ n, ∀ᵐ ω ∂μ, ∀ t,
      |processLeftJump (displacementAfter X (time X T n)) t ω| ≤ J n ω)
    (n : ℕ) :
    eLpNorm (increment X T n) (2 : ℝ≥0∞) μ ≤
      1 + eLpNorm (J n) (2 : ℝ≥0∞) μ := by
  have hincMeas : AEStronglyMeasurable (increment X T n) μ :=
    (stronglyMeasurable_increment hXAdapted hXRight T n).aestronglyMeasurable
  have hdomMeas : AEStronglyMeasurable
      (fun ω => (1 : ℝ) + J n ω) μ :=
    aestronglyMeasurable_const.add (hJMem n).aestronglyMeasurable
  calc
    eLpNorm (increment X T n) (2 : ℝ≥0∞) μ ≤
        eLpNorm (fun ω => (1 : ℝ) + J n ω) (2 : ℝ≥0∞) μ := by
      apply eLpNorm_mono_ae hincMeas
      filter_upwards [hJump n] with ω hJumpω
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (add_nonneg zero_le_one (hJ n ω))]
      exact abs_time_succ_sub_time_le_at X hXLeft T J n ω
        (hJ n ω) hJumpω
    _ ≤ eLpNorm (fun _ : Ω => (1 : ℝ)) (2 : ℝ≥0∞) μ +
        eLpNorm (J n) (2 : ℝ≥0∞) μ :=
      eLpNorm_add_le (by norm_num)
    _ = 1 + eLpNorm (J n) (2 : ℝ≥0∞) μ := by
      congr 1
      rw [eLpNorm_const (1 : ℝ) (by norm_num) (NeZero.ne μ)]
      simp

/-- If the jump-envelope norm is at most one, the second moment of an
excursion increment is at most four. -/
theorem integral_norm_increment_sq_le_four
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [ℱ.IsRightContinuous]
    {X : Process Ω} (hXAdapted : StronglyAdapted ℱ X)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (hXLeft : ProcessHasLeftLimits X)
    (T : ℝ≥0) (J : ℕ → Ω → ℝ)
    (hJ : ∀ n ω, 0 ≤ J n ω)
    (hJMem : ∀ n, MemLp (J n) (2 : ℝ≥0∞) μ)
    (hJump : ∀ n, ∀ᵐ ω ∂μ, ∀ t,
      |processLeftJump (displacementAfter X (time X T n)) t ω| ≤ J n ω)
    (n : ℕ)
    (hJNorm : eLpNorm (J n) (2 : ℝ≥0∞) μ ≤ 1) :
    (∫ ω, ‖increment X T n ω‖ ^ 2 ∂μ) ≤ 4 := by
  have hmem := increment_memLp_two hXAdapted hXRight hXLeft
    T J hJ hJMem hJump n
  have hnorm : eLpNorm (increment X T n) (2 : ℝ≥0∞) μ ≤ 2 := by
    calc
      eLpNorm (increment X T n) (2 : ℝ≥0∞) μ ≤
          1 + eLpNorm (J n) (2 : ℝ≥0∞) μ :=
        eLpNorm_increment_le_one_add hXAdapted hXRight hXLeft
          T J hJ hJMem hJump n
      _ ≤ 1 + 1 := add_le_add le_rfl hJNorm
      _ = 2 := by norm_num
  have hnormReal :
      (eLpNorm (increment X T n) (2 : ℝ≥0∞) μ).toReal ≤ 2 := by
    exact (ENNReal.toReal_le_toReal (hmem.eLpNorm_ne_top)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).2 hnorm
  rw [eLpNorm_two_toReal_eq_sqrt_integral_norm_sq hmem] at hnormReal
  have hnonneg : 0 ≤ ∫ ω, ‖increment X T n ω‖ ^ 2 ∂μ :=
    integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun ω => sq_nonneg _)
  nlinarith [Real.sq_sqrt hnonneg,
    Real.sqrt_nonneg (∫ ω, ‖increment X T n ω‖ ^ 2 ∂μ)]

/-- A completed martingale excursion has a negative tail of fixed mass.  This
is the stochastic consumer of the pure negative-excursion estimate. -/
theorem probReal_increment_le_neg_sq_gt
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
    (n : ℕ)
    (hJNorm : eLpNorm (J n) (2 : ℝ≥0∞) μ ≤ 1)
    {α : ℝ} (hα : 0 < α) (hαOne : α ≤ 1)
    (hMass : 6 * α < μ.real {ω | 1 ≤ |increment X T n ω|}) :
    α ^ 2 < μ.real {ω | increment X T n ω ≤ -α} := by
  have hSecond :
      (∫ ω, ‖increment X T n ω‖ ^ (2 : ℝ) ∂μ) ≤ 4 := by
    simpa only [Real.rpow_two] using
      integral_norm_increment_sq_le_four hX.stronglyAdapted hXRight
        hXLeft T J hJ hJMem hJump n hJNorm
  exact probReal_negExcursion_sq_lt_of_abs_ge
    (stronglyMeasurable_increment hX.stronglyAdapted hXRight T n)
    (integrable_increment hX hXRight T n)
    (increment_memLp_two hX.stronglyAdapted hXRight hXLeft
      T J hJ hJMem hJump n)
    hSecond
    (integral_increment_eq_zero hX hXRight T n)
    hα hαOne hMass

end Lemma47ExcursionStopping

end FTAPTheorem42
