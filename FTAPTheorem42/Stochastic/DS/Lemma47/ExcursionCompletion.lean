/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.DS.Lemma47.ExcursionMartingale
import FTAPTheorem42.Stochastic.Martingale.Basic.MartingaleAbsoluteEnvelope
import FTAPTheorem42.Foundations.ProcessEnvelope
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov

/-!
# Completion probabilities for the Lemma 4.7 excursion clock

Each interval of the chronological excursion clock is the difference of two
stopped martingales.  Continuous-time Doob envelopes for these interval
martingales control the original martingale on the event where the prescribed
number of excursions has not been completed.  A finite `L²` sum estimate then
turns a high maximal event into a uniform lower bound for all earlier
completion events, without any independence assumption.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal MeasureTheory NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace Lemma47ExcursionStopping

/-- Martingale accumulated during the `n`-th clamped excursion interval. -/
noncomputable def excursionProcess
    (X : Process Ω) (T : ℝ≥0) (n : ℕ) : Process Ω :=
  fun t ω =>
    MeasureTheory.stoppedProcess X
        (fun ω => (time X T (n + 1) ω : WithTop ℝ≥0)) t ω -
      MeasureTheory.stoppedProcess X
        (fun ω => (time X T n ω : WithTop ℝ≥0)) t ω

/-- The excursion-interval process is a true martingale. -/
theorem excursionProcess_isMartingale
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [ℱ.IsRightContinuous] [SigmaFiniteFiltration μ ℱ]
    {X : Process Ω} (hX : Martingale X ℱ μ)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (T : ℝ≥0) (n : ℕ) :
    Martingale (excursionProcess X T n) ℱ μ := by
  exact (RightContinuousStoppedMartingale.Martingale.stoppedProcess_of_rightContinuous
    hX (time_isStoppingTime hX.stronglyAdapted hXRight T (n + 1))
      hXRight).sub
    (RightContinuousStoppedMartingale.Martingale.stoppedProcess_of_rightContinuous
      hX (time_isStoppingTime hX.stronglyAdapted hXRight T n) hXRight)

omit [MeasurableSpace Ω] in
/-- Excursion-interval processes inherit right-continuous paths. -/
theorem excursionProcess_rightContinuous
    (X : Process Ω)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (T : ℝ≥0) (n : ℕ) :
    ∀ ω t, ContinuousWithinAt
      (excursionProcess X T n · ω) (Set.Ici t) t := by
  intro ω t
  exact (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
    X hXRight ω t).sub
    (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
      X hXRight ω t)

omit [MeasurableSpace Ω] in
/-- At the common deterministic horizon, an interval process equals the
corresponding sampled excursion increment. -/
theorem excursionProcess_terminal
    (X : Process Ω) (T : ℝ≥0) (n : ℕ) :
    excursionProcess X T n T = increment X T n := by
  funext ω
  unfold excursionProcess increment sample
  rw [MeasureTheory.stoppedProcess_eq_of_ge,
    MeasureTheory.stoppedProcess_eq_of_ge]
  · simp only [WithTop.untopA_eq_untop WithTop.coe_ne_top,
      WithTop.untop_coe]
  · exact WithTop.coe_le_coe.mpr (time_le X T n ω)
  · exact WithTop.coe_le_coe.mpr (time_le X T (n + 1) ω)

omit [MeasurableSpace Ω] in
/-- The sum of the first `k` interval processes telescopes to the stopped
martingale between the initial clock value and the `k`-th clock value. -/
theorem sum_excursionProcess
    (X : Process Ω) (T : ℝ≥0) (k : ℕ) (t : ℝ≥0) (ω : Ω) :
    (∑ i ∈ Finset.range k, excursionProcess X T i t ω) =
      MeasureTheory.stoppedProcess X
          (fun ω => (time X T k ω : WithTop ℝ≥0)) t ω -
        MeasureTheory.stoppedProcess X
          (fun ω => (time X T 0 ω : WithTop ℝ≥0)) t ω := by
  simpa only [excursionProcess] using
    Finset.sum_range_sub (fun i => MeasureTheory.stoppedProcess X
      (fun ω => (time X T i ω : WithTop ℝ≥0)) t ω) k

/-- Doob envelope of one stopped excursion-interval martingale. -/
noncomputable def excursionEnvelope
    (X : Process Ω) (T : ℝ≥0) (n : ℕ) : Ω → ℝ :=
  FactorialChronologicalGrid.martingaleAbsoluteEnvelope
    (excursionProcess X T n) T

/-- Sum of the Doob envelopes for the first `k` excursion intervals. -/
noncomputable def totalExcursionEnvelope
    (X : Process Ω) (T : ℝ≥0) (k : ℕ) : Ω → ℝ :=
  fun ω => ∑ i ∈ Finset.range k, excursionEnvelope X T i ω

theorem excursionEnvelope_memLp_two
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
    (n : ℕ) :
    MemLp (excursionEnvelope X T n) (2 : ℝ≥0∞) μ := by
  apply FactorialChronologicalGrid.Martingale.martingaleAbsoluteEnvelope_memLp
    (excursionProcess_isMartingale hX hXRight T n) T
  rw [excursionProcess_terminal]
  exact increment_memLp_two hX.stronglyAdapted hXRight hXLeft
    T J hJ hJMem hJump n

/-- The `L²` norm of one interval envelope is at most four when the
displacement-jump envelope has norm at most one. -/
theorem eLpNorm_excursionEnvelope_le_four
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
    (n : ℕ) :
    eLpNorm (excursionEnvelope X T n) (2 : ℝ≥0∞) μ ≤ 4 := by
  have hterminal :
      MemLp (excursionProcess X T n T) (2 : ℝ≥0∞) μ := by
    rw [excursionProcess_terminal]
    exact increment_memLp_two hX.stronglyAdapted hXRight hXLeft
      T J hJ hJMem hJump n
  calc
    eLpNorm (excursionEnvelope X T n) (2 : ℝ≥0∞) μ ≤
        2 * eLpNorm (excursionProcess X T n T) (2 : ℝ≥0∞) μ :=
      FactorialChronologicalGrid.Martingale.eLpNorm_martingaleAbsoluteEnvelope_le_two_mul
        (excursionProcess_isMartingale hX hXRight T n) T hterminal
    _ = 2 * eLpNorm (increment X T n) (2 : ℝ≥0∞) μ := by
      rw [excursionProcess_terminal]
    _ ≤ 2 * (1 + eLpNorm (J n) (2 : ℝ≥0∞) μ) := by
      gcongr
      exact eLpNorm_increment_le_one_add hX.stronglyAdapted hXRight
        hXLeft T J hJ hJMem hJump n
    _ ≤ 2 * (1 + 1) := by
      gcongr
      exact hJNorm n
    _ = 4 := by norm_num

theorem totalExcursionEnvelope_memLp_two
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
    MemLp (totalExcursionEnvelope X T k) (2 : ℝ≥0∞) μ := by
  have htotal : totalExcursionEnvelope X T k =
      ∑ n ∈ Finset.range k, excursionEnvelope X T n := by
    funext ω
    simp only [totalExcursionEnvelope, Finset.sum_apply]
  rw [htotal]
  exact memLp_finsetSum' (s := Finset.range k) (fun n _ =>
    excursionEnvelope_memLp_two hX hXRight hXLeft
      T J hJ hJMem hJump n)

/-- Finite aggregation costs only the sum of the interval-envelope norms;
no independence assumption is used. -/
theorem eLpNorm_totalExcursionEnvelope_le
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
    eLpNorm (totalExcursionEnvelope X T k) (2 : ℝ≥0∞) μ ≤
      4 * k := by
  have htotal : totalExcursionEnvelope X T k =
      ∑ i ∈ Finset.range k, excursionEnvelope X T i := by
    funext ω
    simp only [totalExcursionEnvelope, Finset.sum_apply]
  rw [htotal]
  calc
    eLpNorm (∑ i ∈ Finset.range k, excursionEnvelope X T i)
        (2 : ℝ≥0∞) μ ≤
        ∑ i ∈ Finset.range k,
          eLpNorm (excursionEnvelope X T i) (2 : ℝ≥0∞) μ := by
      exact eLpNorm_sum_le (by norm_num)
    _ ≤ ∑ _i ∈ Finset.range k, (4 : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro i _
      exact eLpNorm_excursionEnvelope_le_four hX hXRight hXLeft
        T J hJ hJMem hJump hJNorm i
    _ = 4 * k := by simp [mul_comm]

omit [MeasurableSpace Ω] in
theorem excursionEnvelope_nonnegative
    (X : Process Ω) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    0 ≤ excursionEnvelope X T n ω :=
  Real.sqrt_nonneg _

omit [MeasurableSpace Ω] in
theorem totalExcursionEnvelope_nonnegative
    (X : Process Ω) (T : ℝ≥0) (k : ℕ) (ω : Ω) :
    0 ≤ totalExcursionEnvelope X T k ω := by
  exact Finset.sum_nonneg fun i _ => excursionEnvelope_nonnegative X T i ω

/-- Chebyshev bound for the finite sum of excursion-interval Doob envelopes.
The quadratic dependence on `k` is the one used in the original Lemma 4.7
argument. -/
theorem measure_totalExcursionEnvelope_gt_le
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
    (k : ℕ) {R : ℝ} (hR : 0 < R) :
    μ {ω | R < totalExcursionEnvelope X T k ω} ≤
      (ENNReal.ofReal R)⁻¹ ^ 2 * (4 * (k : ℝ≥0∞)) ^ 2 := by
  have hmem := totalExcursionEnvelope_memLp_two hX hXRight hXLeft
    T J hJ hJMem hJump k
  have hsubset :
      {ω | R < totalExcursionEnvelope X T k ω} ⊆
        {ω | ENNReal.ofReal R ≤
          ‖totalExcursionEnvelope X T k ω‖ₑ} := by
    intro ω hω
    change R < totalExcursionEnvelope X T k ω at hω
    change ENNReal.ofReal R ≤
      ‖totalExcursionEnvelope X T k ω‖ₑ
    rw [Real.enorm_eq_ofReal
      (totalExcursionEnvelope_nonnegative X T k ω)]
    exact ENNReal.ofReal_le_ofReal hω.le
  calc
    μ {ω | R < totalExcursionEnvelope X T k ω} ≤
        μ {ω | ENNReal.ofReal R ≤
          ‖totalExcursionEnvelope X T k ω‖ₑ} :=
      measure_mono hsubset
    _ ≤ (ENNReal.ofReal R)⁻¹ ^ (2 : ℝ≥0∞).toReal *
        eLpNorm (totalExcursionEnvelope X T k)
          (2 : ℝ≥0∞) μ ^ (2 : ℝ≥0∞).toReal := by
      apply meas_ge_le_mul_pow_eLpNorm_enorm μ
        (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
      · exact ENNReal.ofReal_ne_zero_iff.mpr hR
      · simp
    _ ≤ (ENNReal.ofReal R)⁻¹ ^ (2 : ℝ) *
        (4 * (k : ℝ≥0∞)) ^ (2 : ℝ) := by
      norm_num
      gcongr
      exact eLpNorm_totalExcursionEnvelope_le hX hXRight hXLeft
        T J hJ hJMem hJump hJNorm k
    _ = (ENNReal.ofReal R)⁻¹ ^ 2 *
        (4 * (k : ℝ≥0∞)) ^ 2 := by
      rw [ENNReal.rpow_two, ENNReal.rpow_two]

/-- Real-probability form of the preceding Chebyshev estimate. -/
theorem probReal_totalExcursionEnvelope_gt_le
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
    (k : ℕ) {R : ℝ} (hR : 0 < R) :
    μ.real {ω | R < totalExcursionEnvelope X T k ω} ≤
      (4 * (k : ℝ) / R) ^ 2 := by
  have hmeasure := measure_totalExcursionEnvelope_gt_le hX hXRight hXLeft
    T J hJ hJMem hJump hJNorm k hR
  have hfinite :
      (ENNReal.ofReal R)⁻¹ ^ 2 * (4 * (k : ℝ≥0∞)) ^ 2 ≠ ∞ := by
    finiteness
  have hreal := ENNReal.toReal_mono hfinite hmeasure
  change (μ {ω | R < totalExcursionEnvelope X T k ω}).toReal ≤ _
  calc
    (μ {ω | R < totalExcursionEnvelope X T k ω}).toReal ≤
        R⁻¹ ^ 2 * (4 * (k : ℝ)) ^ 2 := by
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_inv, ENNReal.toReal_ofReal hR.le,
        ENNReal.toReal_ofNat, ENNReal.toReal_natCast] using hreal
    _ = (4 * (k : ℝ) / R) ^ 2 := by
      rw [div_eq_mul_inv]
      ring

/-- On the event where the `k`-th clock time has reached the horizon, the
first `k` interval martingales reconstruct the original martingale.  Their
Doob envelopes therefore dominate its finite-horizon envelope. -/
theorem finiteHorizonAbsoluteEnvelope_le_totalExcursionEnvelope_ae
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [ℱ.IsRightContinuous] [SigmaFiniteFiltration μ ℱ]
    {X : Process Ω} (hX : Martingale X ℱ μ)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (hXLeft : ProcessHasLeftLimits X)
    (hXZero : X 0 =ᵐ[μ] 0)
    (T : ℝ≥0) (J : ℕ → Ω → ℝ)
    (hJ : ∀ n ω, 0 ≤ J n ω)
    (hJMem : ∀ n, MemLp (J n) (2 : ℝ≥0∞) μ)
    (hJump : ∀ n, ∀ᵐ ω ∂μ, ∀ t,
      |processLeftJump (displacementAfter X (time X T n)) t ω| ≤ J n ω)
    {k : ℕ} (hk : 0 < k) :
    ∀ᵐ ω ∂μ, ω ∉ completedEvent X T (k - 1) →
      FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope X T ω ≤
        totalExcursionEnvelope X T k ω := by
  have hIntervalDom : ∀ᵐ ω ∂μ, ∀ i t, t ≤ T →
      ‖excursionProcess X T i t ω‖ ≤ excursionEnvelope X T i ω := by
    apply ae_all_iff.2
    intro i
    have hterminal :
        MemLp (excursionProcess X T i T) (2 : ℝ≥0∞) μ := by
      rw [excursionProcess_terminal]
      exact increment_memLp_two hX.stronglyAdapted hXRight hXLeft
        T J hJ hJMem hJump i
    exact FactorialChronologicalGrid.Martingale.norm_le_martingaleAbsoluteEnvelope_ae
      (excursionProcess_isMartingale hX hXRight T i) T hterminal
      (excursionProcess_rightContinuous X hXRight T i)
  filter_upwards [hIntervalDom, hXZero] with ω hdom hzero
  intro hnotCompleted
  have hsmall : |increment X T (k - 1) ω| < 1 := by
    exact lt_of_not_ge hnotCompleted
  have hclock : time X T k ω = T := by
    have hreach := time_succ_eq_horizon_of_abs_sub_lt_one
      X hXRight T (k - 1) ω hsmall
    simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hk.ne')] using hreach
  apply FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope_le_of_bound
  intro t ht
  have hsum := sum_excursionProcess X T k t ω
  have hstopK : MeasureTheory.stoppedProcess X
      (fun ω => (time X T k ω : WithTop ℝ≥0)) t ω = X t ω := by
    rw [MeasureTheory.stoppedProcess_eq_of_le]
    rw [hclock]
    exact WithTop.coe_le_coe.mpr ht
  have hstopZero : MeasureTheory.stoppedProcess X
      (fun ω => (time X T 0 ω : WithTop ℝ≥0)) t ω = X 0 ω := by
    rw [MeasureTheory.stoppedProcess_eq_of_ge]
    · simp only [time_zero, WithTop.untopA_eq_untop
        WithTop.coe_ne_top, WithTop.untop_coe]
    · simp only [time_zero]
      exact bot_le
  have hzero' : X 0 ω = 0 := by simpa only [Pi.zero_apply] using hzero
  rw [hstopK, hstopZero, hzero', sub_zero] at hsum
  calc
    |X t ω| = |∑ i ∈ Finset.range k, excursionProcess X T i t ω| := by
      rw [hsum]
    _ ≤ ∑ i ∈ Finset.range k, |excursionProcess X T i t ω| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range k, excursionEnvelope X T i ω := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Real.norm_eq_abs] using hdom i t ht
    _ = totalExcursionEnvelope X T k ω := by
      simp only [totalExcursionEnvelope]

/-- A high finite-horizon martingale maximum forces every one of the first
`k` chronological unit excursions to be completed with probability greater
than `6 * α`, provided the aggregated Doob-envelope error is at most `α`.
This is the completion-probability step in Delbaen--Schachermayer Lemma 4.7. -/
theorem probReal_completedEvent_gt_six_mul
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [ℱ.IsRightContinuous] [SigmaFiniteFiltration μ ℱ]
    {X : Process Ω} (hX : Martingale X ℱ μ)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (hXLeft : ProcessHasLeftLimits X)
    (hXZero : X 0 =ᵐ[μ] 0)
    (T : ℝ≥0) (J : ℕ → Ω → ℝ)
    (hJ : ∀ n ω, 0 ≤ J n ω)
    (hJMem : ∀ n, MemLp (J n) (2 : ℝ≥0∞) μ)
    (hJump : ∀ n, ∀ᵐ ω ∂μ, ∀ t,
      |processLeftJump (displacementAfter X (time X T n)) t ω| ≤ J n ω)
    (hJNorm : ∀ n, eLpNorm (J n) (2 : ℝ≥0∞) μ ≤ 1)
    {k : ℕ} (hk : 0 < k) {R α : ℝ} (hR : 0 < R)
    (hHigh : 7 * α < μ.real {ω |
      R < FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope X T ω})
    (hError : (4 * (k : ℝ) / R) ^ 2 ≤ α)
    {i : ℕ} (hi : i < k) :
    6 * α < μ.real (completedEvent X T i) := by
  let C : Set Ω := completedEvent X T (k - 1)
  let E : Set Ω := {ω | R < totalExcursionEnvelope X T k ω}
  let H : Set Ω := {ω |
    R < FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope X T ω}
  have hEnvelope :=
    finiteHorizonAbsoluteEnvelope_le_totalExcursionEnvelope_ae
      hX hXRight hXLeft hXZero T J hJ hJMem hJump hk
  have hsubset : H ≤ᵐ[μ] Set.union C E := by
    filter_upwards [hEnvelope] with ω hω
    intro hωH
    by_cases hωC : ω ∈ C
    · exact Set.mem_union_left E hωC
    · apply Set.mem_union_right C
      change R < totalExcursionEnvelope X T k ω
      exact (show R <
          FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope X T ω
        from hωH).trans_le (hω hωC)
  have hHighLeUnion : μ.real H ≤ μ.real (Set.union C E) := by
    exact ENNReal.toReal_mono (by finiteness) (measure_mono_ae hsubset)
  have hUnionLe : μ.real H ≤ μ.real C + μ.real E :=
    hHighLeUnion.trans (measureReal_union_le C E)
  have hTail : μ.real E ≤ α := by
    exact (probReal_totalExcursionEnvelope_gt_le hX hXRight hXLeft
      T J hJ hJMem hJump hJNorm k hR).trans hError
  have hLast : 6 * α < μ.real C := by
    dsimp only [H] at hHigh hUnionLe
    linarith
  have hiLast : i ≤ k - 1 := Nat.le_sub_one_of_lt hi
  exact hLast.trans_le (measureReal_mono
    (completedEvent_antitone X hXRight T hiLast))

end Lemma47ExcursionStopping

end FTAPTheorem42
