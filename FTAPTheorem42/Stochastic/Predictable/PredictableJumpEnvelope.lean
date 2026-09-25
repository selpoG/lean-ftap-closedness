/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Martingale.Basic.ContinuousDoobEnvelope

/-!
# Countable graph control of predictable jumps

This module isolates the passage from a countable enumeration of the jumps
of a predictable finite-variation process to the continuous-time Doob
envelope.  The graph enumeration and the conditional-expectation estimate on
each graph remain explicit inputs; the conclusions are the all-time jump
bound and its `L²` estimate.
-/

namespace FTAPTheorem42

open MeasureTheory Set
open scoped ENNReal MeasureTheory NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The squared envelope of left jumps sampled on countably many graphs. -/
noncomputable def countableLeftJumpSqEnvelope
    (A : Process Ω) (τ : ℕ → Ω → ℝ≥0) : Ω → ℝ≥0∞ :=
  fun ω => ⨆ n, ENNReal.ofReal ((processLeftJump A (τ n ω) ω) ^ 2)

/-- Measurability of every sampled jump makes the countable squared envelope
measurable. -/
theorem measurable_countableLeftJumpSqEnvelope
    (A : Process Ω) (τ : ℕ → Ω → ℝ≥0)
    (hjump : ∀ n, Measurable fun ω => processLeftJump A (τ n ω) ω) :
    Measurable (countableLeftJumpSqEnvelope A τ) := by
  apply Measurable.iSup
  intro n
  exact ((hjump n).pow_const 2).ennreal_ofReal

/-- A countable family covers the left jumps of `A` up to `T` when every
nonzero left jump before `T` agrees with one of the sampled jumps. -/
def CoversLeftJumpsUpTo
    (A : Process Ω) (T : ℝ≥0) (τ : ℕ → Ω → ℝ≥0) : Prop :=
  ∀ ω t, t ≤ T → processLeftJump A t ω ≠ 0 → ∃ n,
    processLeftJump A t ω = processLeftJump A (τ n ω) ω

omit [MeasurableSpace Ω] in
/-- Coverage transfers the countable envelope bound to every left jump before
the deterministic horizon. -/
theorem ofReal_sq_processLeftJump_le_countableLeftJumpSqEnvelope
    (A : Process Ω) (T : ℝ≥0) (τ : ℕ → Ω → ℝ≥0)
    (hcover : CoversLeftJumpsUpTo A T τ)
    (ω : Ω) {t : ℝ≥0} (ht : t ≤ T) :
    ENNReal.ofReal ((processLeftJump A t ω) ^ 2) ≤
      countableLeftJumpSqEnvelope A τ ω := by
  by_cases hjump : processLeftJump A t ω = 0
  · simp [hjump]
  · obtain ⟨n, hn⟩ := hcover ω t ht hjump
    rw [hn]
    exact le_iSup (fun k =>
      ENNReal.ofReal ((processLeftJump A (τ k ω) ω) ^ 2)) n

end FTAPTheorem42

namespace FTAPTheorem42

/-!
## Real-valued predictable-jump envelopes

The graphwise Corollary 2.4 estimates are expressed through an `ℝ≥0∞`-valued
squared envelope.  This section takes its square root, proves `L²` membership,
and transfers graph coverage to one simultaneous bound for all left jumps.
-/

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The real square-root envelope of left jumps sampled on countably many
graphs. -/
noncomputable def countableLeftJumpEnvelope
    (A : Process Ω) (τ : ℕ → Ω → ℝ≥0) : Ω → ℝ :=
  fun ω => Real.sqrt (countableLeftJumpSqEnvelope A τ ω).toReal

theorem measurable_countableLeftJumpEnvelope
    (A : Process Ω) (τ : ℕ → Ω → ℝ≥0)
    (hjump : ∀ n, Measurable fun ω =>
      processLeftJump A (τ n ω) ω) :
    Measurable (countableLeftJumpEnvelope A τ) := by
  exact (measurable_countableLeftJumpSqEnvelope A τ hjump).ennreal_toReal.sqrt

omit [MeasurableSpace Ω] in
theorem countableLeftJumpEnvelope_nonnegative
    (A : Process Ω) (τ : ℕ → Ω → ℝ≥0) :
    0 ≤ countableLeftJumpEnvelope A τ :=
  fun _ => Real.sqrt_nonneg _

omit [MeasurableSpace Ω] in
theorem sq_countableLeftJumpEnvelope
    (A : Process Ω) (τ : ℕ → Ω → ℝ≥0) (ω : Ω) :
    (countableLeftJumpEnvelope A τ ω) ^ 2 =
      (countableLeftJumpSqEnvelope A τ ω).toReal := by
  exact Real.sq_sqrt ENNReal.toReal_nonneg

/-- A finite integral of the squared graph envelope makes its real square
root an `L²` random variable. -/
theorem countableLeftJumpEnvelope_memLp
    {μ : Measure Ω}
    (A : Process Ω) (τ : ℕ → Ω → ℝ≥0)
    (hsampledMeas : ∀ n, Measurable fun ω =>
      processLeftJump A (τ n ω) ω)
    (hfinite : (∫⁻ ω, countableLeftJumpSqEnvelope A τ ω ∂μ) ≠ ∞) :
    MemLp (countableLeftJumpEnvelope A τ) (2 : ℝ≥0∞) μ := by
  have hSqMeas : Measurable (countableLeftJumpSqEnvelope A τ) :=
    measurable_countableLeftJumpSqEnvelope A τ hsampledMeas
  have hToRealIntegrable : Integrable
      (fun ω => (countableLeftJumpSqEnvelope A τ ω).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hSqMeas.aemeasurable hfinite
  have hEnvelopeMeas :=
    measurable_countableLeftJumpEnvelope A τ hsampledMeas
  apply (memLp_two_iff_integrable_sq
    hEnvelopeMeas.aestronglyMeasurable).2
  convert hToRealIntegrable using 1
  funext ω
  exact sq_countableLeftJumpEnvelope A τ ω

/-- A squared-integral estimate with the Doob constant `4` gives the
corresponding `L²` estimate with constant `2` for the real jump envelope. -/
theorem eLpNorm_countableLeftJumpEnvelope_le_two_mul
    {μ : Measure Ω}
    (A : Process Ω) (τ : ℕ → Ω → ℝ≥0) (J : Ω → ℝ)
    (hEnvelope : MemLp (countableLeftJumpEnvelope A τ)
      (2 : ℝ≥0∞) μ)
    (hJ : MemLp J (2 : ℝ≥0∞) μ)
    (hSqBound :
      (∫⁻ ω, countableLeftJumpSqEnvelope A τ ω ∂μ) ≤
        4 * ∫⁻ ω, ENNReal.ofReal ((J ω) ^ 2) ∂μ) :
    eLpNorm (countableLeftJumpEnvelope A τ) (2 : ℝ≥0∞) μ ≤
      2 * eLpNorm J (2 : ℝ≥0∞) μ := by
  let E := countableLeftJumpEnvelope A τ
  have hEsqInt : Integrable (fun ω => (E ω) ^ 2) μ :=
    hEnvelope.integrable_sq
  have hJsqInt : Integrable (fun ω => (J ω) ^ 2) μ :=
    hJ.integrable_sq
  have hEsqNonneg : ∀ᵐ ω ∂μ, 0 ≤ (E ω) ^ 2 :=
    Filter.Eventually.of_forall fun ω => sq_nonneg (E ω)
  have hJsqNonneg : ∀ᵐ ω ∂μ, 0 ≤ (J ω) ^ 2 :=
    Filter.Eventually.of_forall fun ω => sq_nonneg (J ω)
  have hEnvelopeLIntegral :
      (∫⁻ ω, ENNReal.ofReal ((E ω) ^ 2) ∂μ) ≤
        ∫⁻ ω, countableLeftJumpSqEnvelope A τ ω ∂μ := by
    apply lintegral_mono
    intro ω
    change ENNReal.ofReal ((E ω) ^ 2) ≤
      countableLeftJumpSqEnvelope A τ ω
    rw [show (E ω) ^ 2 =
      (countableLeftJumpSqEnvelope A τ ω).toReal by
        exact sq_countableLeftJumpEnvelope A τ ω]
    exact ENNReal.ofReal_toReal_le
  have hSecond :
      (∫ ω, (E ω) ^ 2 ∂μ) ≤ 4 * ∫ ω, (J ω) ^ 2 ∂μ := by
    apply (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (by norm_num) (integral_nonneg_of_ae hJsqNonneg))).mp
    rw [ofReal_integral_eq_lintegral_ofReal hEsqInt hEsqNonneg,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
      ofReal_integral_eq_lintegral_ofReal hJsqInt hJsqNonneg]
    exact hEnvelopeLIntegral.trans (by
      simpa only [ENNReal.ofReal_ofNat] using hSqBound)
  apply (ENNReal.toReal_le_toReal hEnvelope.eLpNorm_ne_top
    (ENNReal.mul_ne_top (by norm_num) hJ.eLpNorm_ne_top)).mp
  rw [eLpNorm_two_toReal_eq_sqrt_integral_norm_sq hEnvelope,
    ENNReal.toReal_mul,
    eLpNorm_two_toReal_eq_sqrt_integral_norm_sq hJ]
  norm_num only [ENNReal.toReal_ofNat]
  have hEIntegralNonneg : 0 ≤ ∫ ω, ‖E ω‖ ^ 2 ∂μ :=
    integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun ω => sq_nonneg ‖E ω‖)
  have hJIntegralNonneg : 0 ≤ ∫ ω, ‖J ω‖ ^ 2 ∂μ :=
    integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun ω => sq_nonneg ‖J ω‖)
  have hSecondNorm :
      (∫ ω, ‖E ω‖ ^ 2 ∂μ) ≤ 4 * ∫ ω, ‖J ω‖ ^ 2 ∂μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using hSecond
  nlinarith [Real.sq_sqrt hEIntegralNonneg,
    Real.sq_sqrt hJIntegralNonneg,
    Real.sqrt_nonneg (∫ ω, ‖E ω‖ ^ 2 ∂μ),
    Real.sqrt_nonneg (∫ ω, ‖J ω‖ ^ 2 ∂μ)]

/-- Graph coverage transfers to a simultaneous real-valued left-jump bound
outside the null set on which the squared envelope is infinite. -/
theorem abs_processLeftJump_le_countableLeftJumpEnvelope_ae
    {μ : Measure Ω}
    (A : Process Ω) (T : ℝ≥0) (τ : ℕ → Ω → ℝ≥0)
    (hcover : CoversLeftJumpsUpTo A T τ)
    (hsampledMeas : ∀ n, Measurable fun ω =>
      processLeftJump A (τ n ω) ω)
    (hfinite : (∫⁻ ω, countableLeftJumpSqEnvelope A τ ω ∂μ) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ t, t ≤ T →
      |processLeftJump A t ω| ≤ countableLeftJumpEnvelope A τ ω := by
  have hSqMeas : Measurable (countableLeftJumpSqEnvelope A τ) :=
    measurable_countableLeftJumpSqEnvelope A τ hsampledMeas
  filter_upwards [ae_lt_top hSqMeas hfinite] with ω hω
  intro t ht
  apply Real.le_sqrt_of_sq_le
  have hENN := ofReal_sq_processLeftJump_le_countableLeftJumpSqEnvelope
    A T τ hcover ω ht
  have hReal :=
    (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hω.ne).2 hENN
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _), sq_abs] using hReal

end FTAPTheorem42
