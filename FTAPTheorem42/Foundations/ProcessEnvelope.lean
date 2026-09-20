/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.GridEnvelope
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov

/-!
# Finite-horizon envelopes of right-continuous processes

Factorial grids produce an envelope which is measurable at the deterministic
horizon and dominates every value, and hence every left jump, before that
horizon.  This provides the terminal random variable used in the sampled
conditional-expectation form of Corollary 2.4.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal MeasureTheory NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace FactorialChronologicalGrid

/-- Real square-root of the squared factorial-grid envelope of `|X|` up to
`T`. -/
noncomputable def finiteHorizonAbsoluteEnvelope
    (X : Process Ω) (T : ℝ≥0) : Ω → ℝ :=
  fun ω => Real.sqrt
    ((eFactorialRunningMaxSqEnvelope (fun t ω => |X t ω|) T ω).toReal)

/-- The finite-horizon envelope is measurable with respect to the terminal
sigma algebra. -/
theorem stronglyMeasurable_finiteHorizonAbsoluteEnvelope
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {X : Process Ω} (hX : StronglyAdapted ℱ X) (T : ℝ≥0) :
    StronglyMeasurable[ℱ T] (finiteHorizonAbsoluteEnvelope X T) := by
  let : MeasurableSpace Ω := ℱ T
  have hSq : Measurable
      (eFactorialRunningMaxSqEnvelope (fun t ω => |X t ω|) T) := by
    apply Measurable.iSup
    intro r
    apply Measurable.ennreal_ofReal
    apply Measurable.pow_const
    unfold factorialRunningMax
    apply measurable_finiteRunningMax
    intro k _
    have htime : (stoppedGrid T r).sampledTime k ≤ T := by
      simp only [ChronologicalGrid.sampledTime, stoppedGrid_time]
      exact min_le_right _ _
    exact (((hX ((stoppedGrid T r).sampledTime k)).mono
      (ℱ.mono htime)).norm).measurable
  exact hSq.ennreal_toReal.sqrt.stronglyMeasurable

omit [MeasurableSpace Ω] in
/-- A pathwise bound up to `T` bounds the squared factorial envelope. -/
theorem eFactorialRunningMaxSqEnvelope_abs_le_of_bound
    (X : Process Ω) (T : ℝ≥0) {G : ℝ} {ω : Ω}
    (hbound : ∀ t, t ≤ T → |X t ω| ≤ G) :
    eFactorialRunningMaxSqEnvelope (fun t ω => |X t ω|) T ω ≤
      ENNReal.ofReal (G ^ 2) := by
  have hG : 0 ≤ G :=
    (abs_nonneg (X 0 ω)).trans (hbound 0 bot_le)
  apply iSup_le
  intro r
  have hmax : factorialRunningMax (fun t ω => |X t ω|) T r ω ≤ G := by
    obtain ⟨k, hk, hkEq⟩ := Finset.exists_mem_eq_sup'
      (s := Finset.range (r * r.factorial + 1))
      Finset.nonempty_range_add_one
      (fun j => (stoppedGrid T r).natSample
        (fun t ω => |X t ω|) j ω)
    rw [show factorialRunningMax (fun t ω => |X t ω|) T r ω =
        (stoppedGrid T r).natSample (fun t ω => |X t ω|) k ω by
      exact hkEq]
    apply hbound
    simp only [ChronologicalGrid.sampledTime, stoppedGrid_time]
    exact min_le_right _ _
  exact ENNReal.ofReal_le_ofReal
    ((sq_le_sq₀
      (finiteRunningMax_nonneg _ _
        ((stoppedGrid T r).natSample_nonneg
          (fun _ _ => abs_nonneg _)) ω)
      hG).2 hmax)

omit [MeasurableSpace Ω] in
/-- A pathwise finite bound also bounds the real square-root envelope. -/
theorem finiteHorizonAbsoluteEnvelope_le_of_bound
    (X : Process Ω) (T : ℝ≥0) {G : ℝ} {ω : Ω}
    (hbound : ∀ t, t ≤ T → |X t ω| ≤ G) :
    finiteHorizonAbsoluteEnvelope X T ω ≤ G := by
  have hG : 0 ≤ G :=
    (abs_nonneg (X 0 ω)).trans (hbound 0 bot_le)
  have hENN := eFactorialRunningMaxSqEnvelope_abs_le_of_bound
    X T hbound
  have hleftFinite :
      eFactorialRunningMaxSqEnvelope (fun t ω => |X t ω|) T ω ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hENN
  have hreal := (ENNReal.toReal_le_toReal hleftFinite
    ENNReal.ofReal_ne_top).2 hENN
  calc
    finiteHorizonAbsoluteEnvelope X T ω ≤
        Real.sqrt ((ENNReal.ofReal (G ^ 2)).toReal) :=
      Real.sqrt_le_sqrt hreal
    _ = G := by
      rw [ENNReal.toReal_ofReal (sq_nonneg G), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hG]

/-- An `L²` envelope of the process supplies `L²` membership of the
terminally measurable finite-horizon envelope. -/
theorem finiteHorizonAbsoluteEnvelope_memLp_of_bound
    {μ : Measure Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {X : Process Ω} (hX : StronglyAdapted ℱ X) (T : ℝ≥0)
    {G : Ω → ℝ} (hG : MemLp G (2 : ℝ≥0∞) μ)
    (hbound : ∀ᵐ ω ∂μ, ∀ t, t ≤ T → |X t ω| ≤ G ω) :
    MemLp (finiteHorizonAbsoluteEnvelope X T) (2 : ℝ≥0∞) μ := by
  apply MemLp.of_le hG
    ((stronglyMeasurable_finiteHorizonAbsoluteEnvelope hX T).mono
      (ℱ.le T)).aestronglyMeasurable
  filter_upwards [hbound] with ω hboundω
  have hGnonneg : 0 ≤ G ω :=
    (abs_nonneg (X 0 ω)).trans (hboundω 0 bot_le)
  have hEnvelopeNonnegative :
      0 ≤ finiteHorizonAbsoluteEnvelope X T ω :=
    Real.sqrt_nonneg _
  rw [Real.norm_eq_abs,
    abs_of_nonneg hEnvelopeNonnegative,
    Real.norm_eq_abs, abs_of_nonneg hGnonneg]
  exact finiteHorizonAbsoluteEnvelope_le_of_bound X T hboundω

omit [MeasurableSpace Ω] in
/-- For a right-continuous path with a finite bound on `[0, T]`, the
factorial-grid envelope dominates every value on that interval. -/
theorem abs_le_finiteHorizonAbsoluteEnvelope_of_bound
    {X : Process Ω} (hRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (T : ℝ≥0) {G : ℝ}
    (hbound : ∀ t, t ≤ T → |X t ω| ≤ G) :
    ∀ t, t ≤ T → |X t ω| ≤ finiteHorizonAbsoluteEnvelope X T ω := by
  have hEnvelopeFinite :
      eFactorialRunningMaxSqEnvelope (fun t ω => |X t ω|) T ω ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (eFactorialRunningMaxSqEnvelope_abs_le_of_bound X T hbound)
  intro t ht
  apply Real.le_sqrt_of_sq_le
  have hENN := ofReal_sq_le_eFactorialRunningMaxSqEnvelope
    (fun t ω => |X t ω|) T (fun _ _ => abs_nonneg _)
    (fun ω t => (hRight ω t).abs) ω ht
  have hreal := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
    hEnvelopeFinite).2 hENN
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _), sq_abs] using hreal

/-- Outside one null set, the finite-horizon envelope dominates every
process value before `T`. -/
theorem abs_le_finiteHorizonAbsoluteEnvelope_ae
    {μ : Measure Ω}
    {X : Process Ω} (hRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (T : ℝ≥0) {G : Ω → ℝ}
    (hbound : ∀ᵐ ω ∂μ, ∀ t, t ≤ T → |X t ω| ≤ G ω) :
    ∀ᵐ ω ∂μ, ∀ t, t ≤ T →
      |X t ω| ≤ finiteHorizonAbsoluteEnvelope X T ω := by
  filter_upwards [hbound] with ω hboundω
  exact abs_le_finiteHorizonAbsoluteEnvelope_of_bound
    hRight T hboundω

/-- An `L²` process envelope gives the usual finite-horizon maximal tail
bound for the factorial-grid envelope. -/
theorem probReal_finiteHorizonAbsoluteEnvelope_gt_le
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {X : Process Ω} (hX : StronglyAdapted ℱ X)
    (T : ℝ≥0) {G : Ω → ℝ}
    (hG : MemLp G (2 : ℝ≥0∞) μ)
    (hbound : ∀ᵐ ω ∂μ, ∀ t, t ≤ T → |X t ω| ≤ G ω)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hGNorm : eLpNorm G (2 : ℝ≥0∞) μ ≤ ENNReal.ofReal C) :
    μ.real {ω | R < finiteHorizonAbsoluteEnvelope X T ω} ≤
      (C / R) ^ 2 := by
  have hEnvelopeMem :=
    finiteHorizonAbsoluteEnvelope_memLp_of_bound hX T hG hbound
  have hEnvelopeNorm :
      eLpNorm (finiteHorizonAbsoluteEnvelope X T) (2 : ℝ≥0∞) μ ≤
        eLpNorm G (2 : ℝ≥0∞) μ := by
    apply eLpNorm_mono_ae hEnvelopeMem.aestronglyMeasurable
    filter_upwards [hbound] with ω hBound
    have hGNonnegative : 0 ≤ G ω :=
      (abs_nonneg (X 0 ω)).trans (hBound 0 bot_le)
    have hEnvelopeNonnegative :
        0 ≤ finiteHorizonAbsoluteEnvelope X T ω :=
      Real.sqrt_nonneg _
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hEnvelopeNonnegative, abs_of_nonneg hGNonnegative]
    exact finiteHorizonAbsoluteEnvelope_le_of_bound X T hBound
  have hMeasure :
      μ {ω | R < finiteHorizonAbsoluteEnvelope X T ω} ≤
        (ENNReal.ofReal R)⁻¹ ^ 2 * (ENNReal.ofReal C) ^ 2 := by
    have hsubset :
        {ω | R < finiteHorizonAbsoluteEnvelope X T ω} ⊆
          {ω | ENNReal.ofReal R ≤
            ‖finiteHorizonAbsoluteEnvelope X T ω‖ₑ} := by
      intro ω hω
      change ENNReal.ofReal R ≤
        ‖finiteHorizonAbsoluteEnvelope X T ω‖ₑ
      have hEnvelopeNonnegative :
          0 ≤ finiteHorizonAbsoluteEnvelope X T ω :=
        Real.sqrt_nonneg _
      rw [Real.enorm_eq_ofReal hEnvelopeNonnegative]
      exact ENNReal.ofReal_le_ofReal hω.le
    calc
      μ {ω | R < finiteHorizonAbsoluteEnvelope X T ω} ≤
          μ {ω | ENNReal.ofReal R ≤
            ‖finiteHorizonAbsoluteEnvelope X T ω‖ₑ} :=
        measure_mono hsubset
      _ ≤ (ENNReal.ofReal R)⁻¹ ^ (2 : ℝ≥0∞).toReal *
          eLpNorm (finiteHorizonAbsoluteEnvelope X T)
            (2 : ℝ≥0∞) μ ^ (2 : ℝ≥0∞).toReal := by
        apply meas_ge_le_mul_pow_eLpNorm_enorm μ
          (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
        · exact ENNReal.ofReal_ne_zero_iff.mpr hR
        · simp
      _ ≤ (ENNReal.ofReal R)⁻¹ ^ 2 * (ENNReal.ofReal C) ^ 2 := by
        norm_num
        gcongr
        exact hEnvelopeNorm.trans hGNorm
  have hFinite :
      (ENNReal.ofReal R)⁻¹ ^ 2 * (ENNReal.ofReal C) ^ 2 ≠ ∞ := by
    finiteness
  have hReal := ENNReal.toReal_mono hFinite hMeasure
  change (μ {ω | R < finiteHorizonAbsoluteEnvelope X T ω}).toReal ≤ _
  calc
    (μ {ω | R < finiteHorizonAbsoluteEnvelope X T ω}).toReal ≤
        R⁻¹ ^ 2 * C ^ 2 := by
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_inv, ENNReal.toReal_ofReal hR.le,
        ENNReal.toReal_ofReal hC] using hReal
    _ = (C / R) ^ 2 := by
      rw [div_eq_mul_inv]
      ring

/-- Two arbitrary sample times bounded by the same horizon have a difference
whose tail is controlled by twice the process-envelope norm.  No ordering or
stopping-time property of the sample times is needed. -/
theorem probReal_sampledDifference_gt_le
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {X : Process Ω} (hX : StronglyAdapted ℱ X)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (T : ℝ≥0) (τ υ : Ω → ℝ≥0)
    (hτ : ∀ ω, τ ω ≤ T) (hυ : ∀ ω, υ ω ≤ T)
    {G : Ω → ℝ} (hG : MemLp G (2 : ℝ≥0∞) μ)
    (hbound : ∀ᵐ ω ∂μ, ∀ t, t ≤ T → |X t ω| ≤ G ω)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 < R)
    (hGNorm : eLpNorm G (2 : ℝ≥0∞) μ ≤ ENNReal.ofReal C) :
    μ.real {ω | R < |X (τ ω) ω - X (υ ω) ω|} ≤
      (2 * C / R) ^ 2 := by
  have hEnvelope : ∀ᵐ ω ∂μ, ∀ t, t ≤ T →
      |X t ω| ≤ finiteHorizonAbsoluteEnvelope X T ω :=
    abs_le_finiteHorizonAbsoluteEnvelope_ae hXRight T hbound
  have hsubset :
      {ω | R < |X (τ ω) ω - X (υ ω) ω|} ≤ᵐ[μ]
        {ω | R / 2 < finiteHorizonAbsoluteEnvelope X T ω} := by
    filter_upwards [hEnvelope] with ω hEnvelopeω
    intro hω
    change R < |X (τ ω) ω - X (υ ω) ω| at hω
    have hdiff : |X (τ ω) ω - X (υ ω) ω| ≤
        |X (τ ω) ω| + |X (υ ω) ω| := abs_sub _ _
    have hτBound := hEnvelopeω (τ ω) (hτ ω)
    have hυBound := hEnvelopeω (υ ω) (hυ ω)
    linarith
  have hmono :
      μ.real {ω | R < |X (τ ω) ω - X (υ ω) ω|} ≤
        μ.real {ω | R / 2 < finiteHorizonAbsoluteEnvelope X T ω} :=
    ENNReal.toReal_mono (by finiteness) (measure_mono_ae hsubset)
  apply hmono.trans
  calc
    μ.real {ω | R / 2 < finiteHorizonAbsoluteEnvelope X T ω} ≤
        (C / (R / 2)) ^ 2 :=
      probReal_finiteHorizonAbsoluteEnvelope_gt_le hX T hG hbound hC
        (by positivity) hGNorm
    _ = (2 * C / R) ^ 2 := by
      field_simp

end FactorialChronologicalGrid

end FTAPTheorem42
