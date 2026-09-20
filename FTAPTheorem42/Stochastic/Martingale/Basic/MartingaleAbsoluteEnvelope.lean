/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Basic.ContinuousDoobEnvelope

/-!
# Absolute-value envelopes for real martingales

The absolute value of a real martingale is a nonnegative submartingale.
Combining this fact with the continuous-time Doob estimate gives a square
integrable envelope which dominates the absolute value of the martingale at
every deterministic time before the horizon.
-/

open Filter MeasureTheory
open scoped ENNReal MeasureTheory NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The absolute value of a real martingale is a submartingale. -/
theorem Martingale.abs_submartingale
    {Time : Type*} [Preorder Time]
    {μ : Measure Ω}
    {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}
    {M : Time → Ω → ℝ} (hM : Martingale M ℱ μ) :
    Submartingale (fun t ω => |M t ω|) ℱ μ := by
  refine ⟨?_, ?_, ?_⟩
  · intro t
    simpa only [Real.norm_eq_abs] using
      (hM.stronglyMeasurable t).norm
  · intro i j hij
    filter_upwards [hM.condExp_ae_eq hij,
      abs_condExp_ae_le_condExp_abs (μ := μ) (m := ℱ i) (M j)]
        with ω heq hle
    change |μ[M j | ℱ i] ω| ≤ μ[(fun ω => |M j ω|) | ℱ i] ω at hle
    rw [heq] at hle
    exact hle
  · intro t
    exact (hM.integrable t).abs

namespace FactorialChronologicalGrid

/-- A real-valued version of the squared factorial-grid envelope. -/
noncomputable def martingaleAbsoluteEnvelope
    (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) : Ω → ℝ :=
  fun ω => Real.sqrt ((eFactorialRunningMaxSqEnvelope
    (fun t ω => |M t ω|) T ω).toReal)

theorem measurable_martingaleAbsoluteEnvelope
    (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (hM : ∀ t, Measurable (M t)) :
    Measurable (martingaleAbsoluteEnvelope M T) := by
  exact ((measurable_eFactorialRunningMaxSqEnvelope
    (fun t ω => |M t ω|) T (fun t => by
      simpa only [Real.norm_eq_abs] using (hM t).norm)).ennreal_toReal).sqrt

/-- The continuous-time Doob estimate applied to the absolute value of a
real martingale. -/
theorem Martingale.lintegral_eFactorialRunningMaxSqEnvelope_abs_le
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ μ)
    (T : ℝ≥0) (hterminal : MemLp (M T) (2 : ℝ≥0∞) μ) :
    (∫⁻ ω, eFactorialRunningMaxSqEnvelope
        (fun t ω => |M t ω|) T ω ∂μ) ≤
      4 * ∫⁻ ω, ENNReal.ofReal ((M T ω) ^ 2) ∂μ := by
  simpa only [sq_abs] using
    Submartingale.lintegral_eFactorialRunningMaxSqEnvelope_le
      (FTAPTheorem42.Martingale.abs_submartingale hM)
      (fun _ _ => abs_nonneg _) T hterminal.abs

/-- The extended squared factorial-grid envelope of a square-integrable
martingale is finite almost surely.  No path regularity is needed. -/
theorem Martingale.eFactorialRunningMaxSqEnvelope_abs_ae_lt_top
    {mu : Measure Ω} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {M : Process Ω} (hM : Martingale M F mu)
    (T : NNReal) (hterminal : MemLp (M T) (2 : ENNReal) mu) :
    ∀ᵐ omega ∂mu,
      eFactorialRunningMaxSqEnvelope
        (fun t omega => |M t omega|) T omega < ∞ := by
  have hMeasurable : Measurable
      (eFactorialRunningMaxSqEnvelope
        (fun t omega => |M t omega|) T) :=
    measurable_eFactorialRunningMaxSqEnvelope
      (fun t omega => |M t omega|) T
      (fun t => by simpa only [Real.norm_eq_abs] using
        ((hM.stronglyMeasurable t).mono (F.le t)).norm.measurable)
  apply ae_lt_top hMeasurable
  apply ne_of_lt
  exact (Martingale.lintegral_eFactorialRunningMaxSqEnvelope_abs_le
    hM T hterminal).trans_lt
    (ENNReal.mul_lt_top (by norm_num) hterminal.integrable_sq.lintegral_lt_top)

/-- Terminal `L²` control makes the real absolute-value envelope itself an
`L²` random variable. -/
theorem Martingale.martingaleAbsoluteEnvelope_memLp
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ μ)
    (T : ℝ≥0) (hterminal : MemLp (M T) (2 : ℝ≥0∞) μ) :
    MemLp (martingaleAbsoluteEnvelope M T) (2 : ℝ≥0∞) μ := by
  let Z := eFactorialRunningMaxSqEnvelope
    (fun t ω => |M t ω|) T
  have hZmeas : Measurable Z :=
    measurable_eFactorialRunningMaxSqEnvelope
      (fun t ω => |M t ω|) T
      (fun t => by simpa only [Real.norm_eq_abs] using
        ((hM.stronglyMeasurable t).mono (ℱ.le t)).norm.measurable)
  have hterminalFinite :
      (∫⁻ ω, ENNReal.ofReal ((M T ω) ^ 2) ∂μ) < ∞ :=
    hterminal.integrable_sq.lintegral_lt_top
  have hZne : (∫⁻ ω, Z ω ∂μ) ≠ ∞ := by
    apply ne_of_lt
    exact (Martingale.lintegral_eFactorialRunningMaxSqEnvelope_abs_le
      hM T hterminal).trans_lt
      (ENNReal.mul_lt_top (by norm_num) hterminalFinite)
  have htoReal : Integrable (fun ω => (Z ω).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hZmeas.aemeasurable hZne
  apply (memLp_two_iff_integrable_sq
    (measurable_martingaleAbsoluteEnvelope M T
      (fun t => ((hM.stronglyMeasurable t).mono
        (ℱ.le t)).measurable)).aestronglyMeasurable).2
  convert htoReal using 1
  funext ω
  exact Real.sq_sqrt (ENNReal.toReal_nonneg)

/-- Doob's `L²` inequality in seminorm form for the continuous-time
absolute-value envelope. -/
theorem Martingale.eLpNorm_martingaleAbsoluteEnvelope_le_two_mul
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ μ)
    (T : ℝ≥0) (hterminal : MemLp (M T) (2 : ℝ≥0∞) μ) :
    eLpNorm (martingaleAbsoluteEnvelope M T) (2 : ℝ≥0∞) μ ≤
      2 * eLpNorm (M T) (2 : ℝ≥0∞) μ := by
  let E := martingaleAbsoluteEnvelope M T
  let Z := eFactorialRunningMaxSqEnvelope
    (fun t ω => |M t ω|) T
  have hE : MemLp E (2 : ℝ≥0∞) μ :=
    Martingale.martingaleAbsoluteEnvelope_memLp hM T hterminal
  have hEsqInt : Integrable (fun ω => E ω ^ 2) μ := by
    exact (hE.integrable_mul hE).congr
      (Filter.Eventually.of_forall fun ω => by simp [pow_two])
  have hTsqInt : Integrable (fun ω => (M T ω) ^ 2) μ := by
    exact (hterminal.integrable_mul hterminal).congr
      (Filter.Eventually.of_forall fun ω => by simp [pow_two])
  have hEsqNonneg : ∀ᵐ ω ∂μ, 0 ≤ E ω ^ 2 :=
    Filter.Eventually.of_forall fun ω => sq_nonneg (E ω)
  have hTsqNonneg : ∀ᵐ ω ∂μ, 0 ≤ (M T ω) ^ 2 :=
    Filter.Eventually.of_forall fun ω => sq_nonneg (M T ω)
  have hEnvelopeLIntegral :
      (∫⁻ ω, ENNReal.ofReal (E ω ^ 2) ∂μ) ≤ ∫⁻ ω, Z ω ∂μ := by
    apply lintegral_mono
    intro ω
    unfold E martingaleAbsoluteEnvelope Z
    change ENNReal.ofReal
      (Real.sqrt
        (eFactorialRunningMaxSqEnvelope
          (fun t ω => |M t ω|) T ω).toReal ^ 2) ≤ _
    rw [Real.sq_sqrt ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal_le
  have hSecond :
      (∫ ω, E ω ^ 2 ∂μ) ≤ 4 * ∫ ω, (M T ω) ^ 2 ∂μ := by
    apply (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (by norm_num) (integral_nonneg_of_ae hTsqNonneg))).mp
    rw [ofReal_integral_eq_lintegral_ofReal hEsqInt hEsqNonneg,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
      ofReal_integral_eq_lintegral_ofReal hTsqInt hTsqNonneg]
    exact hEnvelopeLIntegral.trans (by
      simpa only [Z, ENNReal.ofReal_ofNat] using
        Martingale.lintegral_eFactorialRunningMaxSqEnvelope_abs_le
          hM T hterminal)
  apply (ENNReal.toReal_le_toReal hE.eLpNorm_ne_top
    (ENNReal.mul_ne_top (by norm_num) hterminal.eLpNorm_ne_top)).mp
  rw [eLpNorm_two_toReal_eq_sqrt_integral_norm_sq hE,
    ENNReal.toReal_mul,
    eLpNorm_two_toReal_eq_sqrt_integral_norm_sq hterminal]
  norm_num only [ENNReal.toReal_ofNat]
  have hEIntegralNonneg : 0 ≤ ∫ ω, ‖E ω‖ ^ 2 ∂μ :=
    integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun ω => sq_nonneg ‖E ω‖)
  have hTIntegralNonneg : 0 ≤ ∫ ω, ‖M T ω‖ ^ 2 ∂μ :=
    integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun ω => sq_nonneg ‖M T ω‖)
  have hSecondNorm :
      (∫ ω, ‖E ω‖ ^ 2 ∂μ) ≤ 4 * ∫ ω, ‖M T ω‖ ^ 2 ∂μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using hSecond
  nlinarith [Real.sq_sqrt hEIntegralNonneg,
    Real.sq_sqrt hTIntegralNonneg,
    Real.sqrt_nonneg (∫ ω, ‖E ω‖ ^ 2 ∂μ),
    Real.sqrt_nonneg (∫ ω, ‖M T ω‖ ^ 2 ∂μ)]

/-- The real envelope dominates the martingale at every time up to `T`,
outside one null set independent of time. -/
theorem Martingale.norm_le_martingaleAbsoluteEnvelope_ae
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ μ)
    (T : ℝ≥0) (hterminal : MemLp (M T) (2 : ℝ≥0∞) μ)
    (hMRight : ∀ ω t,
      ContinuousWithinAt (M · ω) (Set.Ici t) t) :
    ∀ᵐ ω ∂μ, ∀ t, t ≤ T → ‖M t ω‖ ≤
      martingaleAbsoluteEnvelope M T ω := by
  let Z := eFactorialRunningMaxSqEnvelope
    (fun t ω => |M t ω|) T
  have hZmeas : Measurable Z :=
    measurable_eFactorialRunningMaxSqEnvelope
      (fun t ω => |M t ω|) T
      (fun t => by simpa only [Real.norm_eq_abs] using
        ((hM.stronglyMeasurable t).mono (ℱ.le t)).norm.measurable)
  have hterminalFinite :
      (∫⁻ ω, ENNReal.ofReal ((M T ω) ^ 2) ∂μ) < ∞ :=
    hterminal.integrable_sq.lintegral_lt_top
  have hZne : (∫⁻ ω, Z ω ∂μ) ≠ ∞ := by
    apply ne_of_lt
    exact (Martingale.lintegral_eFactorialRunningMaxSqEnvelope_abs_le
      hM T hterminal).trans_lt
      (ENNReal.mul_lt_top (by norm_num) hterminalFinite)
  filter_upwards [ae_lt_top hZmeas hZne] with ω hZω
  intro t ht
  rw [Real.norm_eq_abs]
  apply Real.le_sqrt_of_sq_le
  have hENN := ofReal_sq_le_eFactorialRunningMaxSqEnvelope
    (fun t ω => |M t ω|) T (fun _ _ => abs_nonneg _)
    (fun ω t => (hMRight ω t).abs) ω ht
  have hReal := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hZω.ne).2 hENN
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _), sq_abs] using hReal

/-- Doob envelope of the difference between a sequence member and its limit. -/
noncomputable def martingaleDifferenceEnvelope
    (Nbar : Nat → Process Ω) (M : Process Ω) (T : NNReal)
    (n : Nat) : Ω → Real :=
  martingaleAbsoluteEnvelope (fun t => Nbar n t - M t) T

end FactorialChronologicalGrid

end FTAPTheorem42
