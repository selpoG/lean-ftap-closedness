/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.CadlagEnvelope

/-! # Truncated absolute expectation

The expectation of min(|f|, 1) is nonnegative and at most one on a probability
space. Measurability and integrability are supplied for later test estimates. -/

namespace FTAPTheorem42

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SemimartingaleQuasiNorm

/-- The expectation of a real random variable truncated at one in absolute
value. -/
noncomputable def truncatedExpectation
    (μ : Measure Ω) (f : Ω → ℝ) : ℝ :=
  ∫ ω, min |f ω| 1 ∂μ

theorem stronglyMeasurable_truncatedExpectationIntegrand
    {f : Ω → ℝ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun ω => min |f ω| 1) := by
  simpa only [Real.norm_eq_abs] using
    (continuous_fst.min continuous_snd).comp_stronglyMeasurable
      (hf.norm.prodMk (stronglyMeasurable_const :
        StronglyMeasurable (fun _ : Ω => (1 : ℝ))))

theorem integrable_truncatedExpectationIntegrand
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : StronglyMeasurable f) :
    Integrable (fun ω => min |f ω| 1) μ := by
  apply Integrable.of_bound
    (stronglyMeasurable_truncatedExpectationIntegrand hf).aestronglyMeasurable
    1
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact min_le_right _ _
  · exact le_min (abs_nonneg _) zero_le_one

theorem truncatedExpectation_nonnegative
    {μ : Measure Ω} {f : Ω → ℝ} :
    0 ≤ truncatedExpectation μ f := by
  apply integral_nonneg_of_ae
  filter_upwards [] with ω
  exact le_min (abs_nonneg _) zero_le_one

theorem truncatedExpectation_le_one
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : StronglyMeasurable f) :
    truncatedExpectation μ f ≤ 1 := by
  unfold truncatedExpectation
  calc
    (∫ ω, min |f ω| 1 ∂μ) ≤ ∫ _ : Ω, (1 : ℝ) ∂μ := by
      apply integral_mono_ae
        (integrable_truncatedExpectationIntegrand hf)
        (integrable_const 1)
      filter_upwards [] with ω
      exact min_le_right _ _
    _ = 1 := by simp

/-- Scaling an envelope controls its unit cap by the same cap times `max a 1`. -/
theorem cappedEnvelope_cap_scale
    (a : ℝ) (ha : 0 ≤ a) (E : ℝ≥0∞) :
    (min (ENNReal.ofReal a * E) 1).toReal ≤
      max a 1 * (min E 1).toReal := by
  by_cases hE : E = ∞
  · rw [hE]
    by_cases ha0 : a = 0
    · simp [ha0]
    · have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hmul : ENNReal.ofReal a * ∞ = ∞ :=
        ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr haPos))
      rw [hmul]
      have hmin : min (∞ : ℝ≥0∞) 1 = 1 := min_eq_right le_top
      rw [hmin]
      simp only [ENNReal.toReal_one]
      simpa only [mul_one] using (le_max_right a 1)
  · have hprod : ENNReal.ofReal a * E ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE
    rw [ENNReal.toReal_min hprod ENNReal.one_ne_top,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal ha,
      ENNReal.toReal_min hE ENNReal.one_ne_top]
    simp only [ENNReal.toReal_one]
    by_cases ha1 : a ≤ 1
    · by_cases hE1 : E.toReal ≤ 1
      · have hxa : a * E.toReal ≤ E.toReal :=
          mul_le_of_le_one_left ENNReal.toReal_nonneg ha1
        have hxa1 : a * E.toReal ≤ 1 := hxa.trans hE1
        have hcap : min E.toReal 1 = E.toReal := min_eq_left hE1
        rw [hcap, min_eq_left hxa1]
        exact hxa.trans (le_mul_of_one_le_left
          ENNReal.toReal_nonneg (le_max_right a 1))
      · have hE1' : 1 ≤ E.toReal := le_of_not_ge hE1
        have hcap : min E.toReal 1 = 1 := min_eq_right hE1'
        rw [hcap]
        calc
          min (a * E.toReal) 1 ≤ 1 := min_le_right _ _
          _ ≤ max a 1 := le_max_right _ _
          _ = max a 1 * 1 := (mul_one _).symm
    · have ha1' : 1 ≤ a := le_of_not_ge ha1
      by_cases hE1 : E.toReal ≤ 1
      · have hcap : min E.toReal 1 = E.toReal := min_eq_left hE1
        rw [hcap, max_eq_left ha1']
        exact min_le_left _ _
      · have hcap : min E.toReal 1 = 1 := min_eq_right (le_of_not_ge hE1)
        rw [hcap, max_eq_left ha1']
        simp only [mul_one]
        exact (min_le_right _ _).trans ha1'

end SemimartingaleQuasiNorm

end FTAPTheorem42
