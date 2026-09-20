/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Memin.ControlLIntegral

/-!
# An equivalent measure for the finite-variation half of Mémin localization

An almost surely summable sequence of nonnegative random variables need not
have summable expectations under the original probability measure.  Weighting
the measure by the squared reciprocal of one plus the pointwise sum makes all
those expectations summable while preserving the almost-everywhere relation.

This module applies that normalization to the successive whole-axis variation
differences extracted after Lemma 4.11.  It supplies the finite-variation half
of the local `S¹` estimate required by Mémin's stochastic-integral closedness
argument.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace MeminEquivalentFiniteVariationMeasure

/-- Pointwise extended sum used to normalize an almost surely summable
sequence of nonnegative real random variables. -/
noncomputable def summableEnvelope (V : ℕ → Ω → ℝ) : Ω → ℝ≥0∞ :=
  fun ω => ∑' n, ENNReal.ofReal (V n ω)

/-- Squared reciprocal density which turns pointwise summability into
summability of expectations and controls every term in `L²`. -/
noncomputable def referenceDensity (V : ℕ → Ω → ℝ) : Ω → ℝ≥0∞ :=
  fun ω => ((1 + summableEnvelope V ω) ^ 2)⁻¹

/-- The finite reference measure associated with a pointwise summable
nonnegative sequence. -/
noncomputable def referenceMeasure (μ : Measure Ω) (V : ℕ → Ω → ℝ) :
    Measure Ω :=
  μ.withDensity (referenceDensity V)

theorem summableEnvelope_measurable {V : ℕ → Ω → ℝ}
    (hV : ∀ n, Measurable (V n)) : Measurable (summableEnvelope V) := by
  exact Measurable.tsum fun n => (hV n).ennreal_ofReal

theorem referenceDensity_measurable {V : ℕ → Ω → ℝ}
    (hV : ∀ n, Measurable (V n)) : Measurable (referenceDensity V) := by
  exact ((measurable_const.add
    (summableEnvelope_measurable hV)).pow_const 2).inv

omit [MeasurableSpace Ω] in
theorem referenceDensity_le_one (V : ℕ → Ω → ℝ) (ω : Ω) :
    referenceDensity V ω ≤ 1 := by
  apply ENNReal.inv_le_one.2
  exact one_le_pow_of_one_le' (le_add_right le_rfl) 2

omit [MeasurableSpace Ω] in
theorem referenceDensity_ne_top (V : ℕ → Ω → ℝ) (ω : Ω) :
    referenceDensity V ω ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    (referenceDensity_le_one V ω)

omit [MeasurableSpace Ω] in
theorem referenceDensity_mul_envelope_le_one
    (V : ℕ → Ω → ℝ) (ω : Ω) :
    referenceDensity V ω * summableEnvelope V ω ≤ 1 := by
  let R := summableEnvelope V ω
  have hR : R ≤ (1 + R) ^ 2 := by
    calc
      R ≤ 1 + R := le_add_left le_rfl
      _ = 1 * (1 + R) := (one_mul _).symm
      _ ≤ (1 + R) * (1 + R) :=
        mul_le_mul_left (le_add_right le_rfl) _
      _ = (1 + R) ^ 2 := (pow_two _).symm
  calc
    referenceDensity V ω * summableEnvelope V ω ≤
        referenceDensity V ω * ((1 + summableEnvelope V ω) ^ 2) :=
      mul_le_mul_right hR _
    _ ≤ 1 := ENNReal.inv_mul_le_one _

omit [MeasurableSpace Ω] in
theorem referenceDensity_mul_term_sq_le_one
    (V : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    referenceDensity V ω * (ENNReal.ofReal (V n ω)) ^ 2 ≤ 1 := by
  have hTerm : ENNReal.ofReal (V n ω) ≤ summableEnvelope V ω := by
    exact ENNReal.le_tsum (f := fun k => ENNReal.ofReal (V k ω)) n
  have hSq : (ENNReal.ofReal (V n ω)) ^ 2 ≤
      (1 + summableEnvelope V ω) ^ 2 := by
    gcongr
    exact hTerm.trans (le_add_left le_rfl)
  calc
    referenceDensity V ω * (ENNReal.ofReal (V n ω)) ^ 2 ≤
        referenceDensity V ω * (1 + summableEnvelope V ω) ^ 2 :=
      mul_le_mul_right hSq _
    _ ≤ 1 := ENNReal.inv_mul_le_one _

/-- The reciprocal normalization makes the sum of all `L¹` sizes finite.
The upper bound is the mass of the original finite measure. -/
theorem tsum_lintegral_referenceMeasure_le {μ : Measure Ω}
    [IsFiniteMeasure μ] {V : ℕ → Ω → ℝ}
    (hV : ∀ n, Measurable (V n)) :
    (∑' n, ∫⁻ ω, ENNReal.ofReal (V n ω) ∂referenceMeasure μ V) ≤
      μ Set.univ := by
  rw [← lintegral_tsum fun n =>
    ((hV n).ennreal_ofReal.aemeasurable (μ := referenceMeasure μ V))]
  change (∫⁻ ω, summableEnvelope V ω ∂
    μ.withDensity (referenceDensity V)) ≤ μ Set.univ
  rw [lintegral_withDensity_eq_lintegral_mul μ
    (referenceDensity_measurable hV) (summableEnvelope_measurable hV)]
  calc
    ∫⁻ ω, referenceDensity V ω * summableEnvelope V ω ∂μ ≤
        ∫⁻ _ω : Ω, (1 : ℝ≥0∞) ∂μ := by
      apply lintegral_mono
      intro ω
      exact referenceDensity_mul_envelope_le_one V ω
    _ = μ Set.univ := by simp

theorem tsum_lintegral_referenceMeasure_ne_top {μ : Measure Ω}
    [IsFiniteMeasure μ] {V : ℕ → Ω → ℝ}
    (hV : ∀ n, Measurable (V n)) :
    (∑' n, ∫⁻ ω, ENNReal.ofReal (V n ω) ∂referenceMeasure μ V) ≠
      ∞ := by
  exact ne_top_of_le_ne_top (measure_ne_top μ Set.univ)
    (tsum_lintegral_referenceMeasure_le hV)

/-- Each nonnegative term is square integrable under the common normalized
reference measure. -/
theorem term_memLp_two_referenceMeasure {μ : Measure Ω}
    [IsFiniteMeasure μ] {V : ℕ → Ω → ℝ}
    (hV : ∀ n, Measurable (V n))
    (hVNonnegative : ∀ n ω, 0 ≤ V n ω) (n : ℕ) :
    MemLp (V n) (2 : ℝ≥0∞) (referenceMeasure μ V) := by
  apply (memLp_two_iff_integrable_sq
    (hV n).aestronglyMeasurable).2
  apply (integrable_withDensity_iff
    (referenceDensity_measurable hV)
    (Eventually.of_forall fun ω =>
      (referenceDensity_le_one V ω).trans_lt ENNReal.one_lt_top)).2
  apply (integrable_const (1 : ℝ)).mono'
    ((hV n).pow_const 2 |>.mul
      (referenceDensity_measurable hV).ennreal_toReal
      |>.aestronglyMeasurable)
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · have hBound := referenceDensity_mul_term_sq_le_one V n ω
    have hReal := ENNReal.toReal_mono ENNReal.one_ne_top hBound
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (hVNonnegative n ω),
      ENNReal.toReal_one] at hReal
    change V n ω ^ 2 * (referenceDensity V ω).toReal ≤ 1
    simpa only [mul_comm] using hReal
  · exact mul_nonneg (sq_nonneg _)
      ENNReal.toReal_nonneg

end MeminEquivalentFiniteVariationMeasure

end FTAPTheorem42
