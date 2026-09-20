/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Core.WeakStar
import FTAPTheorem42.Core.FSpace
import FTAPTheorem42.Core.L1DualRepresentation
import FTAPTheorem42.Core.WeakStarBoundedSlice
import FTAPTheorem42.Core.KreinSmulian
import FTAPTheorem42.Core.KreinSmulianC0
import FTAPTheorem42.Core.KreinSmulianC0Separation
import FTAPTheorem42.Core.C0DualCoefficients
import FTAPTheorem42.Core.KreinSmulianPredualSeparator
import FTAPTheorem42.Core.KreinSmulianCriterion
import FTAPTheorem42.Core.WeakStarFatouClosed
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The exponentially tilted envelope measure

For a nonnegative finite envelope `ξ`, this file records the elementary
measure-theoretic part of the change of measure used after the maximal
process estimate.  The density is `exp (-ξ)`, normalized to have total mass
one.  The stochastic-integral arguments which produce `ξ` are deliberately
kept out of this file.
-/

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace CommonEnvelopeMeasure

variable {μ : Measure Ω}

noncomputable def weight (ξ : Ω → ℝ) : Ω → ℝ≥0∞ :=
  fun ω => ENNReal.ofReal (Real.exp (-ξ ω))

noncomputable def normalizer (μ : Measure Ω) (ξ : Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, weight ξ ω ∂μ

noncomputable def tilted (μ : Measure Ω) (ξ : Ω → ℝ) : Measure Ω :=
  (normalizer μ ξ)⁻¹ • μ.withDensity (weight ξ)

theorem weight_measurable {ξ : Ω → ℝ} (hξ : Measurable ξ) :
    Measurable (weight ξ) := by
  exact (hξ.neg.exp).ennreal_ofReal

omit [MeasurableSpace Ω] in
theorem weight_pos (ξ : Ω → ℝ) (ω : Ω) : 0 < weight ξ ω := by
  exact ENNReal.ofReal_pos.2 (Real.exp_pos _)

omit [MeasurableSpace Ω] in
theorem weight_le_one {ξ : Ω → ℝ} (hξ : ∀ ω, 0 ≤ ξ ω) :
    ∀ ω, weight ξ ω ≤ 1 := by
  intro ω
  rw [weight, ENNReal.ofReal_le_one]
  rw [Real.exp_le_one_iff]
  linarith [hξ ω]

theorem normalizer_pos [IsProbabilityMeasure μ] {ξ : Ω → ℝ} (hξ : Measurable ξ) :
    0 < normalizer μ ξ := by
  rw [normalizer, (lintegral_pos_iff_support (weight_measurable hξ))]
  rw [show Function.support (weight ξ) = Set.univ by
    ext ω
    simp [Function.mem_support, ne_of_gt (weight_pos ξ ω)]]
  simp

theorem normalizer_le_one [IsProbabilityMeasure μ] {ξ : Ω → ℝ} (hξ : ∀ ω, 0 ≤ ξ ω) :
    normalizer μ ξ ≤ 1 := by
  rw [normalizer]
  calc
    ∫⁻ ω, weight ξ ω ∂μ ≤ ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂μ :=
      lintegral_mono (weight_le_one hξ)
    _ = 1 := by simp

theorem normalizer_ne_top [IsProbabilityMeasure μ] {ξ : Ω → ℝ} (hξ : ∀ ω, 0 ≤ ξ ω) :
    normalizer μ ξ ≠ ∞ := by
  exact ne_of_lt (lt_of_le_of_lt (normalizer_le_one hξ) ENNReal.one_lt_top)

theorem tilted_isProbabilityMeasure [IsProbabilityMeasure μ] {ξ : Ω → ℝ}
    (hξ_meas : Measurable ξ) (hξ_nonneg : ∀ ω, 0 ≤ ξ ω) :
    IsProbabilityMeasure (tilted μ ξ) := by
  constructor
  change (normalizer μ ξ)⁻¹ * (μ.withDensity (weight ξ)) univ = 1
  have hmass : (μ.withDensity (weight ξ)) univ = normalizer μ ξ := by
    rw [withDensity_apply (weight ξ) MeasurableSet.univ]
    simp [normalizer]
  rw [hmass]
  exact ENNReal.inv_mul_cancel
    (ne_of_gt (normalizer_pos (μ := μ) hξ_meas))
    (normalizer_ne_top (μ := μ) hξ_nonneg)

theorem tilted_absolutelyContinuous {ξ : Ω → ℝ} :
    tilted μ ξ ≪ μ := by
  unfold tilted
  exact Measure.smul_absolutelyContinuous.trans
    (withDensity_absolutelyContinuous μ (weight ξ))

/-- The normalized exponential density is bounded by the inverse normalizer. -/
theorem tilted_le_smul {ξ : Ω → ℝ} (hξ : ∀ ω, 0 ≤ ξ ω) :
    tilted μ ξ ≤ (normalizer μ ξ)⁻¹ • μ := by
  apply _root_.smul_le_smul_left
  simpa only [withDensity_const, one_smul] using
    (withDensity_mono (μ := μ) (Eventually.of_forall (weight_le_one hξ)))

/-- Exponential tilting preserves an existing `Lp` envelope. -/
theorem memLp_tilted [IsProbabilityMeasure μ] {ξ f : Ω → ℝ} {p : ℝ≥0∞}
    (hξ_meas : Measurable ξ) (hξ_nonneg : ∀ ω, 0 ≤ ξ ω)
    (hf : MemLp f p μ) : MemLp f p (tilted μ ξ) := by
  exact (hf.smul_measure (ENNReal.inv_ne_top.mpr
    (normalizer_pos hξ_meas).ne')).mono_measure (tilted_le_smul hξ_nonneg)

theorem absolutelyContinuous_tilted [IsProbabilityMeasure μ] {ξ : Ω → ℝ}
    (hξ_meas : Measurable ξ) (hξ_nonneg : ∀ ω, 0 ≤ ξ ω) :
    μ ≪ tilted μ ξ := by
  unfold tilted
  have hpos : ∀ᵐ ω ∂μ, weight ξ ω ≠ 0 :=
    Filter.Eventually.of_forall (fun ω => ne_of_gt (weight_pos ξ ω))
  have hac : μ ≪ μ.withDensity (weight ξ) :=
    withDensity_absolutelyContinuous' (weight_measurable hξ_meas).aemeasurable hpos
  exact hac.trans (Measure.absolutelyContinuous_smul
    (ENNReal.inv_ne_zero.2 (normalizer_ne_top hξ_nonneg)))

omit [MeasurableSpace Ω] in
theorem sq_mul_exp_neg_le_four {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 * Real.exp (-x) ≤ 4 := by
  have h := Real.mul_exp_neg_le_exp_neg_one (x / 2)
  have h₁ : x * Real.exp (-(x / 2)) ≤ 2 * Real.exp (-1) := by
    nlinarith
  have h₁_nonneg : 0 ≤ x * Real.exp (-(x / 2)) :=
    mul_nonneg hx (Real.exp_pos _).le
  have h₂_nonneg : 0 ≤ 2 * Real.exp (-1) := by positivity
  have hsq := (sq_le_sq₀ h₁_nonneg h₂_nonneg).2 h₁
  calc
    x ^ 2 * Real.exp (-x) =
        (x * Real.exp (-(x / 2))) ^ 2 := by
          rw [mul_pow, show -x = -(x / 2) + -(x / 2) by ring, Real.exp_add]
          ring
    _ ≤ (2 * Real.exp (-1)) ^ 2 := hsq
    _ ≤ 4 := by
      have he : Real.exp (-1) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        norm_num
      nlinarith [Real.exp_pos (-1)]

theorem memLp_two_tilted [IsProbabilityMeasure μ]
    {ξ : Ω → ℝ} (hξ_meas : Measurable ξ) (hξ_nonneg : ∀ ω, 0 ≤ ξ ω) :
    MemLp ξ 2 (tilted μ ξ) := by
  refine (memLp_two_iff_integrable_sq hξ_meas.aestronglyMeasurable).2 ?_
  unfold tilted
  apply Integrable.smul_measure
  · rw [integrable_withDensity_iff (weight_measurable hξ_meas)]
    · have hmeas : AEStronglyMeasurable
          (fun ω => ξ ω ^ 2 * Real.exp (-ξ ω)) μ := by
          fun_prop
      have hint : Integrable (fun ω => ξ ω ^ 2 * Real.exp (-ξ ω)) μ := by
        apply Integrable.mono' (integrable_const 4) hmeas
        filter_upwards with ω
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
        exact sq_mul_exp_neg_le_four (hξ_nonneg ω)
      convert hint using 1
      ext ω
      simp [weight, ENNReal.toReal_ofReal (Real.exp_pos _).le]
    · filter_upwards with ω
      simp [weight]
  · exact ENNReal.inv_ne_top.2 (ne_of_gt (normalizer_pos (μ := μ) hξ_meas))

end CommonEnvelopeMeasure
end FTAPTheorem42

namespace FTAPTheorem42
open MeasureTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/--
A nonnegative `Lᵖ` envelope transfers membership to every a.e. strongly
measurable real-valued random variable which it dominates in norm.
-/
theorem memLp_of_ae_norm_le_nonnegative_envelope
    {μ : Measure Ω} {p : ℝ≥0∞} {f ξ : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hξ : MemLp ξ p μ)
    (hξ_nonneg : ∀ᵐ ω ∂μ, 0 ≤ ξ ω)
    (hdom : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ ξ ω) :
    MemLp f p μ := by
  apply hξ.of_le hf
  filter_upwards [hξ_nonneg, hdom] with ω hξω hdomω
  exact hdomω.trans_eq (by
    rw [Real.norm_eq_abs, abs_of_nonneg hξω])

end FTAPTheorem42
