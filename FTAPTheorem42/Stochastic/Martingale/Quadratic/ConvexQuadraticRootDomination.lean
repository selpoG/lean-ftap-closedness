/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Compactness.ForwardConvexUniformIntegrability

/-! # Integrable variation bounds for convex quadratic roots -/

open Filter MeasureTheory
open scoped ENNReal NNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω}

private theorem ui_add {f g : Nat → Ω → Real}
    (hf : UniformIntegrable f 1 mu) (hg : UniformIntegrable g 1 mu) :
    UniformIntegrable (f + g) 1 mu := by
  obtain ⟨C, hC⟩ := hf.2
  obtain ⟨D, hD⟩ := hg.2
  refine ⟨hf.unifIntegrable.add hg.unifIntegrable le_rfl, C + D, ?_⟩
  intro n
  exact (eLpNorm_add_le le_rfl).trans
    (by simpa using add_le_add (hC n) (hD n))

private theorem ui_mono {f g : Nat → Ω → Real}
    (hf : UniformIntegrable f 1 mu) (hg : ∀ n, AEStronglyMeasurable (g n) mu)
    (hBound : ∀ n, ∀ᵐ w ∂mu, ‖g n w‖ ≤ ‖f n w‖) :
    UniformIntegrable g 1 mu := by
  refine ⟨unifIntegrable_iff.2 ?_, ?_⟩
  · intro ε hε
    obtain ⟨δ, hδ, h⟩ := unifIntegrable_iff.1 hf.unifIntegrable ε hε
    refine ⟨δ, hδ, fun n s hμ => ?_⟩
    exact (eLpNorm_mono_ae
      ((hg n).mono_measure Measure.restrict_le_self)
      (ae_restrict_of_ae (hBound n))).trans (h n s hμ)
  · obtain ⟨C, hC⟩ := hf.2
    exact ⟨C, fun n => (eLpNorm_mono_ae (hg n) (hBound n)).trans (hC n)⟩

/-- A common integrable root error remains sufficient after arbitrary
forward convexification of the energies. No second moment of the error is used. -/
theorem ForwardConvexWeights.uniformIntegrable_sqrt_of_root_bound
    [IsProbabilityMeasure mu] (W : ForwardConvexWeights)
    {E B : Nat → Ω → Real} {A : Ω → Real}
    (hB : UniformIntegrable B 1 mu) (hA : Integrable A mu)
    (hE : ∀ n, AEStronglyMeasurable (E n) mu)
    (hEn : ∀ n w, 0 ≤ E n w) (hBn : ∀ n w, 0 ≤ B n w)
    (hAn : ∀ w, 0 ≤ A w)
    (hRoot : ∀ n w, Real.sqrt (E n w) ≤ Real.sqrt (B n w) + A w) :
    UniformIntegrable (fun k w => Real.sqrt (W.apply E k w)) 1 mu := by
  have hWB := W.uniformIntegrable_apply le_rfl hB
  have hC : UniformIntegrable (fun _ : Nat => fun w => 1 + A w) 1 mu :=
    uniformIntegrable_const le_rfl ENNReal.one_ne_top
      (memLp_one_iff_integrable.mpr ((integrable_const 1).add hA))
  have hMajor := ui_add (ui_add hWB hWB) (ui_add hC hC)
  apply ui_mono hMajor
    (fun k => Real.continuous_sqrt.comp_aestronglyMeasurable
      (W.apply_aestronglyMeasurable hE k))
  · intro k
    filter_upwards [] with w
    have hB0 : 0 ≤ W.apply B k w :=
      Finset.sum_nonneg fun i hi => mul_nonneg (W.nonneg k i hi) (hBn i w)
    have hA0 := hAn w
    have hEnergy : W.apply E k w ≤ 2 * W.apply B k w + 2 * (A w) ^ 2 := by
      calc
        _ ≤ ∑ i ∈ W.support k, W.weight k i * (2 * B i w + 2 * (A w) ^ 2) := by
          apply Finset.sum_le_sum
          intro i hi
          apply mul_le_mul_of_nonneg_left _ (W.nonneg k i hi)
          have hr := hRoot i w
          have he := Real.sq_sqrt (hEn i w)
          have hb := Real.sq_sqrt (hBn i w)
          nlinarith [sq_nonneg (Real.sqrt (B i w) - A w),
            sq_nonneg (Real.sqrt (B i w) + A w - Real.sqrt (E i w)),
            mul_nonneg (Real.sqrt_nonneg (E i w))
              (sub_nonneg.mpr hr)]
        _ = _ := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, W.sum_eq_one,
            one_mul]
          simp only [ForwardConvexWeights.apply]
          rw [Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          ring
    have hBound : Real.sqrt (W.apply E k w) ≤
        2 * W.apply B k w + 2 * (1 + A w) := by
      apply (Real.sqrt_le_iff).mpr
      refine ⟨by positivity, ?_⟩
      nlinarith [sq_nonneg (W.apply B k w), sq_nonneg (A w),
        mul_nonneg hB0 (hAn w)]
    simp only [Pi.add_apply, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (show 0 ≤ W.apply B k w + W.apply B k w +
        ((1 + A w) + (1 + A w)) by positivity)]
    linarith

end FTAPTheorem42
