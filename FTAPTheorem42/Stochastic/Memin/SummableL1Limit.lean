/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# `L¹` limits from summable successive differences

The local Mémín argument produces summable `L¹` sizes of successive
integrands.  This module records the analytic consequence needed to pass to
the stochastic-integral limit: the pointwise `limUnder` is integrable, the
original sequence converges to it almost everywhere, and the `L¹` distance
to it tends to zero.
-/

open Filter MeasureTheory Topology
open scoped BigOperators ENNReal

namespace FTAPTheorem42.MeminL1

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}

/-- Almost-everywhere convergence together with summable successive `L¹`
distances implies convergence to the same limit in `L¹`. -/
theorem lintegral_edist_tendsto_zero_of_summable_steps
    (f : ℕ → α → ℝ) (limit : α → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) ν)
    (hSteps : (∑' k, ∫⁻ x, edist (f (k + 1) x) (f k x) ∂ν) ≠ ∞)
    (hTendsto : ∀ᵐ x ∂ν,
      Tendsto (fun n => f n x) atTop (𝓝 (limit x))) :
    Tendsto (fun n => ∫⁻ x, edist (f n x) (limit x) ∂ν)
      atTop (𝓝 0) := by
  let step : ℕ → α → ℝ≥0∞ := fun k x =>
    edist (f (k + 1) x) (f k x)
  let bound : α → ℝ≥0∞ := fun x => ∑' k, step k x
  have hStepMeasurable : ∀ k, AEMeasurable (step k) ν := by
    intro k
    exact (hf (k + 1)).edist (hf k)
  have hBoundFinite : (∫⁻ x, bound x ∂ν) ≠ ∞ := by
    rw [lintegral_tsum hStepMeasurable]
    exact hSteps
  have hLimitMeasurable : AEStronglyMeasurable limit ν :=
    aestronglyMeasurable_of_tendsto_ae atTop hf hTendsto
  have hDifferenceMeasurable : ∀ n,
      AEMeasurable (fun x => edist (f n x) (limit x)) ν := by
    intro n
    exact (hf n).edist hLimitMeasurable
  have hDifferenceBound : ∀ n, ∀ᵐ x ∂ν,
      edist (f n x) (limit x) ≤ bound x := by
    intro n
    filter_upwards [hTendsto] with x hx
    calc
      edist (f n x) (limit x) ≤ ∑' m, step (n + m) x := by
        apply edist_le_tsum_of_edist_le_of_tendsto (f := fun k => f k x) (fun k => step k x)
        · intro k
          simpa only [step, Nat.succ_eq_add_one, edist_comm] using
            (le_refl (edist (f k x) (f (k + 1) x)))
        · exact hx
      _ ≤ ∑' k, step k x :=
        ENNReal.tsum_comp_le_tsum_of_injective (add_right_injective n) (fun k => step k x)
      _ = bound x := rfl
  have hDifferenceTendsto : ∀ᵐ x ∂ν,
      Tendsto (fun n => edist (f n x) (limit x)) atTop (𝓝 0) := by
    filter_upwards [hTendsto] with x hx
    simpa using hx.edist
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => limit x)
        atTop (𝓝 (limit x)))
  simpa only [lintegral_zero] using
    tendsto_lintegral_of_dominated_convergence' bound
      hDifferenceMeasurable hDifferenceBound hBoundFinite
        hDifferenceTendsto

/-- If the first term is integrable, the almost-everywhere limit of a
sequence with summable successive `L¹` distances is integrable. -/
theorem integrable_limit_of_summable_steps
    (f : ℕ → α → ℝ) (limit : α → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) ν)
    (hf0 : Integrable (f 0) ν)
    (hSteps : (∑' k, ∫⁻ x, edist (f (k + 1) x) (f k x) ∂ν) ≠ ∞)
    (hTendsto : ∀ᵐ x ∂ν,
      Tendsto (fun n => f n x) atTop (𝓝 (limit x))) :
    Integrable limit ν := by
  let step : ℕ → α → ℝ≥0∞ := fun k x =>
    edist (f (k + 1) x) (f k x)
  let bound : α → ℝ≥0∞ := fun x => ∑' k, step k x
  have hStepMeasurable : ∀ k, AEMeasurable (step k) ν := by
    intro k
    exact (hf (k + 1)).edist (hf k)
  have hBoundFinite : (∫⁻ x, bound x ∂ν) ≠ ∞ := by
    rw [lintegral_tsum hStepMeasurable]
    exact hSteps
  have hLimitMeasurable : AEStronglyMeasurable limit ν :=
    aestronglyMeasurable_of_tendsto_ae atTop hf hTendsto
  have hDifferenceBound : ∀ᵐ x ∂ν,
      ‖f 0 x - limit x‖ₑ ≤ bound x := by
    filter_upwards [hTendsto] with x hx
    have h := edist_le_tsum_of_edist_le_of_tendsto₀
      (fun k => step k x) (fun k => by
        simpa only [step, Nat.succ_eq_add_one, edist_comm] using
          (le_refl (edist (f k x) (f (k + 1) x)))) hx
    simpa only [Real.enorm_eq_ofReal_abs, edist_dist, Real.dist_eq] using h
  have hDifferenceFinite : HasFiniteIntegral
      (fun x => f 0 x - limit x) ν := by
    rw [hasFiniteIntegral_iff_enorm, lt_top_iff_ne_top]
    exact ne_top_of_le_ne_top hBoundFinite
      (lintegral_mono_ae hDifferenceBound)
  have hDifferenceIntegrable : Integrable
      (fun x => f 0 x - limit x) ν :=
    ⟨(hf 0).sub hLimitMeasurable, hDifferenceFinite⟩
  apply (hf0.sub hDifferenceIntegrable).congr
  exact Eventually.of_forall fun x => by
    simp only [Pi.sub_apply]
    ring

/-- Summable successive `L¹` distances identify the pointwise `limUnder`,
make it integrable, and give `L¹` convergence to it. -/
theorem integrable_l1_limit_of_summable_steps
    (f : ℕ → α → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) ν)
    (hf0 : Integrable (f 0) ν)
    (hSteps : (∑' k, ∫⁻ x, edist (f (k + 1) x) (f k x) ∂ν) ≠ ∞) :
    let limit := fun x => limUnder atTop (fun n => f n x)
    Integrable limit ν ∧
      (∀ᵐ x ∂ν, Tendsto (fun n => f n x) atTop (𝓝 (limit x))) ∧
      Tendsto (fun n => ∫⁻ x, edist (f n x) (limit x) ∂ν)
        atTop (𝓝 0) := by
  let step : ℕ → α → ℝ≥0∞ := fun k x =>
    edist (f (k + 1) x) (f k x)
  let limit := fun x => limUnder atTop (fun n => f n x)
  have hStepMeasurable : ∀ k, AEMeasurable (step k) ν := by
    intro k
    exact (hf (k + 1)).edist (hf k)
  have hIntegral : (∫⁻ x, ∑' k, step k x ∂ν) ≠ ∞ := by
    rw [lintegral_tsum hStepMeasurable]
    exact hSteps
  have hFiniteAE : ∀ᵐ x ∂ν, (∑' k, step k x) < ∞ :=
    ae_lt_top' (AEMeasurable.tsum hStepMeasurable) hIntegral
  have hTendsto : ∀ᵐ x ∂ν,
      Tendsto (fun n => f n x) atTop (𝓝 (limit x)) := by
    filter_upwards [hFiniteAE] with x hx
    have hRealSummable : Summable fun k => (step k x).toReal :=
      ENNReal.summable_toReal hx.ne
    have hDistSummable : Summable fun k =>
        dist (f k x) (f (k + 1) x) := by
      simpa only [step, dist_edist, edist_comm] using hRealSummable
    exact (cauchySeq_of_summable_dist hDistSummable).tendsto_limUnder
  exact ⟨integrable_limit_of_summable_steps f limit hf hf0 hSteps hTendsto,
    hTendsto,
    lintegral_edist_tendsto_zero_of_summable_steps
      f limit hf hSteps hTendsto⟩

/-- The pointwise `limUnder` of a sequence with an `L¹` base point and
summable successive `L¹` distances belongs to `L¹`. -/
theorem memLp_one_limUnder_of_summable_steps
    (f : ℕ → α → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) ν)
    (hf0 : MemLp (f 0) 1 ν)
    (hSteps : (∑' k, ∫⁻ x, edist (f (k + 1) x) (f k x) ∂ν) ≠ ∞) :
    MemLp (fun x => limUnder atTop (fun n => f n x)) 1 ν := by
  apply memLp_one_iff_integrable.mpr
  exact (integrable_l1_limit_of_summable_steps f hf
    (memLp_one_iff_integrable.mp hf0) hSteps).1

end FTAPTheorem42.MeminL1
