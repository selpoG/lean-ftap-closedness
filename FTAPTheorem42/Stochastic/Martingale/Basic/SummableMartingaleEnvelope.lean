/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Calculus.SemimartingaleStrategy
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! # Martingale laws under integrably dominated pointwise limits -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped NNReal

theorem Martingale.of_ae_tendsto_of_integrable_domination
    {Ω : Type*} [MeasurableSpace Ω]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [SigmaFiniteFiltration mu F]
    (M : Nat → Process Ω) (X : Process Ω)
    (hM : ∀ n, Martingale (M n) F mu) (hX : StronglyAdapted F X)
    (hlim : ∀ t, ∀ᵐ omega ∂mu,
      Tendsto (fun n => M n t omega) atTop (𝓝 (X t omega)))
    (B : Process Ω) (hB : ∀ t, Integrable (B t) mu)
    (hBound : ∀ n t, ∀ᵐ omega ∂mu, ‖M n t omega‖ ≤ B t omega) :
    Martingale X F mu := by
  have hInt : ∀ t, Integrable (X t) mu := by
    intro t
    apply (hB t).mono' ((hX t).mono (F.le t)).aestronglyMeasurable
    filter_upwards [hlim t, ae_all_iff.mpr (fun n => hBound n t)] with omega hLim hBounds
    exact le_of_tendsto hLim.norm (Eventually.of_forall hBounds)
  have hSetLimit (t : NNReal) (s : Set Ω) :
      Tendsto (fun n => ∫ omega in s, M n t omega ∂mu) atTop
        (𝓝 (∫ omega in s, X t omega ∂mu)) :=
    tendsto_integral_of_dominated_convergence (B t)
      (fun n => ((hM n).integrable t).aestronglyMeasurable.restrict)
      (hB t).integrableOn (fun n => ae_restrict_of_ae (hBound n t))
      (ae_restrict_of_ae (hlim t))
  refine ⟨hX, fun i j hij => ?_⟩
  apply EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (F.le i) (hInt j)
  · exact fun _ _ _ => (hInt i).integrableOn
  · intro s hs _
    exact tendsto_nhds_unique (hSetLimit i s)
      ((hSetLimit j s).congr' (Eventually.of_forall fun n =>
        ((hM n).setIntegral_eq hij hs).symm))
  · exact (hX i).aestronglyMeasurable

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## Martingale series dominated by summable integrable envelopes -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

theorem ae_summable_of_summable_envelope_integrals
    {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} (g : Nat → Ω → Real)
    (hg : ∀ k, Measurable (g k)) (hNonneg : ∀ k w, 0 ≤ g k w)
    (hSum : (∑' k, ∫⁻ w, ENNReal.ofReal (g k w) ∂mu) ≠ ∞) :
    ∀ᵐ w ∂mu, Summable (fun k => g k w) := by
  have hInt : (∫⁻ w, ∑' k, ENNReal.ofReal (g k w) ∂mu) ≠ ∞ := by
    rw [lintegral_tsum (fun k => (hg k).ennreal_ofReal.aemeasurable)]
    exact hSum
  filter_upwards [ae_lt_top (Measurable.tsum (fun k => (hg k).ennreal_ofReal)) hInt] with w hw
  simpa only [ENNReal.toReal_ofReal (hNonneg _ _)] using ENNReal.summable_toReal hw.ne

theorem ae_uniform_series_of_summable_envelopes
    {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω}
    (M : Nat → Process Ω) (g : Nat → Ω → Real)
    (hg : ∀ k, Measurable (g k)) (hNonneg : ∀ k w, 0 ≤ g k w)
    (hBound : ∀ k w t, |M k t w| ≤ g k w)
    (hSum : (∑' k, ∫⁻ w, ENNReal.ofReal (g k w) ∂mu) ≠ ∞) :
    ∀ᵐ w ∂mu, TendstoUniformly (fun n t => ∑ k ∈ Finset.range n, M k t w)
      (fun t => ∑' k, M k t w) atTop := by
  filter_upwards [ae_summable_of_summable_envelope_integrals g hg hNonneg hSum] with w hw
  exact tendstoUniformly_tsum_nat hw (fun k t => by
    simpa only [Real.norm_eq_abs] using hBound k w t)

theorem martingale_tsum_of_summable_envelopes
    {Ω : Type*} [MeasurableSpace Ω]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
    [SigmaFiniteFiltration mu F] (M : Nat → Process Ω) (g : Nat → Ω → Real)
    (hM : ∀ k, Martingale (M k) F mu) (hg : ∀ k, Measurable (g k))
    (hNonneg : ∀ k w, 0 ≤ g k w)
    (hBound : ∀ k w t, |M k t w| ≤ g k w)
    (hSum : (∑' k, ∫⁻ w, ENNReal.ofReal (g k w) ∂mu) ≠ ∞) :
    Martingale (fun t w => ∑' k, M k t w) F mu := by
  let B : Ω → ENNReal := fun w => ∑' k, ENNReal.ofReal (g k w)
  have hBMeas : Measurable B := Measurable.tsum (fun k => (hg k).ennreal_ofReal)
  have hBInt : (∫⁻ w, B w ∂mu) ≠ ∞ := by
    rw [lintegral_tsum (fun k => (hg k).ennreal_ofReal.aemeasurable)]
    exact hSum
  have hGSum := ae_summable_of_summable_envelope_integrals g hg hNonneg hSum
  have hNormSum : ∀ᵐ w ∂mu, ∀ t, Summable (fun k => ‖M k t w‖) := by
    filter_upwards [hGSum] with w hw
    intro t
    exact hw.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => by
      simpa only [Real.norm_eq_abs] using hBound k w t)
  let P : Nat → Process Ω := fun n t w => ∑ k ∈ Finset.range n, M k t w
  have hP : ∀ n, Martingale (P n) F mu := by
    intro n
    induction n with
    | zero =>
      change Martingale (0 : Process Ω) F mu
      exact martingale_zero Real F mu
    | succ n ih =>
      have hEq : P (n + 1) = P n + M n := by
        funext t w
        exact Finset.sum_range_succ _ _
      rw [hEq]
      exact ih.add (hM n)
  refine Martingale.of_ae_tendsto_of_integrable_domination P _ hP ?_ ?_
    (fun _ w => (B w).toReal) ?_ ?_
  · intro t
    have hMeas : ∀ k, @Measurable Ω Real (F t) _ (M k t) :=
      fun k => ((hM k).stronglyAdapted t).measurable
    let : MeasurableSpace Ω := F t
    exact (Measurable.tsum hMeas).stronglyMeasurable
  · intro t
    filter_upwards [hNormSum] with w hw
    exact (hw t).of_norm.tendsto_sum_tsum_nat
  · intro _
    exact integrable_toReal_of_lintegral_ne_top hBMeas.aemeasurable hBInt
  · intro n t
    filter_upwards [hGSum] with w hgSum
    have hPartial : ‖P n t w‖ ≤ ∑ k ∈ Finset.range n, g k w :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => by
        simpa only [Real.norm_eq_abs] using hBound k w t))
    have hEq : (B w).toReal = ∑' k, g k w := by
      rw [ENNReal.tsum_toReal_eq (fun k => ENNReal.ofReal_ne_top)]
      simp only [ENNReal.toReal_ofReal (hNonneg _ _)]
    rw [hEq]
    exact hPartial.trans (hgSum.sum_le_tsum _ (fun k _ => hNonneg k w))

end FTAPTheorem42
