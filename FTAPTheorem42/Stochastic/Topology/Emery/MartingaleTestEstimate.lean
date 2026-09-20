/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Elementary.MartingaleGoodIntegrator
import FTAPTheorem42.Stochastic.Topology.Emery.ProcessCauchy

/-! # A uniform elementary-test estimate from terminal martingale energy

The bound depends on the represented test integrand, not its elementary
presentation. Thus the same tail works for all tests in the Emery topology.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

open FactorialChronologicalGrid

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

omit [MeasurableSpace Ω] in
private theorem cappedEnvelope_stopped_const (X : Process Ω) (T : NNReal) :
    cappedFiniteHorizonAbsoluteEnvelope
      (stoppedProcess X (fun _ : Ω => (T : WithTop NNReal))) T =
      cappedFiniteHorizonAbsoluteEnvelope X T := by
  funext ω
  unfold cappedFiniteHorizonAbsoluteEnvelope
  congr 2
  apply iSup_congr
  intro r
  congr 1
  unfold factorialRunningMax
  apply Finset.sup'_congr
  · rfl
  intro k hk
  simp only [ChronologicalGrid.natSample, stoppedProcess_const_apply]
  congr 1
  simp only [ChronologicalGrid.sampledTime, stoppedGrid_time,
    min_eq_left (min_le_right _ _)]

omit [SigmaFiniteFiltration μ F] in
private theorem cappedEnvelope_eLpNorm_two_le {X : Process Ω}
    (hX : Martingale X F μ) (T : NNReal) (hXT : MemLp (X T) 2 μ) :
    eLpNorm (cappedFiniteHorizonAbsoluteEnvelope X T) 2 μ ≤ 2 * eLpNorm (X T) 2 μ := by
  have hFinite := Martingale.eFactorialRunningMaxSqEnvelope_abs_ae_lt_top hX T hXT
  have hBound : ∀ᵐ ω ∂μ, ‖cappedFiniteHorizonAbsoluteEnvelope X T ω‖ ≤
      ‖martingaleAbsoluteEnvelope X T ω‖ := by
    filter_upwards [hFinite] with ω hω
    have h := cappedFiniteHorizonAbsoluteEnvelope_le_of_sq_ne_top X T ω hω.ne
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (cappedFiniteHorizonAbsoluteEnvelope_nonneg X T ω),
      abs_of_nonneg (Real.sqrt_nonneg _),
      finiteHorizonAbsoluteEnvelope, martingaleAbsoluteEnvelope] using h
  exact (eLpNorm_mono_ae
    ((stronglyMeasurable_cappedFiniteHorizonAbsoluteEnvelope hX.stronglyAdapted T).mono
      (F.le T)).aestronglyMeasurable hBound).trans
    (Martingale.eLpNorm_martingaleAbsoluteEnvelope_le_two_mul hX T hXT)

/-- Every unit-bounded elementary test has capped maximal expectation at most
twice the terminal L² norm of the zero-initial source martingale. -/
theorem martingale_test_integral_le {M : Process Ω}
    (hM : Martingale M F μ)
    (hRight : ∀ ω t, ContinuousWithinAt (M · ω) (Ici t) t)
    (hZero : M 0 =ᵐ[μ] 0) (T : NNReal) (hMT : MemLp (M T) 2 μ)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) F) :
    ENNReal.ofReal (∫ ω, cappedFiniteHorizonAbsoluteEnvelope
      (ElementaryStrategy.gain M J.strategy.toElementary) T ω ∂μ) ≤
      2 * eLpNorm (M T) 2 μ := by
  let X := ElementaryStrategy.gain M J.strategy.toElementary
  let Z := stoppedProcess X (fun _ : Ω => (T : WithTop NNReal))
  have hZ : Martingale Z F μ :=
    J.strategy.stoppedGain_isMartingale_of_integrand_bound hM hRight T hMT
      zero_le_one J.abs_integrand_le_one
  have hEnergy : (∫ ω, (M T ω - M 0 ω) ^ 2 ∂μ) = ∫ ω, ‖M T ω‖ ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hZero] with ω hω
    simp only [hω, Pi.zero_apply, sub_zero, Real.norm_eq_abs, sq_abs]
  have hNorm : eLpNorm (X T) 2 μ ≤ eLpNorm (M T) 2 μ := by
    have h := J.strategy.eLpNorm_gain_le_integrand_bound hM hRight T hMT
      zero_le_one J.abs_integrand_le_one
    rwa [one_mul, hEnergy, ← eLpNorm_two_toReal_eq_sqrt_integral_norm_sq hMT,
      ENNReal.ofReal_toReal hMT.eLpNorm_ne_top] at h
  have hZT : Z T = X T := by
    funext ω
    simp only [Z, stoppedProcess_const_apply, min_self]
  have hZMem : MemLp (Z T) 2 μ :=
    by rw [hZT]; exact hNorm.trans_lt hMT.eLpNorm_lt_top
  let C := cappedFiniteHorizonAbsoluteEnvelope X T
  have hMeas : StronglyMeasurable C := by
    dsimp only [C]
    rw [← cappedEnvelope_stopped_const X T]
    exact (stronglyMeasurable_cappedFiniteHorizonAbsoluteEnvelope hZ.stronglyAdapted T).mono
      (F.le T)
  have hInt : Integrable C μ := Integrable.of_bound hMeas.aestronglyMeasurable 1
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (cappedFiniteHorizonAbsoluteEnvelope_nonneg X T ω)]
      exact cappedFiniteHorizonAbsoluteEnvelope_le_one X T ω)
  have hIntegral : ENNReal.ofReal (∫ ω, C ω ∂μ) = eLpNorm C 1 μ := by
    rw [ofReal_integral_eq_lintegral_ofReal hInt
      (Eventually.of_forall (cappedFiniteHorizonAbsoluteEnvelope_nonneg X T)),
      eLpNorm_one_eq_lintegral_enorm hMeas.aestronglyMeasurable]
    apply lintegral_congr
    intro ω
    rw [Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (cappedFiniteHorizonAbsoluteEnvelope_nonneg X T ω)]
  change ENNReal.ofReal (∫ ω, C ω ∂μ) ≤ _
  rw [hIntegral]
  apply (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ENNReal) ≤ 2)).trans
  have hCap := cappedEnvelope_eLpNorm_two_le hZ T hZMem
  rw [cappedEnvelope_stopped_const X T, hZT] at hCap
  exact hCap.trans (mul_le_mul le_rfl hNorm bot_le bot_le)

/-- Vanishing terminal L² norms supply uniform elementary-test convergence.
No bounds on test length or coefficient sums are used. -/
theorem elementaryEmeryConverges_zero_of_martingale_L2
    {M : Nat → Process Ω} (hM : ∀ n, Martingale (M n) F μ)
    (hRight : ∀ n ω t, ContinuousWithinAt (M n · ω) (Ici t) t)
    (hZero : ∀ n, M n 0 =ᵐ[μ] 0)
    (hMem : ∀ n T, MemLp (M n T) 2 μ)
    (hNorm : ∀ T, Tendsto (fun n => eLpNorm (M n T) 2 μ) atTop (𝓝 0)) :
    ElementaryEmeryConverges μ F M 0 := by
  intro T ε hε
  have hLim : Tendsto (fun n => 2 * eLpNorm (M n T) 2 μ) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul (hNorm T)
      (Or.inr (by norm_num : (2 : ENNReal) ≠ ∞))
  filter_upwards [hLim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hε))] with n hn
  intro J
  have h := (martingale_test_integral_le (hM n) (hRight n) (hZero n) T (hMem n T) J).trans hn.le
  have hReal := (ENNReal.ofReal_le_ofReal_iff hε.le).mp h
  have hZeroGain : ElementaryStrategy.gain (0 : Process Ω) J.strategy.toElementary = 0 := by
    funext t ω
    simp [ElementaryStrategy.gain, ElementaryInterval.gain]
  simpa only [hZeroGain, Pi.zero_apply, sub_zero] using hReal

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## Finite terminal energy controls all earlier elementary tests -/

open Filter MeasureTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

/-- A finite terminal L² representative controls every earlier horizon,
uniformly over all represented unit-bounded elementary tests. -/
theorem integral_martingale_testError_le_terminal_norm {M : Process Ω}
    (hM : Martingale M F μ)
    (hRight : ∀ ω t, ContinuousWithinAt (M · ω) (Ici t) t)
    (hZero : M 0 =ᵐ[μ] 0) (T U : NNReal) (hTU : T ≤ U)
    (z : Lp Real 2 μ) (hz : ⇑z =ᵐ[μ] M U)
    (J : BoundedPredictableElementaryMultiplier (Ω := Ω) F) :
    (∫ ω, elementaryEmeryTestError M 0 J T ω ∂μ) ≤ 2 * ‖z‖ := by
  have hU : MemLp (M U) 2 μ := MemLp.ae_eq hz (Lp.memLp z)
  have hT : MemLp (M T) 2 μ := MemLp.ae_eq (hM.condExp_ae_eq hTU)
    (hU.condExp (by norm_num))
  have hNorm : eLpNorm (M T) 2 μ ≤ eLpNorm (M U) 2 μ := by
    rw [← eLpNorm_congr_ae (hM.condExp_ae_eq hTU)]
    exact eLpNorm_condExp_le_eLpNorm _ (by norm_num)
  have h := (martingale_test_integral_le hM hRight hZero T hT J).trans
    (mul_le_mul le_rfl hNorm bot_le bot_le)
  have hzNorm : eLpNorm z 2 μ = ENNReal.ofReal ‖z‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top z)]
  rw [← eLpNorm_congr_ae hz, hzNorm] at h
  have hReal : (∫ ω, FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
      (ElementaryStrategy.gain M J.strategy.toElementary) T ω ∂μ) ≤ 2 * ‖z‖ := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 2),
      ENNReal.ofReal_ofNat] using h
  have hZeroGain : ElementaryStrategy.gain (0 : Process Ω) J.strategy.toElementary = 0 := by
    funext t ω
    simp [ElementaryStrategy.gain, ElementaryInterval.gain]
  simpa only [elementaryEmeryTestError, hZeroGain, Pi.zero_apply, sub_zero] using hReal

/-- Terminal L² Cauchy estimates control all tests on earlier horizons.
The sequence cutoff is independent of both the horizon and the test. -/
theorem martingale_testError_cauchy_of_terminal_L2
    {M : Nat → Process Ω} (hM : ∀ n, Martingale (M n) F μ)
    (hRight : ∀ n ω t, ContinuousWithinAt (M n · ω) (Ici t) t)
    (hZero : ∀ n, M n 0 =ᵐ[μ] 0) (U : NNReal)
    (Z : Nat → Lp Real 2 μ) (hZ : ∀ n, ⇑(Z n) =ᵐ[μ] M n U)
    (hCauchy : CauchySeq Z) :
    ∀ ε : Real, 0 < ε → ∃ N : Nat, ∀ n, N ≤ n → ∀ k, N ≤ k →
      ∀ T : NNReal, T ≤ U → ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
        (∫ ω, elementaryEmeryTestError (M n) (M k) J T ω ∂μ) ≤ ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hCauchy (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn k hk T hTU J => ?_⟩
  have hDiffZero : (M n - M k) 0 =ᵐ[μ] 0 := by
    filter_upwards [hZero n, hZero k] with ω hn hk
    simp only [Pi.sub_apply, hn, hk, Pi.zero_apply, sub_zero]
  have hDiffTerminal : ⇑(Z n - Z k) =ᵐ[μ] (M n - M k) U := by
    filter_upwards [Lp.coeFn_sub (Z n) (Z k), hZ n, hZ k] with ω hSub hn hk
    simpa only [Pi.sub_apply, hn, hk] using hSub
  have h := integral_martingale_testError_le_terminal_norm ((hM n).sub (hM k))
    (fun ω t => (hRight n ω t).sub (hRight k ω t)) hDiffZero T U hTU
    (Z n - Z k) hDiffTerminal J
  have hEq : elementaryEmeryTestError (M n - M k) 0 J T =
      elementaryEmeryTestError (M n) (M k) J T := by
    unfold elementaryEmeryTestError
    congr 1
    have hSub := PredictableElementaryEmery.elementaryGain_source_sub (M n) (M k) J.strategy
    have hZeroGain : ElementaryStrategy.gain (0 : Process Ω) J.strategy.toElementary = 0 := by
      funext t ω
      simp [ElementaryStrategy.gain, ElementaryInterval.gain]
    simp only [hZeroGain, Pi.zero_apply, sub_zero]
    funext t ω
    exact congrFun (congrFun hSub t) ω
  rw [hEq] at h
  have hDist := hN n hn k hk
  rw [dist_eq_norm] at hDist
  linarith only [h, hDist]

end FTAPTheorem42
