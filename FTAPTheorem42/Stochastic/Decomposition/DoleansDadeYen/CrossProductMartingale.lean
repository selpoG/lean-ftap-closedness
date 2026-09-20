/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.DoleansDadeYen.SquareIntegralMartingale
import FTAPTheorem42.Stochastic.Integral.Elementary.StoppedFiniteGridIntegral

/-! # The DDY cross-product correction as a dominated martingale limit -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} {X : Process Ω} {c : Real}

noncomputable def DoleansDadeYenData.crossProductCorrection
    (d : DoleansDadeYenData X F mu c) : Process Ω := fun t omega =>
  d.L t omega * d.Q t omega -
    ∑' s : Ioc (0 : NNReal) t, processLeftJump d.L s omega * processLeftJump d.Q s omega

theorem DoleansDadeYenData.tendsto_stopped_crossProductCorrection
    (d : DoleansDadeYenData X F mu c) (tau : Ω → NNReal) (t : NNReal) (omega : Ω) :
    let L := stoppedProcess d.L (fun w => (tau w : WithTop NNReal))
    let Q := stoppedProcess d.Q (fun w => (tau w : WithTop NNReal))
    Tendsto (fun r =>
      (FactorialChronologicalGrid.grid (r + 1)).martingaleIntegralProcess L Q t omega +
      (FactorialChronologicalGrid.grid (r + 1)).martingaleIntegralProcess Q L t omega) atTop
      (𝓝 (stoppedProcess d.crossProductCorrection
        (fun w => (tau w : WithTop NNReal)) t omega)) := by
  intro L Q
  have hBV : ∀ w, LocallyBoundedVariationOn (Q · w) univ := by
    intro w
    have h := (FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn
      (d.Q_locallyBoundedVariation w) (tau w)).locallyBoundedVariationOn
    change LocallyBoundedVariationOn (fun s => d.Q (min s (tau w)) w) univ at h
    simpa only [Q, BoundedMartingaleQuadraticKernel.Data.stoppedProcess_coe_apply] using h
  have hLRight : ∀ w s, ContinuousWithinAt (L · w) (Ici s) s :=
    RightContinuousStoppedMartingale.stoppedProcess_rightContinuous d.L d.L_rightContinuous
  have hQRight : ∀ w s, ContinuousWithinAt (Q · w) (Ici s) s :=
    RightContinuousStoppedMartingale.stoppedProcess_rightContinuous d.Q d.Q_rightContinuous
  have hLLeft : ProcessHasLeftLimits L := d.L_leftLimits.stoppedProcess _
  have hQLeft : ProcessHasLeftLimits Q := d.Q_leftLimits.stoppedProcess _
  have hCross := FactorialChronologicalGrid.tendsto_crossIncrementProcess_stieltjes L Q omega
    (hLRight omega) (hLLeft omega) (hBV omega) (hQRight omega) t
  change Tendsto _ atTop (𝓝 (∫ᵛ s in Ioc (0 : NNReal) t, processLeftJump L s omega
    ∂•(FiniteVariationPath.signedMeasure
      (FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn
        (hBV omega) t)))) at hCross
  rw [setIntegral_processLeftJump_eq_tsum L Q hLRight hLLeft hQRight hQLeft hBV] at hCross
  have hSum := tsum_stopped_jump_eq d.L d.Q d.L_leftLimits d.Q_leftLimits
    (fun x y => x * y) (by norm_num) tau t omega
  change (∑' s : Ioc (0 : NNReal) t,
    processLeftJump L s omega * processLeftJump Q s omega) = _ at hSum
  rw [hSum] at hCross
  have hLim := hCross.const_sub (L t omega * Q t omega)
  apply hLim.congr'
  filter_upwards [eventually_ge_atTop (Nat.ceil t)] with r hr
  have ht : t ≤ (r + 1 : Nat) :=
    (Nat.le_ceil t).trans (by exact_mod_cast hr.trans (Nat.le_succ r))
  have hLast : (FactorialChronologicalGrid.grid (r + 1)).sampledTime
      ((r + 1) * (r + 1).factorial) = (r + 1 : Nat) := by
    simp only [ChronologicalGrid.sampledTime, ChronologicalGrid.natIndex,
      FactorialChronologicalGrid.grid, min_self, Nat.cast_mul]
    exact mul_div_cancel_right₀ _ (by exact_mod_cast Nat.factorial_ne_zero (r + 1))
  have hFirst : (FactorialChronologicalGrid.grid (r + 1)).sampledTime 0 = 0 := by
    simp [ChronologicalGrid.sampledTime, ChronologicalGrid.natIndex,
      FactorialChronologicalGrid.grid]
  rw [(FactorialChronologicalGrid.grid (r + 1)).product_decomposition, hLast, hFirst,
    min_eq_left ht, min_eq_right (show (0 : NNReal) ≤ t from bot_le)]
  have hZero : Q 0 omega = 0 := by
    change stoppedProcess d.Q (fun w => (tau w : WithTop NNReal)) 0 omega = 0
    rw [BoundedMartingaleQuadraticKernel.Data.stoppedProcess_coe_apply,
      min_eq_left (show (0 : NNReal) ≤ tau omega from bot_le), d.Q_zero, Pi.zero_apply]
  rw [hZero, mul_zero, sub_zero]

theorem DoleansDadeYenL1Localization.crossProductCorrection_stopped_martingale
    [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
    {d : DoleansDadeYenData X F mu c} (R : DoleansDadeYenL1Localization d)
    (hc : 0 ≤ c) (n : Nat) :
    Martingale (stoppedProcess d.crossProductCorrection
      (fun w => (R.tau n w : WithTop NNReal))) F mu := by
  let L := stoppedProcess d.L (fun w => (R.tau n w : WithTop NNReal))
  let Q := stoppedProcess d.Q (fun w => (R.tau n w : WithTop NNReal))
  let M : Nat → Process Ω := fun r t omega =>
    (FactorialChronologicalGrid.grid (r + 1)).martingaleIntegralProcess L Q t omega +
      (FactorialChronologicalGrid.grid (r + 1)).martingaleIntegralProcess Q L t omega
  have hM : ∀ r, Martingale (M r) F mu := by
    intro r
    have h := R.grid_martingales n _ (FactorialChronologicalGrid.grid (r + 1))
    exact h.2.2.add h.2.1
  have hLim := d.tendsto_stopped_crossProductCorrection (R.tau n)
  apply Martingale.of_ae_tendsto_of_integrable_domination M _ hM
  · intro t
    apply stronglyMeasurable_of_tendsto atTop (fun r => (hM r).stronglyMeasurable t)
    rw [tendsto_pi_nhds]
    exact hLim t
  · exact fun t => Eventually.of_forall (hLim t)
  · exact fun _ => (R.variation_integrable n).const_mul (3 * (cadlagPassageLevel n + 2 * c))
  · intro r t
    filter_upwards [R.L_bound n] with omega hL
    have hBV : ∀ w, LocallyBoundedVariationOn (Q · w) univ := by
      intro w
      have h := (FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn
        (d.Q_locallyBoundedVariation w) (R.tau n w)).locallyBoundedVariationOn
      change LocallyBoundedVariationOn (fun s => d.Q (min s (R.tau n w)) w) univ at h
      simpa only [Q, BoundedMartingaleQuadraticKernel.Data.stoppedProcess_coe_apply] using h
    have hZero : Q 0 = 0 := by
      funext w
      change stoppedProcess d.Q (fun w => (R.tau n w : WithTop NNReal)) 0 w = 0
      rw [BoundedMartingaleQuadraticKernel.Data.stoppedProcess_coe_apply,
        min_eq_left (show (0 : NNReal) ≤ R.tau n w from bot_le), d.Q_zero, Pi.zero_apply]
    have hFirst : (FactorialChronologicalGrid.grid (r + 1)).sampledTime 0 = 0 := by
      simp [ChronologicalGrid.sampledTime, ChronologicalGrid.natIndex,
        FactorialChronologicalGrid.grid]
    have hb : 0 ≤ cadlagPassageLevel n + 2 * c :=
      add_nonneg (cadlagPassageLevel_nonnegative n) (mul_nonneg (by norm_num) hc)
    rw [Real.norm_eq_abs]
    exact ((FactorialChronologicalGrid.grid (r + 1)).abs_product_integrals_le_three_mul_variation
      L Q omega hBV hZero hFirst hb hL t).trans
        (mul_le_mul_of_nonneg_left (R.variation_bound n omega t) (mul_nonneg (by norm_num) hb))

theorem DoleansDadeYenData.crossProductCorrection_isLocalMartingale
    [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] [F.IsRightContinuous]
    (d : DoleansDadeYenData X F mu c) (hc : 0 ≤ c) :
    LocalMartingale d.crossProductCorrection F mu := by
  obtain ⟨R⟩ := d.exists_common_localizer_integrableVariation hc
  apply LocalMartingale.of_closed_stops_of_zero
    (tau := fun n w => (R.tau n w : WithTop NNReal))
  · funext omega
    simp [crossProductCorrection, d.Q_zero]
  · exact R.isLocalizingSequence
  · exact R.crossProductCorrection_stopped_martingale hc

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## The original square residual for the same regularized DDY variation -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  [F.IsRightContinuous] {X : Process Ω} {c : Real}

theorem DoleansDadeYenData.corrected_squareResidual_isLocalMartingale
    (d : DoleansDadeYenData X F mu c) (hc : 0 ≤ c)
    (C : LocalMartingaleQuadratic.LocalMartingaleQuadraticSchedule
      (F := F) (mu := mu) (M := d.L))
    (QC : LocalMartingaleQuadratic.GluedQuadraticVariationCertificate C)
    {V : Process Ω} (hVAdapted : StronglyAdapted F V)
    (hVRight : ∀ omega t, ContinuousWithinAt (V · omega) (Ici t) t)
    (hV : ProcessIndistinguishable mu V
      (fun t omega => QC.variation t omega + d.quadraticCorrection t omega)) :
    LocalMartingale (fun t omega => X t omega ^ 2 - V t omega) F mu := by
  obtain ⟨R⟩ := d.exists_common_localizer_integrableVariation hc
  let B : Process Ω := fun t omega =>
    d.crossProductCorrection t omega + d.finiteVariationSquareIntegral t omega
  have hB : LocalMartingale B F mu := by
    apply LocalMartingale.of_closed_stops_of_zero
      (tau := fun n w => (R.tau n w : WithTop NNReal))
    · funext omega
      simp [B, crossProductCorrection, finiteVariationSquareIntegral, d.Q_zero]
    · exact R.isLocalizingSequence
    · intro n
      have h := (R.crossProductCorrection_stopped_martingale hc n).add
        (R.squareIntegral_stopped_martingale n)
      convert h using 1
      funext t omega
      simp only [B, BoundedMartingaleQuadraticKernel.Data.stoppedProcess_coe_apply, Pi.add_apply]
  let U : Process Ω := fun t omega => X t omega ^ 2 - V t omega
  let Z : Process Ω := fun t omega => d.L t omega ^ 2 - QC.variation t omega
  have hXAdapted : StronglyAdapted F X := by
    rw [d.decomposition]
    exact d.L_isStronglyAdapted.add d.Q_isStronglyAdapted
  have hXRight : ∀ omega t, ContinuousWithinAt (X · omega) (Ici t) t := by
    rw [d.decomposition]
    exact fun omega t => (d.L_rightContinuous omega t).add (d.Q_rightContinuous omega t)
  have hUAdapted : StronglyAdapted F U := fun t => ((hXAdapted t).pow 2).sub (hVAdapted t)
  have hURight : ∀ omega t, ContinuousWithinAt (U · omega) (Ici t) t :=
    fun omega t => ((hXRight omega t).pow 2).sub (hVRight omega t)
  have hZAdapted : StronglyAdapted F Z := fun t =>
    ((d.L_isStronglyAdapted t).pow 2).sub (QC.variation_isStronglyAdapted t)
  have hZRight : ∀ omega t, ContinuousWithinAt (Z · omega) (Ici t) t :=
    fun omega t => ((d.L_rightContinuous omega t).pow 2).sub (QC.variation_rightContinuous omega t)
  have hReg : LocalMartingale (fun t omega => U t omega - Z t omega) F mu := by
    apply (hB.smul 2).congr_indistinguishable (hUAdapted.sub hZAdapted)
      (fun omega t => (hURight omega t).sub (hZRight omega t))
    filter_upwards [d.corrected_squareResidual_eq C QC hV] with omega hEq
    intro t
    have h := hEq t
    change U t omega = Z t omega + 2 * B t omega at h
    change 2 * B t omega = U t omega - Z t omega
    linarith
  have hZ : LocalMartingale Z F mu := by
    simpa only [d.L_zero, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), sub_zero] using
      QC.squareResidual_isLocalMartingale
  have hSum := hZ.add_of_rightContinuous hReg hZRight
    (fun omega t => (hURight omega t).sub (hZRight omega t))
  apply hSum.congr_indistinguishable hUAdapted hURight
  exact Eventually.of_forall fun omega t => by dsimp only [Z]; ring

end FTAPTheorem42
