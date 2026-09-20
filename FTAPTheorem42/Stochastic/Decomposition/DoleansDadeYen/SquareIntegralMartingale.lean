/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.DoleansDadeYen.CommonLocalization
import FTAPTheorem42.Stochastic.Decomposition.DoleansDadeYen.CorrectionStopping
import FTAPTheorem42.Stochastic.Martingale.Basic.SummableMartingaleEnvelope

/-! # Stieltjes reduction of the original DDY square residual -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} {X : Process Ω} {c : Real}

/-- The concrete pathwise integral of the left limit against the same
finite-variation DDY component. The measure is stopped at the evaluation horizon. -/
noncomputable def DoleansDadeYenData.finiteVariationSquareIntegral
    (d : DoleansDadeYenData X F mu c) : Process Ω := fun t omega =>
  ∫ᵛ s in Ioc (0 : NNReal) t, Function.leftLim (d.Q · omega) s
    ∂•(FiniteVariationPath.signedMeasure
      (FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn
        (d.Q_locallyBoundedVariation omega) t))

/-- Reduce the original square residual to the bounded-jump residual,
the cross-product correction, and an actual Stieltjes integral.
This is an algebraic identity; martingale properties of the correction
terms are established separately. -/
theorem DoleansDadeYenData.corrected_squareResidual_eq
    (d : DoleansDadeYenData X F mu c)
    (C : LocalMartingaleQuadratic.LocalMartingaleQuadraticSchedule
      (F := F) (mu := mu) (M := d.L))
    (QC : LocalMartingaleQuadratic.GluedQuadraticVariationCertificate C)
    {V : Process Ω} (hV : ProcessIndistinguishable mu V
      (fun t omega => QC.variation t omega + d.quadraticCorrection t omega)) :
    ∀ᵐ omega ∂mu, ∀ t,
      X t omega ^ 2 - V t omega =
        (d.L t omega ^ 2 - QC.variation t omega) +
          2 * (d.L t omega * d.Q t omega -
            (∑' s : Ioc (0 : NNReal) t,
              processLeftJump d.L s omega * processLeftJump d.Q s omega) +
            d.finiteVariationSquareIntegral t omega) := by
  filter_upwards [hV] with omega hPath
  intro t
  have hQ := finiteVariation_squareResidual_eq_stieltjes d.Q d.Q_rightContinuous
    d.Q_leftLimits d.Q_locallyBoundedVariation t omega
  have hQZero : d.Q 0 omega = 0 := congrFun d.Q_zero omega
  change d.Q t omega ^ 2 - d.Q 0 omega ^ 2 -
    (∑' s : Ioc (0 : NNReal) t, (processLeftJump d.Q s omega) ^ 2) =
      2 * d.finiteVariationSquareIntegral t omega at hQ
  rw [hQZero, zero_pow (by decide : 2 ≠ 0), sub_zero] at hQ
  have hX : X t omega = d.L t omega + d.Q t omega :=
    congrFun (congrFun d.decomposition t) omega
  rw [hPath t, hX]
  dsimp only [quadraticCorrection]
  nlinarith [hQ]

/-! ## The DDY finite-variation square integral under common localization -/

theorem DoleansDadeYenData.tendsto_stopped_squareIntegral
    (d : DoleansDadeYenData X F mu c) (tau : Ω → NNReal) (t : NNReal) (omega : Ω) :
    Tendsto (fun r => (FactorialChronologicalGrid.grid (r + 1)).martingaleIntegralProcess
      (stoppedProcess d.Q (fun w => (tau w : WithTop NNReal)))
      (stoppedProcess d.Q (fun w => (tau w : WithTop NNReal))) t omega) atTop
      (𝓝 (stoppedProcess d.finiteVariationSquareIntegral
        (fun w => (tau w : WithTop NNReal)) t omega)) := by
  let Q := stoppedProcess d.Q (fun w => (tau w : WithTop NNReal))
  have hBV : ∀ w, LocallyBoundedVariationOn (Q · w) univ := by
    intro w
    have h := (FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn
      (d.Q_locallyBoundedVariation w) (tau w)).locallyBoundedVariationOn
    change LocallyBoundedVariationOn (fun s => d.Q (min s (tau w)) w) univ at h
    simpa only [Q, BoundedMartingaleQuadraticKernel.Data.stoppedProcess_coe_apply] using h
  have hRight : ∀ w s, ContinuousWithinAt (Q · w) (Ici s) s :=
    RightContinuousStoppedMartingale.stoppedProcess_rightContinuous d.Q d.Q_rightContinuous
  have hLeft : ProcessHasLeftLimits Q := d.Q_leftLimits.stoppedProcess _
  have hLim := FactorialChronologicalGrid.tendsto_martingaleIntegralProcess_stieltjes Q Q omega
    (hRight omega) (hLeft omega) (hBV omega) (hRight omega) t
  have hSquare := finiteVariation_squareResidual_eq_stieltjes Q hRight hLeft hBV t omega
  have hOriginal := finiteVariation_squareResidual_eq_stieltjes d.Q d.Q_rightContinuous
    d.Q_leftLimits d.Q_locallyBoundedVariation (min t (tau omega)) omega
  have hSum := tsum_stopped_jump_eq d.Q d.Q d.Q_leftLimits d.Q_leftLimits
    (fun _ y => y ^ 2) (by norm_num) tau t omega
  change (∑' s : Ioc (0 : NNReal) t, (processLeftJump Q s omega) ^ 2) = _ at hSum
  rw [hSum] at hSquare
  rw [show Q t omega = d.Q (min t (tau omega)) omega from
    BoundedMartingaleQuadraticKernel.Data.stoppedProcess_coe_apply d.Q tau t omega,
    show Q 0 omega = d.Q 0 omega from by
      simp only [Q, BoundedMartingaleQuadraticKernel.Data.stoppedProcess_coe_apply,
        min_eq_left (show (0 : NNReal) ≤ tau omega from bot_le)]] at hSquare
  have hEq := (mul_left_cancel₀ (show (2 : Real) ≠ 0 by norm_num)
    (hSquare.symm.trans hOriginal))
  rw [hEq] at hLim
  simpa only [BoundedMartingaleQuadraticKernel.Data.stoppedProcess_coe_apply,
    finiteVariationSquareIntegral] using hLim

theorem DoleansDadeYenL1Localization.squareIntegral_stopped_martingale
    [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
    {d : DoleansDadeYenData X F mu c} (R : DoleansDadeYenL1Localization d) (n : Nat) :
    Martingale (stoppedProcess d.finiteVariationSquareIntegral
      (fun w => (R.tau n w : WithTop NNReal))) F mu := by
  let Q := stoppedProcess d.Q (fun w => (R.tau n w : WithTop NNReal))
  let M : Nat → Process Ω := fun r =>
    (FactorialChronologicalGrid.grid (r + 1)).martingaleIntegralProcess Q Q
  have hM : ∀ r, Martingale (M r) F mu := fun r =>
    (R.grid_martingales n _ (FactorialChronologicalGrid.grid (r + 1))).1
  have hLim := d.tendsto_stopped_squareIntegral (R.tau n)
  apply Martingale.of_ae_tendsto_of_integrable_domination M _ hM
  · intro t
    apply stronglyMeasurable_of_tendsto atTop (fun r => (hM r).stronglyMeasurable t)
    rw [tendsto_pi_nhds]
    exact hLim t
  · exact fun t => Eventually.of_forall (hLim t)
  · exact fun _ => (R.variation_integrable n).const_mul (cadlagPassageLevel n)
  · intro r t
    apply Eventually.of_forall
    intro omega
    have hBV : LocallyBoundedVariationOn (Q · omega) univ := by
      have h := (FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn
        (d.Q_locallyBoundedVariation omega) (R.tau n omega)).locallyBoundedVariationOn
      change LocallyBoundedVariationOn (fun s => d.Q (min s (R.tau n omega)) omega) univ at h
      simpa only [Q, BoundedMartingaleQuadraticKernel.Data.stoppedProcess_coe_apply] using h
    rw [Real.norm_eq_abs]
    exact (ChronologicalGrid.abs_martingaleIntegralProcess_stopped_le_variation
      (FactorialChronologicalGrid.grid (r + 1))
      d.Q d.Q (R.tau n) omega hBV (cadlagPassageLevel_nonnegative n)
      (R.Q_pre_bound n omega) t).trans
        (mul_le_mul_of_nonneg_left (R.variation_bound n omega t) (cadlagPassageLevel_nonnegative n))

theorem DoleansDadeYenData.finiteVariationSquareIntegral_isLocalMartingale
    [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] [F.IsRightContinuous]
    (d : DoleansDadeYenData X F mu c) (hc : 0 ≤ c) :
    LocalMartingale d.finiteVariationSquareIntegral F mu := by
  obtain ⟨R⟩ := d.exists_common_localizer_integrableVariation hc
  apply LocalMartingale.of_closed_stops_of_zero
    (tau := fun n w => (R.tau n w : WithTop NNReal))
  · funext omega
    simp [finiteVariationSquareIntegral]
  · exact R.isLocalizingSequence
  · exact R.squareIntegral_stopped_martingale

end FTAPTheorem42
