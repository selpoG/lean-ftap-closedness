/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.DoleansDadeYen.StoppedRootIdentification
import FTAPTheorem42.Stochastic.Decomposition.DoleansDadeYen.RootUniformIntegrability
import FTAPTheorem42.Stochastic.Martingale.Basic.MartingaleGridEnvelopeLimit

/-! # Continuous-time Davis estimates for the original common-stopped DDY source -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  [F.IsRightContinuous] {X : Process Ω} {c : Real}

theorem DoleansDadeYenL1Localization.source_continuous_davis
    {d : DoleansDadeYenData X F mu c} (R : DoleansDadeYenL1Localization d)
    (hUsual : Filtration.UsualConditions mu F)
    (hXR : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hXL : ProcessHasLeftLimits X)
    (C : LocalMartingaleQuadratic.LocalMartingaleQuadraticSchedule
      (F := F) (mu := mu) (M := d.L))
    (QC : LocalMartingaleQuadratic.GluedQuadraticVariationCertificate C)
    {V : Process Ω} (hV : ProcessIndistinguishable mu V
      (fun t w => QC.variation t w + d.quadraticCorrection t w))
    (n : Nat) (T : NNReal) :
    let Y := stoppedProcess X (fun w => (R.tau n w : WithTop NNReal))
    let Z := fun w => Real.sqrt (V (min T (R.tau n w)) w)
    Integrable Z mu ∧
    Integrable (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope Y T) mu ∧
    (∫ w, FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope Y T w ∂mu) ≤
      6 * ∫ w, Z w ∂mu := by
  let Y := stoppedProcess X (fun w => (R.tau n w : WithTop NNReal))
  let Z := fun w => Real.sqrt (V (min T (R.tau n w)) w)
  obtain ⟨D, hInt, hLimit⟩ := R.exists_original_root_tendsto_L1 hUsual hXR C QC hV n T
  let f := fun k w => Real.sqrt
    (BoundedMartingaleQuadraticConvexification.squaredIncrementPart
      Y T (D.weights (D.cutoff k)) T w)
  let W := TailConvexWeights.toForwardReindex D.cutoff D.cutoff_strictMono D.weights
  have hUI : UniformIntegrable f 1 mu := by
    have h := R.source_convex_root_uniformIntegrable hXR n T W
    simpa only [W, f, Y, TailConvexWeights.toForwardReindex_apply,
      BoundedMartingaleQuadraticConvexification.squaredIncrementPart_apply] using h
  have hfInt : ∀ k, Integrable (f k) mu := fun k =>
    memLp_one_iff_integrable.mp (hUI.memLp k)
  have hIntegral : Tendsto (fun k => ∫ w, f k w ∂mu) atTop (𝓝 (∫ w, Z w ∂mu)) :=
    tendsto_integral_of_L1' Z (Eventually.of_forall hfInt) hLimit
  have hYZero : Y 0 = 0 := by
    funext w
    change X (min 0 (R.tau n w)) w = 0
    rw [zero_min]
    have h := congrFun (congrFun d.decomposition 0) w
    simpa only [Pi.add_apply, d.L_zero, d.Q_zero, Pi.zero_apply, add_zero] using h
  have hGrid : ∀ r, (∫ w, FactorialChronologicalGrid.factorialRunningMax
      (fun t w => |Y t w|) T (BoundedMartingaleQuadraticApproximation.level T r) w ∂mu) ≤
      6 * ∫ w, Z w ∂mu := by
    intro r
    apply le_of_tendsto_of_tendsto tendsto_const_nhds (hIntegral.const_mul 6)
    filter_upwards [eventually_ge_atTop r] with k hk
    exact BoundedMartingaleQuadraticKernel.factorialGridDavis_integral_runningMax_le_six_convexRoot
      Y T (R.source_martingale n) hYZero (D.weights (D.cutoff k)) (hfInt k) r
      (hk.trans D.cutoff_strictMono.le_apply)
  exact ⟨hInt,
    BoundedMartingaleQuadraticKernel.finiteHorizonAbsoluteEnvelope_integrable_of_grid_bound
      Y T (R.source_martingale n)
      (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous X hXR)
      (hXL.stoppedProcess _) (mul_nonneg (by norm_num)
        (integral_nonneg (fun _ => Real.sqrt_nonneg _))) hGrid⟩

theorem exists_localMartingaleQuadraticVariation_common_davis
    (hX : LocalMartingale X F mu) (hXA : StronglyAdapted F X)
    (hXR : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hXL : ProcessHasLeftLimits X) (hXZero : X 0 = 0)
    (hUsual : Filtration.UsualConditions mu F) :
    ∃ (Q : LocalMartingaleQuadraticVariation X F mu)
      (d : DoleansDadeYenData X F mu 1) (R : DoleansDadeYenL1Localization d),
      ∀ n T,
        let Y := stoppedProcess X (fun w => (R.tau n w : WithTop NNReal))
        let Z := fun w => Real.sqrt (Q.variation (min T (R.tau n w)) w)
        Integrable Z mu ∧
        Integrable (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope Y T) mu ∧
        (∫ w, FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope Y T w ∂mu) ≤
          6 * ∫ w, Z w ∂mu := by
  obtain ⟨d, C, QC, _, _, _, _, _, _, _, _, _, hV, _⟩ :=
    HorizonFactorialGrid.exists_doleansDadeYen_quadratic_davis
      hX hXA hXR hXL hXZero (c := 1) zero_lt_one hUsual
  obtain ⟨V, hInd, hAdapted, hRight, hMono, hZero, hBV, hLeft, hJump, _, _, hResidual⟩ := hV
  let Q : LocalMartingaleQuadraticVariation X F mu := {
    variation := V
    stronglyAdapted := hAdapted
    rightContinuous := hRight
    leftLimits := hLeft
    locallyBoundedVariation := hBV
    monotone := hMono
    zero := hZero
    jump_sq := hJump
    squareResidual := hResidual }
  obtain ⟨R⟩ := d.exists_common_localizer_integrableVariation zero_le_one
  exact ⟨Q, d, R, R.source_continuous_davis hUsual hXR hXL C QC hInd⟩

end FTAPTheorem42
