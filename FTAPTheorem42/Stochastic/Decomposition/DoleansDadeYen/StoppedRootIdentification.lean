/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.DoleansDadeYen.RootUniformIntegrability
import FTAPTheorem42.Stochastic.Martingale.Quadratic.IntrinsicCertificates
import FTAPTheorem42.Stochastic.Martingale.Quadratic.BoundedMartingaleQuadraticUnconvexAE
import FTAPTheorem42.Stochastic.Martingale.Davis.QuadraticLimit

/-! # L1 convergence of the original DDY source's stopped quadratic roots -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  {X : Process Ω} {c : Real}

theorem DoleansDadeYenL1Localization.coordinate_root_tendsto_L1
    {d : DoleansDadeYenData X F mu c} (R : DoleansDadeYenL1Localization d)
    (hXR : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t) (n : Nat) (T : NNReal)
    (D : BoundedMartingaleQuadraticKernel.Data F mu
      (stoppedProcess d.L (fun w => (R.tau n w : WithTop NNReal))) T) :
    let Y := stoppedProcess X (fun w => (R.tau n w : WithTop NNReal))
    let Z := fun w => Real.sqrt
      (D.variation T w + d.quadraticCorrection (min T (R.tau n w)) w)
    Integrable Z mu ∧
    Tendsto (fun k => eLpNorm ((fun w => Real.sqrt
      (BoundedMartingaleQuadraticConvexification.squaredIncrementPart
        Y T (D.weights (D.cutoff k)) T w)) - Z) 1 mu) atTop (𝓝 0) := by
  let W := TailConvexWeights.toForwardReindex D.cutoff D.cutoff_strictMono D.weights
  let Y := stoppedProcess X (fun w => (R.tau n w : WithTop NNReal))
  let Z := fun w => Real.sqrt
    (D.variation T w + d.quadraticCorrection (min T (R.tau n w)) w)
  let f := fun k w => Real.sqrt
    (BoundedMartingaleQuadraticConvexification.squaredIncrementPart
      Y T (D.weights (D.cutoff k)) T w)
  have hUI : UniformIntegrable f 1 mu := by
    have h := R.source_convex_root_uniformIntegrable hXR n T W
    simpa only [W, f, Y, TailConvexWeights.toForwardReindex_apply,
      BoundedMartingaleQuadraticConvexification.squaredIncrementPart_apply] using h
  have hLimit : ∀ᵐ w ∂mu, Tendsto (fun k => f k w) atTop (𝓝 (Z w)) := by
    filter_upwards [d.coordinate_stopped_corrected_tendsto (R.tau n) T D] with w hw
    exact (Real.continuous_sqrt.tendsto _).comp (hw T le_rfl)
  exact ⟨hUI.integrable_of_ae_tendsto hLimit,
    tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top hUI.aestronglyMeasurable
      (hUI.memLp_of_ae_tendsto hLimit) hUI.unifIntegrable hLimit⟩

theorem DoleansDadeYenL1Localization.exists_coordinate_root_tendsto_L1
    {d : DoleansDadeYenData X F mu c} (R : DoleansDadeYenL1Localization d)
    (hUsual : Filtration.UsualConditions mu F)
    (hXR : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t) (n : Nat) (T : NNReal) :
    ∃ D : BoundedMartingaleQuadraticKernel.Data F mu
        (stoppedProcess d.L (fun w => (R.tau n w : WithTop NNReal))) T,
      let Y := stoppedProcess X (fun w => (R.tau n w : WithTop NNReal))
      let Z := fun w => Real.sqrt
        (D.variation T w + d.quadraticCorrection (min T (R.tau n w)) w)
      Integrable Z mu ∧
      Tendsto (fun k => eLpNorm ((fun w => Real.sqrt
        (BoundedMartingaleQuadraticConvexification.squaredIncrementPart
          Y T (D.weights (D.cutoff k)) T w)) - Z) 1 mu) atTop (𝓝 0) := by
  have hM := R.L_martingale n
  have hMT : MemLp
      (stoppedProcess d.L (fun w => (R.tau n w : WithTop NNReal)) T) 2 mu := by
    apply MemLp.of_bound ((hM.stronglyAdapted T).mono (F.le T)).aestronglyMeasurable
      (cadlagPassageLevel n + 2 * c)
    filter_upwards [R.L_bound n] with w hw
    simpa only [Real.norm_eq_abs] using hw T
  obtain ⟨D⟩ := SquareIntegrableMartingaleQuadraticKernel.exists_data hUsual hM
    (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous d.L d.L_rightContinuous)
    T hMT
  exact ⟨D, R.coordinate_root_tendsto_L1 hXR n T D⟩

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## Identifying the stopped DDY root limit with the original quadratic variation -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  [F.IsRightContinuous] {X : Process Ω} {c : Real}

theorem DoleansDadeYenL1Localization.corrected_terminal_eq
    {d : DoleansDadeYenData X F mu c} (R : DoleansDadeYenL1Localization d)
    (hUsual : Filtration.UsualConditions mu F)
    (C : LocalMartingaleQuadratic.LocalMartingaleQuadraticSchedule
      (F := F) (mu := mu) (M := d.L))
    (QC : LocalMartingaleQuadratic.GluedQuadraticVariationCertificate C)
    {V : Process Ω} (hV : ProcessIndistinguishable mu V
      (fun t w => QC.variation t w + d.quadraticCorrection t w))
    (n : Nat) (T : NNReal)
    (D : BoundedMartingaleQuadraticKernel.Data F mu
      (stoppedProcess d.L (fun w => (R.tau n w : WithTop NNReal))) T) :
    ∀ᵐ w ∂mu, D.variation T w + d.quadraticCorrection (min T (R.tau n w)) w =
      V (min T (R.tau n w)) w := by
  let tau : Ω → WithTop NNReal := fun w => R.tau n w
  let M := stoppedProcess d.L tau
  have hMR : ∀ w t, ContinuousWithinAt (M · w) (Ici t) t :=
    RightContinuousStoppedMartingale.stoppedProcess_rightContinuous d.L d.L_rightContinuous
  have hML : ProcessHasLeftLimits M := d.L_leftLimits.stoppedProcess tau
  have hM0 : M 0 = 0 := by
    funext w
    simp only [M, tau, BoundedMartingaleQuadraticKernel.Data.stoppedProcess_coe_apply,
      zero_min, d.L_zero, Pi.zero_apply]
  let P := (QC.toIntrinsic d.L_zero).stopped d.L_rightContinuous d.L_leftLimits d.L_zero
    (R.isLocalizingSequence.isStoppingTime n)
  let PT := P.stopped hMR hML hM0 (isStoppingTime_const F T)
  have hEq := (D.toIntrinsic (R.L_martingale n) hMR hML hM0).unique hUsual
    (BoundedMartingaleQuadraticApproximation.stoppedSource_rightContinuous M hMR T) PT
  filter_upwards [hEq, hV] with w hw hVw
  have h := hw T
  change D.variation T w = stoppedProcess (stoppedProcess QC.variation tau)
    (fun _ => (T : WithTop NNReal)) T w at h
  simp only [stoppedProcess_const_apply, min_self, tau,
    BoundedMartingaleQuadraticKernel.Data.stoppedProcess_coe_apply] at h
  rw [h, hVw]

theorem DoleansDadeYenL1Localization.exists_original_root_tendsto_L1
    {d : DoleansDadeYenData X F mu c} (R : DoleansDadeYenL1Localization d)
    (hUsual : Filtration.UsualConditions mu F)
    (hXR : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (C : LocalMartingaleQuadratic.LocalMartingaleQuadraticSchedule
      (F := F) (mu := mu) (M := d.L))
    (QC : LocalMartingaleQuadratic.GluedQuadraticVariationCertificate C)
    {V : Process Ω} (hV : ProcessIndistinguishable mu V
      (fun t w => QC.variation t w + d.quadraticCorrection t w))
    (n : Nat) (T : NNReal) :
    ∃ D : BoundedMartingaleQuadraticKernel.Data F mu
        (stoppedProcess d.L (fun w => (R.tau n w : WithTop NNReal))) T,
      let Y := stoppedProcess X (fun w => (R.tau n w : WithTop NNReal))
      let Z := fun w => Real.sqrt (V (min T (R.tau n w)) w)
      Integrable Z mu ∧
      Tendsto (fun k => eLpNorm ((fun w => Real.sqrt
        (BoundedMartingaleQuadraticConvexification.squaredIncrementPart
          Y T (D.weights (D.cutoff k)) T w)) - Z) 1 mu) atTop (𝓝 0) := by
  obtain ⟨D, hInt, hLimit⟩ := R.exists_coordinate_root_tendsto_L1 hUsual hXR n T
  have hEq := R.corrected_terminal_eq hUsual C QC hV n T D
  have hRoot : (fun w => Real.sqrt
      (D.variation T w + d.quadraticCorrection (min T (R.tau n w)) w)) =ᵐ[mu]
      (fun w => Real.sqrt (V (min T (R.tau n w)) w)) := by
    filter_upwards [hEq] with w hw
    exact congrArg Real.sqrt hw
  refine ⟨D, hInt.congr hRoot, ?_⟩
  apply hLimit.congr'
  apply Eventually.of_forall
  intro k
  apply eLpNorm_congr_ae
  filter_upwards [hRoot] with w hw
  simp only [Pi.sub_apply, hw]

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## Original quadratic convergence and reverse Davis after common DDY stopping -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

open BoundedMartingaleQuadraticApproximation SquareIntegrableMartingaleQuadraticConvexification

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  [F.IsRightContinuous] {X : Process Ω} {c : Real}

theorem DoleansDadeYenL1Localization.source_quadratic_tendstoInMeasure
    {d : DoleansDadeYenData X F mu c} (R : DoleansDadeYenL1Localization d)
    (hUsual : Filtration.UsualConditions mu F)
    (hXR : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (C : LocalMartingaleQuadratic.LocalMartingaleQuadraticSchedule
      (F := F) (mu := mu) (M := d.L))
    (QC : LocalMartingaleQuadratic.GluedQuadraticVariationCertificate C)
    {V : Process Ω} (hV : ProcessIndistinguishable mu V
      (fun t w => QC.variation t w + d.quadraticCorrection t w))
    (n : Nat) (T : NNReal) :
    let Y := stoppedProcess X (fun w => (R.tau n w : WithTop NNReal))
    TendstoInMeasure mu (fun k => squaredIncrementPart Y T k T) atTop
      (fun w => V (min T (R.tau n w)) w) := by
  let tau : Ω → WithTop NNReal := fun w => R.tau n w
  let M := stoppedProcess d.L tau
  let Y := stoppedProcess X tau
  have hMR := RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
    d.L d.L_rightContinuous (τ := tau)
  have hYR := RightContinuousStoppedMartingale.stoppedProcess_rightContinuous X hXR (τ := tau)
  have hMT : MemLp (M T) (2 : ENNReal) mu := by
    apply MemLp.of_bound (((R.L_martingale n).stronglyAdapted T).mono (F.le T)).aestronglyMeasurable
      (cadlagPassageLevel n + 2 * c)
    filter_upwards [R.L_bound n] with w hw
    simpa only [Real.norm_eq_abs] using hw T
  obtain ⟨D⟩ := SquareIntegrableMartingaleQuadraticKernel.exists_data hUsual
    (R.L_martingale n) hMR T hMT
  have hBound : ∀ᵐ w ∂mu, ∀ t, t ≤ T →
      |M t w| ≤ Real.toNNReal (cadlagPassageLevel n + 2 * c) := by
    filter_upwards [R.L_bound n] with w hw
    exact fun t _ => (hw t).trans (Real.le_coe_toNNReal _)
  have hMIn := D.squaredIncrementPart_terminal_tendstoInMeasure hUsual (R.L_martingale n)
    hMR (d.L_leftLimits.stoppedProcess tau) hMT hBound
  have hCorrection : TendstoInMeasure mu
      (fun k => squaredIncrementPart Y T k T - squaredIncrementPart M T k T) atTop
      (fun w => d.quadraticCorrection (min T (R.tau n w)) w) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro k
      have h := (squaredIncrementPart_terminal_stronglyMeasurable
        (R.source_martingale n) hYR T k).sub
          (squaredIncrementPart_terminal_stronglyMeasurable (R.L_martingale n) hMR T k)
      exact h.aestronglyMeasurable
    · exact Eventually.of_forall (fun w => d.stoppedCorrection_tendsto (R.tau n) T T w le_rfl)
  have hSum := tendstoInMeasure_add hMIn hCorrection
  have hSource : TendstoInMeasure mu (fun k => squaredIncrementPart Y T k T) atTop
      (fun w => D.variation T w + d.quadraticCorrection (min T (R.tau n w)) w) := by
    simpa only [M, tau, Pi.sub_apply, ← add_sub_assoc, add_sub_cancel_left] using hSum
  exact hSource.congr_right (R.corrected_terminal_eq hUsual C QC hV n T D)

theorem DoleansDadeYenL1Localization.source_continuous_reverse_davis
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
    (∫⁻ w, ENNReal.ofReal (Real.sqrt (V (min T (R.tau n w)) w)) ∂mu) ≤
      7 * ∫⁻ w, ENNReal.ofReal
        (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope Y T w) ∂mu := by
  apply lintegral_root_le_seven_maximal_of_quadraticGrid_tendstoInMeasure
    (R.source_martingale n)
    (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous X hXR)
    (hXL.stoppedProcess _)
  · funext w
    change X (min 0 (R.tau n w)) w = 0
    rw [zero_min]
    have h := congrFun (congrFun d.decomposition 0) w
    simpa only [Pi.add_apply, d.L_zero, d.Q_zero, Pi.zero_apply, add_zero] using h
  · exact R.source_quadratic_tendstoInMeasure hUsual hXR C QC hV n T

end FTAPTheorem42
