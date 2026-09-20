/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.DoleansDadeYen.StoppedRootIdentification

/-! # Reverse Davis inequality for general zero-initial local martingales -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  {X : Process Ω}

theorem LocalMartingaleQuadraticVariation.lintegral_root_le_seven_maximal
    (Q : LocalMartingaleQuadraticVariation X F mu)
    (hX : LocalMartingale X F mu) (hXA : StronglyAdapted F X)
    (hXR : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hXL : ProcessHasLeftLimits X) (hXZero : X 0 = 0)
    (hUsual : Filtration.UsualConditions mu F) (T : NNReal) :
    (∫⁻ w, ENNReal.ofReal (Real.sqrt (Q.variation T w)) ∂mu) ≤
      7 * ∫⁻ w, ENNReal.ofReal
        (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope X T w) ∂mu := by
  let : F.IsRightContinuous := hUsual.rightContinuous
  obtain ⟨d, C, QC, _, _, _, _, _, _, _, _, _, hV, _⟩ :=
    HorizonFactorialGrid.exists_doleansDadeYen_quadratic_davis
      hX hXA hXR hXL hXZero (c := 1) zero_lt_one hUsual
  obtain ⟨V, hInd, hAdapted, hRight, hMono, hZero, hBV, hLeft, hJump, _, _, hResidual⟩ := hV
  let P : LocalMartingaleQuadraticVariation X F mu := {
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
  let E := fun n w => ENNReal.ofReal (Real.sqrt (P.variation (min T (R.tau n w)) w))
  let B := fun w => ENNReal.ofReal (Real.sqrt (P.variation T w))
  have hEmeas (n : Nat) : AEMeasurable (E n) mu := by
    let PN := P.stopped hXR hXL hXZero (R.isLocalizingSequence.isStoppingTime n)
    exact (((PN.stronglyAdapted T).mono (F.le T)).measurable.sqrt.ennreal_ofReal).aemeasurable
  have hBound (n : Nat) : (∫⁻ w, E n w ∂mu) ≤
      7 * ∫⁻ w, ENNReal.ofReal
        (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope X T w) ∂mu := by
    apply (R.source_continuous_reverse_davis hUsual hXR hXL C QC hInd n T).trans
    apply mul_le_mul' le_rfl
    apply lintegral_mono
    intro w
    dsimp only
    rw [FactorialChronologicalGrid.ofReal_finiteHorizonAbsoluteEnvelope_eq_iSup
      (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous X hXR)
      (hXL.stoppedProcess _) T]
    apply iSup_le
    intro t
    apply ENNReal.ofReal_le_ofReal
    exact FactorialChronologicalGrid.abs_le_finiteHorizonAbsoluteEnvelope_of_cadlag
      hXR hXL T (min t.1 (R.tau n w)) ((min_le_left _ _).trans t.2)
  have hLimit : ∀ᵐ w ∂mu, Tendsto (fun n => E n w) atTop (𝓝 (B w)) := by
    filter_upwards [R.isLocalizingSequence.tendsto_top] with w hw
    apply tendsto_const_nhds.congr'
    filter_upwards [(WithTop.tendsto_nhds_top_iff _).mp hw T] with n hn
    have hT : T ≤ R.tau n w := (WithTop.coe_lt_coe.mp hn).le
    simp only [E, B, min_eq_left hT]
  have hFatou : (∫⁻ w, B w ∂mu) ≤
      7 * ∫⁻ w, ENNReal.ofReal
        (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope X T w) ∂mu := by
    calc
      (∫⁻ w, B w ∂mu) = ∫⁻ w, liminf (fun n => E n w) atTop ∂mu :=
        lintegral_congr_ae (hLimit.mono (fun _ h => h.liminf_eq.symm))
      _ ≤ liminf (fun n => ∫⁻ w, E n w ∂mu) atTop := lintegral_liminf_le' hEmeas
      _ ≤ _ := liminf_le_of_frequently_le' (Eventually.of_forall hBound).frequently
  have hPQ := P.unique hUsual hXR Q
  have hRootEq : B =ᵐ[mu] (fun w => ENNReal.ofReal (Real.sqrt (Q.variation T w))) := by
    filter_upwards [hPQ] with w hw
    exact congrArg (fun x => ENNReal.ofReal (Real.sqrt x)) (hw T)
  rwa [lintegral_congr_ae hRootEq] at hFatou

end FTAPTheorem42
