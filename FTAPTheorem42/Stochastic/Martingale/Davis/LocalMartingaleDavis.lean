/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.DoleansDadeYen.ContinuousDavis

/-! # Davis's maximal inequality for general zero-initial local martingales -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  {X : Process Ω}

theorem LocalMartingaleQuadraticVariation.lintegral_maximal_le_six_root
    (Q : LocalMartingaleQuadraticVariation X F mu)
    (hX : LocalMartingale X F mu) (hXA : StronglyAdapted F X)
    (hXR : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hXL : ProcessHasLeftLimits X) (hXZero : X 0 = 0)
    (hUsual : Filtration.UsualConditions mu F) (T : NNReal) :
    (∫⁻ w, ENNReal.ofReal
      (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope X T w) ∂mu) ≤
      6 * ∫⁻ w, ENNReal.ofReal (Real.sqrt (Q.variation T w)) ∂mu := by
  let : F.IsRightContinuous := hUsual.rightContinuous
  obtain ⟨P, d, R, hDavis⟩ := exists_localMartingaleQuadraticVariation_common_davis
    hX hXA hXR hXL hXZero hUsual
  let Y := fun n => stoppedProcess X (fun w => (R.tau n w : WithTop NNReal))
  let E := fun n w => ENNReal.ofReal
    (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope (Y n) T w)
  let B := fun w => ENNReal.ofReal
    (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope X T w)
  have hEmeas : ∀ n, AEMeasurable (E n) mu := fun n =>
    (((FactorialChronologicalGrid.stronglyMeasurable_finiteHorizonAbsoluteEnvelope
      (R.source_martingale n).stronglyAdapted T).mono
        (F.le T)).measurable.ennreal_ofReal).aemeasurable
  have hBound : ∀ n, (∫⁻ w, E n w ∂mu) ≤
      6 * ∫⁻ w, ENNReal.ofReal (Real.sqrt (P.variation T w)) ∂mu := by
    intro n
    obtain ⟨hZ, hE, hLe⟩ := hDavis n T
    calc
      (∫⁻ w, E n w ∂mu) = ENNReal.ofReal
          (∫ w, FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope (Y n) T w ∂mu) :=
        (ofReal_integral_eq_lintegral_ofReal hE
          (Eventually.of_forall (fun _ => Real.sqrt_nonneg _))).symm
      _ ≤ ENNReal.ofReal (6 * ∫ w, Real.sqrt
          (P.variation (min T (R.tau n w)) w) ∂mu) := ENNReal.ofReal_le_ofReal hLe
      _ = 6 * ∫⁻ w, ENNReal.ofReal
          (Real.sqrt (P.variation (min T (R.tau n w)) w)) ∂mu := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 6),
          ofReal_integral_eq_lintegral_ofReal hZ
            (Eventually.of_forall (fun _ => Real.sqrt_nonneg _))]
        norm_num
      _ ≤ 6 * ∫⁻ w, ENNReal.ofReal (Real.sqrt (P.variation T w)) ∂mu := by
        apply mul_le_mul' le_rfl
        apply lintegral_mono
        intro w
        exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (P.monotone w (min_le_left _ _)))
  have hLimit : ∀ᵐ w ∂mu, Tendsto (fun n => E n w) atTop (𝓝 (B w)) := by
    filter_upwards [R.isLocalizingSequence.tendsto_top] with w hw
    apply tendsto_const_nhds.congr'
    filter_upwards [(WithTop.tendsto_nhds_top_iff _).mp hw T] with n hn
    have hT : T ≤ R.tau n w := (WithTop.coe_lt_coe.mp hn).le
    dsimp only [E, B]
    rw [FactorialChronologicalGrid.ofReal_finiteHorizonAbsoluteEnvelope_eq_iSup hXR hXL T,
      FactorialChronologicalGrid.ofReal_finiteHorizonAbsoluteEnvelope_eq_iSup
        (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous X hXR)
        (hXL.stoppedProcess _) T]
    congr 1
    funext t
    change ENNReal.ofReal |X t.1 w| = ENNReal.ofReal |X (min t.1 (R.tau n w)) w|
    rw [min_eq_left (t.2.trans hT)]
  have hFatou : (∫⁻ w, B w ∂mu) ≤
      6 * ∫⁻ w, ENNReal.ofReal (Real.sqrt (P.variation T w)) ∂mu := by
    calc
      (∫⁻ w, B w ∂mu) = ∫⁻ w, liminf (fun n => E n w) atTop ∂mu :=
        lintegral_congr_ae (hLimit.mono (fun _ h => h.liminf_eq.symm))
      _ ≤ liminf (fun n => ∫⁻ w, E n w ∂mu) atTop := lintegral_liminf_le' hEmeas
      _ ≤ _ := liminf_le_of_frequently_le' (Eventually.of_forall hBound).frequently
  have hPQ := P.unique hUsual hXR Q
  have hRootEq : (fun w => ENNReal.ofReal (Real.sqrt (P.variation T w))) =ᵐ[mu]
      (fun w => ENNReal.ofReal (Real.sqrt (Q.variation T w))) := by
    filter_upwards [hPQ] with w hw
    rw [hw T]
  rwa [lintegral_congr_ae hRootEq] at hFatou

/-! ## Infinite-horizon Davis costs -/

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
theorem LocalMartingaleQuadraticVariation.measurable_allTimeRoot
    (Q : LocalMartingaleQuadraticVariation X F mu) :
    Measurable (fun w => ⨆ t : NNReal, ENNReal.ofReal (Real.sqrt (Q.variation t w))) := by
  have hEq : (fun w => ⨆ t : NNReal, ENNReal.ofReal (Real.sqrt (Q.variation t w))) =
      (fun w => ⨆ n : Nat, ENNReal.ofReal (Real.sqrt (Q.variation n w))) := by
    funext w
    apply le_antisymm
    · apply iSup_le
      intro t
      exact le_iSup_of_le (Nat.ceil t) (ENNReal.ofReal_le_ofReal
        (Real.sqrt_le_sqrt (Q.monotone w (Nat.le_ceil t))))
    · exact iSup_le (fun n => le_iSup
        (fun t : NNReal => ENNReal.ofReal (Real.sqrt (Q.variation t w))) (n : NNReal))
  rw [hEq]
  apply Measurable.iSup
  intro n
  exact (Real.continuous_sqrt.measurable.comp
    ((Q.stronglyAdapted n).mono (F.le n)).measurable).ennreal_ofReal

theorem LocalMartingaleQuadraticVariation.lintegral_allTime_maximal_le_six_root
    (Q : LocalMartingaleQuadraticVariation X F mu)
    (hX : LocalMartingale X F mu) (hXA : StronglyAdapted F X)
    (hXR : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hXL : ProcessHasLeftLimits X) (hXZero : X 0 = 0)
    (hUsual : Filtration.UsualConditions mu F) :
    (∫⁻ w, ⨆ t : NNReal, ENNReal.ofReal |X t w| ∂mu) ≤
      6 * ∫⁻ w, ⨆ t : NNReal, ENNReal.ofReal (Real.sqrt (Q.variation t w)) ∂mu := by
  let E := fun n w => ENNReal.ofReal
    (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope X ((n + 1 : Nat) : NNReal) w)
  have hMeas : ∀ n, Measurable (E n) := fun n =>
    ((FactorialChronologicalGrid.stronglyMeasurable_finiteHorizonAbsoluteEnvelope
      hXA ((n + 1 : Nat) : NNReal)).mono (F.le _)).measurable.ennreal_ofReal
  have hMono : Monotone E := by
    intro n m hnm w
    exact ENNReal.ofReal_le_ofReal
      (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope_mono hXR hXL
        (by exact_mod_cast Nat.add_le_add_right hnm 1))
  have hEnvelope : (fun w => ⨆ t : NNReal, ENNReal.ofReal |X t w|) =
      (fun w => ⨆ n, E n w) := by
    funext w
    exact (FactorialChronologicalGrid.allTimeAbsoluteEnvelope_eq_iSup hXR hXL).symm
  rw [hEnvelope, lintegral_iSup hMeas hMono]
  apply iSup_le
  intro n
  exact (Q.lintegral_maximal_le_six_root hX hXA hXR hXL hXZero hUsual _).trans
    (mul_le_mul' le_rfl (lintegral_mono (fun w => le_iSup
      (fun t : NNReal => ENNReal.ofReal (Real.sqrt (Q.variation t w))) _)))

end FTAPTheorem42
