/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Martingale.Davis.LocalMartingaleReverseDavis
import FTAPTheorem42.Stochastic.Topology.J1.MartingaleRegularization

/-! # Quadratic-root control for the limit of a martingale series -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]

theorem J1Decomposition.lintegral_root_series_le
    {Z : Nat → Process Ω} (D : ∀ k, J1Decomposition (Z k) F mu)
    (Q : ∀ k, LocalMartingaleQuadraticVariation (D k).N F mu)
    {X : Process Ω} (P : LocalMartingaleQuadraticVariation X F mu)
    (hX : LocalMartingale X F mu) (hXA : StronglyAdapted F X)
    (hXR : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hXL : ProcessHasLeftLimits X) (hXZero : X 0 = 0)
    (hUsual : Filtration.UsualConditions mu F) (T : NNReal)
    (hU : ∀ᵐ w ∂mu, TendstoUniformlyOn
      (fun n t => ∑ k ∈ Finset.range n, (D k).N t w) (X · w) atTop (Icc 0 T)) :
    (∫⁻ w, ENNReal.ofReal (Real.sqrt (P.variation T w)) ∂mu) ≤
      42 * ∑' k, ∫⁻ w, ENNReal.ofReal (Real.sqrt ((Q k).variation T w)) ∂mu := by
  let g := fun k w => ENNReal.ofReal
    (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope (D k).N T w)
  have hMeas (k : Nat) : Measurable (g k) :=
    ((FactorialChronologicalGrid.stronglyMeasurable_finiteHorizonAbsoluteEnvelope
      (D k).adaptedN T).mono (F.le T)).measurable.ennreal_ofReal
  have hEnvelope : ∀ᵐ w ∂mu, ENNReal.ofReal
      (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope X T w) ≤ ∑' k, g k w := by
    filter_upwards [hU] with w hw
    rw [FactorialChronologicalGrid.ofReal_finiteHorizonAbsoluteEnvelope_eq_iSup hXR hXL T]
    apply iSup_le
    intro t
    have hLimit := ENNReal.tendsto_ofReal ((hw.tendsto_at ⟨bot_le, t.2⟩).abs)
    apply le_of_tendsto hLimit
    apply Eventually.of_forall
    intro n
    calc
      ENNReal.ofReal |∑ k ∈ Finset.range n, (D k).N t.1 w| ≤
          ENNReal.ofReal (∑ k ∈ Finset.range n,
            FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope (D k).N T w) := by
        apply ENNReal.ofReal_le_ofReal
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        exact Finset.sum_le_sum (fun k _ =>
          FactorialChronologicalGrid.abs_le_finiteHorizonAbsoluteEnvelope_of_cadlag
            (D k).rightN (D k).leftN T t.1 t.2)
      _ = ∑ k ∈ Finset.range n, g k w :=
        ENNReal.ofReal_sum_of_nonneg (fun _ _ => Real.sqrt_nonneg _)
      _ ≤ _ := ENNReal.sum_le_tsum _
  calc
    _ ≤ 7 * ∫⁻ w, ENNReal.ofReal
        (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope X T w) ∂mu :=
      P.lintegral_root_le_seven_maximal hX hXA hXR hXL hXZero hUsual T
    _ ≤ 7 * ∫⁻ w, ∑' k, g k w ∂mu := mul_le_mul' le_rfl (lintegral_mono_ae hEnvelope)
    _ = 7 * ∑' k, ∫⁻ w, g k w ∂mu := by
      rw [lintegral_tsum (fun k => (hMeas k).aemeasurable)]
    _ ≤ 7 * ∑' k, 6 * ∫⁻ w, ENNReal.ofReal (Real.sqrt ((Q k).variation T w)) ∂mu := by
      apply mul_le_mul' le_rfl
      exact ENNReal.tsum_le_tsum (fun k => (Q k).lintegral_maximal_le_six_root
        (D k).localMartingale (D k).adaptedN (D k).rightN (D k).leftN (D k).zeroN hUsual T)
    _ = _ := by rw [ENNReal.tsum_mul_left, ← mul_assoc]; norm_num

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## Quadratic-root tails of the same martingale sum after a common stop -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

open RightContinuousStoppedMartingale

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]

private theorem partialSum_regular
    {Z : Nat → Process Ω} (D : ∀ k, J1Decomposition (Z k) F mu) (n : Nat) :
    let S := fun t w => ∑ k ∈ Finset.range n, (D k).N t w
    StronglyAdapted F S ∧ LocalMartingale S F mu ∧
      (∀ w t, ContinuousWithinAt (S · w) (Ici t) t) ∧
      ProcessHasLeftLimits S ∧ S 0 = 0 := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    refine ⟨(martingale_zero Real F mu).stronglyAdapted,
      Locally.of_prop (martingale_zero Real F mu),
      fun _ _ => continuousWithinAt_const, ?_, rfl⟩
    exact fun _ _ => tendsto_leftLim_of_tendsto ⟨0, tendsto_const_nhds⟩
  | succ n ih =>
    obtain ⟨hA, hM, hR, hL, hZ⟩ := ih
    simp only [Finset.sum_range_succ]
    exact ⟨hA.add (D n).adaptedN,
      hM.add_of_rightContinuous (D n).localMartingale hR (D n).rightN,
      fun w t => (hR w t).add ((D n).rightN w t), hL.add (D n).leftN,
      by simp only [hZ, (D n).zeroN, Pi.zero_apply, add_zero]⟩

theorem J1Decomposition.lintegral_root_series_tail_stopped_le
    {Z : Nat → Process Ω} (D : ∀ k, J1Decomposition (Z k) F mu)
    (Q : ∀ k, LocalMartingaleQuadraticVariation (D k).N F mu)
    {M : Process Ω} (hM : LocalMartingale M F mu) (hMA : StronglyAdapted F M)
    (hMR : ∀ w t, ContinuousWithinAt (M · w) (Ici t) t)
    (hML : ProcessHasLeftLimits M) (hMZero : M 0 = 0)
    (hEq : ProcessIndistinguishable mu M (fun t w => ∑' k, (D k).N t w))
    (hUsual : Filtration.UsualConditions mu F)
    {tau : Ω → NNReal} {T : NNReal}
    (hTau : IsStoppingTime F (fun w => (tau w : WithTop NNReal)))
    (hTauT : ∀ w, tau w ≤ T)
    (hSum : (∑' k, ∫⁻ w, ENNReal.ofReal (Real.sqrt ((Q k).variation (tau w) w)) ∂mu) ≠ ∞)
    (n : Nat)
    (P : LocalMartingaleQuadraticVariation
      (fun t w => M t w - ∑ k ∈ Finset.range n, (D k).N t w) F mu) :
    (∫⁻ w, ENNReal.ofReal (Real.sqrt (P.variation (tau w) w)) ∂mu) ≤
      42 * ∑' k, ∫⁻ w, ENNReal.ofReal (Real.sqrt ((Q (k + n)).variation (tau w) w)) ∂mu := by
  let S := fun t w => ∑ k ∈ Finset.range n, (D k).N t w
  let X := M - S
  obtain ⟨hSA, hSM, hSR, hSL, hSZ⟩ := partialSum_regular D n
  have hXA : StronglyAdapted F X := hMA.sub hSA
  have hXR : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t :=
    fun w t => (hMR w t).sub (hSR w t)
  have hXL : ProcessHasLeftLimits X := hML.sub hSL
  have hXZ : X 0 = 0 := by simp only [X, S, Pi.sub_apply, hMZero, hSZ, sub_self]
  have hXM : LocalMartingale X F mu := by
    change LocalMartingale (fun t w => M t w - S t w) F mu
    simpa only [S, sub_eq_add_neg] using
      hM.add_of_rightContinuous hSM.neg hMR (fun w t => (hSR w t).neg)
  let E := fun k => (D (k + n)).stopped hTau
  let QE := fun k => (Q (k + n)).stopped
    (D (k + n)).rightN (D (k + n)).leftN (D (k + n)).zeroN hTau
  let XP := stoppedProcess X (fun w => (tau w : WithTop NNReal))
  let PP := P.stopped hXR hXL hXZ hTau
  have hXPM : LocalMartingale XP F mu := hXM.stoppedProcess_of_zero_of_rightContinuous hXZ hXR hTau
  have hXPA : StronglyAdapted F XP :=
    StronglyAdapted.stoppedProcess_of_rightContinuous hXA hTau hXR
  have hXPR := RightContinuousStoppedMartingale.stoppedProcess_rightContinuous X hXR
    (τ := fun w => (tau w : WithTop NNReal))
  have hXPZ : XP 0 = 0 := by
    funext w
    change X (min 0 (tau w)) w = 0
    simp only [zero_min, hXZ, Pi.zero_apply]
  have hRows := (J1Decomposition.martingale_tsum_stopped_of_summable_roots
    D Q hUsual hTau hTauT hSum).2
  have hU : ∀ᵐ w ∂mu, TendstoUniformlyOn
      (fun m t => ∑ k ∈ Finset.range m, (E k).N t w) (XP · w) atTop (Icc 0 T) := by
    filter_upwards [hRows, hEq] with w hw heq
    have hShift : TendstoUniformlyOn
        (fun m t => ∑ k ∈ Finset.range (m + n),
          stoppedProcess (D k).N (fun w => (tau w : WithTop NNReal)) t w)
        (fun t => stoppedProcess (fun t w => ∑' k, (D k).N t w)
          (fun w => (tau w : WithTop NNReal)) t w) atTop (Icc 0 T) := by
      intro u hu
      exact (tendsto_add_atTop_nat n).eventually (hw.tendstoUniformlyOn u hu)
    have hConst : TendstoUniformlyOn (fun (_ : Nat) t => S (min t (tau w)) w)
        (fun t => S (min t (tau w)) w) atTop (Icc 0 T) := by
      intro u hu
      exact Eventually.of_forall (fun _ _ _ => refl_mem_uniformity hu)
    have hDiff := (hShift.sub hConst).congr_right (fun t _ => by
      change (∑' k, (D k).N (min t (tau w)) w) - S (min t (tau w)) w = _
      rw [← heq (min t (tau w))])
    apply hDiff.congr
    apply Eventually.of_forall
    intro m t _
    change (∑ k ∈ Finset.range (m + n), (D k).N (min t (tau w)) w) -
      ∑ k ∈ Finset.range n, (D k).N (min t (tau w)) w =
      ∑ k ∈ Finset.range m, (D (k + n)).N (min t (tau w)) w
    rw [Nat.add_comm m n, Finset.sum_range_add, add_sub_cancel_left]
    exact Finset.sum_congr rfl (fun k _ => by rw [Nat.add_comm n k])
  have h := J1Decomposition.lintegral_root_series_le E QE PP hXPM hXPA hXPR
    (hXL.stoppedProcess _) hXPZ hUsual T hU
  have hStopP : ∀ w, PP.variation T w = P.variation (tau w) w := fun w => by
    change P.variation (min T (tau w)) w = _
    rw [min_eq_right (hTauT w)]
  have hStopQ : ∀ k w, (QE k).variation T w = (Q (k + n)).variation (tau w) w := fun k w => by
    change (Q (k + n)).variation (min T (tau w)) w = _
    rw [min_eq_right (hTauT w)]
  simpa only [hStopP, hStopQ] using h

theorem J1Decomposition.exists_quadratic_series_tails
    {Z : Nat → Process Ω} (D : ∀ k, J1Decomposition (Z k) F mu)
    (Q : ∀ k, LocalMartingaleQuadraticVariation (D k).N F mu)
    {M : Process Ω} (hM : LocalMartingale M F mu) (hMA : StronglyAdapted F M)
    (hMR : ∀ w t, ContinuousWithinAt (M · w) (Ici t) t)
    (hML : ProcessHasLeftLimits M) (hMZero : M 0 = 0)
    (hEq : ProcessIndistinguishable mu M (fun t w => ∑' k, (D k).N t w))
    (hUsual : Filtration.UsualConditions mu F) :
    ∃ P : ∀ n, LocalMartingaleQuadraticVariation
        (fun t w => M t w - ∑ k ∈ Finset.range n, (D k).N t w) F mu,
      ∀ (tau : Ω → NNReal) (T : NNReal),
        IsStoppingTime F (fun w => (tau w : WithTop NNReal)) →
        (∀ w, tau w ≤ T) →
        (∑' k, ∫⁻ w, ENNReal.ofReal (Real.sqrt ((Q k).variation (tau w) w)) ∂mu) ≠ ∞ →
        Tendsto (fun n => ∫⁻ w, ENNReal.ofReal (Real.sqrt ((P n).variation (tau w) w)) ∂mu)
          atTop (𝓝 0) := by
  let : F.IsRightContinuous := hUsual.rightContinuous
  have hExists (n : Nat) : Nonempty (LocalMartingaleQuadraticVariation
      (fun t w => M t w - ∑ k ∈ Finset.range n, (D k).N t w) F mu) := by
    obtain ⟨hSA, hSM, hSR, hSL, _⟩ := partialSum_regular D n
    let X := fun t w => M t w - ∑ k ∈ Finset.range n, (D k).N t w
    have hXR : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t :=
      fun w t => (hMR w t).sub (hSR w t)
    have hXZ : X 0 = 0 := by
      funext w
      simp only [X, hMZero, (D _).zeroN, Pi.zero_apply, Finset.sum_const_zero, sub_self]
    have hXM : LocalMartingale X F mu := by
      simpa only [X, sub_eq_add_neg] using
        hM.add_of_rightContinuous hSM.neg hMR (fun w t => (hSR w t).neg)
    obtain ⟨P, _⟩ := exists_unique_localMartingaleQuadraticVariation
      hXM (hMA.sub hSA) hXR (hML.sub hSL) hXZ hUsual
    exact ⟨P⟩
  let P := fun n => Classical.choice (hExists n)
  refine ⟨P, fun tau T hTau hTauT hSum => ?_⟩
  have hBound := fun n => J1Decomposition.lintegral_root_series_tail_stopped_le
    D Q hM hMA hMR hML hMZero hEq hUsual hTau hTauT hSum n (P n)
  have hTail := ENNReal.tendsto_sum_nat_add
    (fun k => ∫⁻ w, ENNReal.ofReal (Real.sqrt ((Q k).variation (tau w) w)) ∂mu) hSum
  have hUpper := ENNReal.Tendsto.const_mul hTail
    (Or.inr (by norm_num : (42 : ENNReal) ≠ ∞))
  simp only [mul_zero] at hUpper
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hUpper (fun _ => bot_le) hBound

end FTAPTheorem42
