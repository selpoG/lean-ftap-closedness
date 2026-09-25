/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Topology.J1.LeftClockSum
import FTAPTheorem42.Stochastic.Topology.J1.LeftVariation

/-! # Summing prelocal costs at a common stopping time -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  {X : Process Ω}

theorem J1Decomposition.leftVariation_nonneg
    (D : J1Decomposition X F mu) (t : NNReal) (w : Ω) :
    0 ≤ Function.leftLim (variationOnFromTo (D.A · w) univ 0) t := by
  by_cases ht : t = 0
  · subst t
    rw [leftLim_eq_of_isBot (a := (0 : NNReal)) isBot_bot, variationOnFromTo.self]
  have hMono : Monotone (variationOnFromTo (D.A · w) univ 0) := by
    rw [← monotoneOn_univ]
    exact variationOnFromTo.monotoneOn (D.variationA w) (mem_univ 0)
  simpa only [variationOnFromTo.self] using hMono.le_leftLim (pos_iff_ne_zero.mpr ht)

theorem J1Decomposition.measurable_sampledJump (D : J1Decomposition X F mu)
    {tau : Ω → NNReal} {T : NNReal}
    (hTau : IsStoppingTime F (fun w => (tau w : WithTop NNReal)))
    (hTauT : ∀ w, tau w ≤ T) :
    Measurable (fun w => ENNReal.ofReal |processLeftJump D.N (tau w) w|) := by
  have hProg : IsStronglyProgressive F (processLeftJump D.N) :=
    (FTAPTheorem42.StronglyAdapted.isStronglyProgressive_of_rightContinuous
      D.adaptedN D.rightN).sub
      (D.leftN.stronglyPredictable_leftLim D.adaptedN).isStronglyProgressive
  have hMeas := ((hProg.stronglyAdapted_stoppedProcess hTau T).mono (F.le T)).measurable
  have hEq : stoppedProcess (processLeftJump D.N)
      (fun w => (tau w : WithTop NNReal)) T =
      (fun w => processLeftJump D.N (tau w) w) := by
    funext w
    rw [stoppedProcess_eq_of_ge (u := processLeftJump D.N)
      (τ := fun w => (tau w : WithTop NNReal)) (WithTop.coe_le_coe.mpr (hTauT w))]
    rfl
  rw [hEq] at hMeas
  exact hMeas.abs.ennreal_ofReal

theorem J1Decomposition.prelocal_cost_le_leftClock_add_jump
    [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
    (D : J1Decomposition X F mu) (Q : LocalMartingaleQuadraticVariation D.N F mu)
    (hUsual : Filtration.UsualConditions mu F) {tau : Ω → NNReal} {T : NNReal}
    (hTau : IsStoppingTime F (fun w => (tau w : WithTop NNReal)))
    (hTauT : ∀ w, tau w ≤ T) :
    prelocalSemimartingaleJ1 X F mu (fun w => (tau w : WithTop NNReal)) ≤
      (∫⁻ w, ENNReal.ofReal (D.leftClock Q (tau w) w) ∂mu) +
      ∫⁻ w, ENNReal.ofReal |processLeftJump D.N (tau w) w| ∂mu := by
  apply (D.prelocal_cost_le_left_components_add_jump Q hUsual hTau hTauT).trans
  apply (le_lintegral_add _ _).trans
  rw [← lintegral_add_right (fun w => ENNReal.ofReal (D.leftClock Q (tau w) w))
    (D.measurable_sampledJump hTau hTauT)]
  apply lintegral_mono
  intro w
  dsimp only [J1Decomposition.leftClock]
  rw [ENNReal.ofReal_add (Real.sqrt_nonneg _) (D.leftVariation_nonneg (tau w) w)]
  exact le_of_eq (add_right_comm _ _ _)

private theorem sum_lintegral_le (s : Finset Nat) (f : Nat → Ω → ENNReal) :
    (∑ k ∈ s, ∫⁻ w, f k w ∂mu) ≤ ∫⁻ w, ∑ k ∈ s, f k w ∂mu := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

theorem tsum_lintegral_le_of_ae_tsum_le [IsProbabilityMeasure mu]
    (f : Nat → Ω → ENNReal) {b : ENNReal}
    (hBound : ∀ᵐ w ∂mu, (∑' k, f k w) ≤ b) :
    (∑' k, ∫⁻ w, f k w ∂mu) ≤ b := by
  apply ENNReal.summable.tsum_le_of_sum_le
  intro s
  apply (sum_lintegral_le s _).trans
  calc
    _ ≤ ∫⁻ _ : Ω, b ∂mu := by
      apply lintegral_mono_ae
      filter_upwards [hBound] with w hw
      exact (ENNReal.sum_le_tsum s).trans hw
    _ = b := by simp

theorem J1Decomposition.tsum_prelocal_cost_le_of_leftClock_bound
    [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    {Z : Nat → Process Ω} (D : ∀ k, J1Decomposition (Z k) F mu)
    (Q : ∀ k, LocalMartingaleQuadraticVariation (D k).N F mu)
    {tau : Ω → NNReal} {T : NNReal} {b : ENNReal}
    (hTau : IsStoppingTime F (fun w => (tau w : WithTop NNReal)))
    (hTauT : ∀ w, tau w ≤ T)
    (hBound : ∀ᵐ w ∂mu, (∑' k, ENNReal.ofReal ((D k).leftClock (Q k) (tau w) w)) ≤ b) :
    (∑' k, prelocalSemimartingaleJ1 (Z k) F mu (fun w => (tau w : WithTop NNReal))) ≤
      b + ∑' k, ∫⁻ w, ENNReal.ofReal |processLeftJump (D k).N (tau w) w| ∂mu := by
  have hLeft := tsum_lintegral_le_of_ae_tsum_le _ hBound
  calc
    _ ≤ ∑' k, ((∫⁻ w, ENNReal.ofReal ((D k).leftClock (Q k) (tau w) w) ∂mu) +
        ∫⁻ w, ENNReal.ofReal |processLeftJump (D k).N (tau w) w| ∂mu) :=
      ENNReal.tsum_le_tsum (fun k =>
        (D k).prelocal_cost_le_leftClock_add_jump (Q k) hUsual hTau hTauT)
    _ ≤ _ := by rw [ENNReal.tsum_add]; exact add_le_add hLeft le_rfl

theorem J1Decomposition.exists_common_localizers_prelocal_cost_bound
    [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] [F.IsRightContinuous]
    (hUsual : Filtration.UsualConditions mu F)
    {Z : Nat → Process Ω} (D : ∀ k, J1Decomposition (Z k) F mu)
    (Q : ∀ k, LocalMartingaleQuadraticVariation (D k).N F mu)
    (hCap : ∀ n : Nat, (∑' k, ∫⁻ w, min ((D k).clock (Q k) (n : NNReal) w) 1 ∂mu) ≠ ∞) :
    ∃ tau : Nat → Ω → NNReal,
      IsLocalizingSequence F (fun r w => (tau r w : WithTop NNReal)) mu ∧
      (∀ r w, tau r w ≤ ((r + 1 : Nat) : NNReal)) ∧
      ∀ r, (∑' k, prelocalSemimartingaleJ1 (Z k) F mu
        (fun w => (tau r w : WithTop NNReal))) ≤
        (r + 1 : Nat) + ∑' k, ∫⁻ w,
          ENNReal.ofReal |processLeftJump (D k).N (tau r w) w| ∂mu := by
  obtain ⟨U, _, _, _, hLoc, hT, hGood⟩ :=
    J1Decomposition.exists_common_passage_leftClock_bound hUsual D Q hCap
  have hLoc' : IsLocalizingSequence F
      (fun r w => (cadlagAbsolutePassageLocalizerFinite U r w : WithTop NNReal)) mu := by
    simpa only [coe_cadlagAbsolutePassageLocalizerFinite] using hLoc
  refine ⟨cadlagAbsolutePassageLocalizerFinite U, hLoc', hT, ?_⟩
  intro r
  apply J1Decomposition.tsum_prelocal_cost_le_of_leftClock_bound hUsual D Q
    (hLoc'.isStoppingTime r) (hT r)
  filter_upwards [hGood] with w hw
  exact hw.2 r

end FTAPTheorem42
