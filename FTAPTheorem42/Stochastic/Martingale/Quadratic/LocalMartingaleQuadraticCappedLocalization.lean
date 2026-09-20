/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.DoleansDadeYen.Quadratic

/-! # Intrinsic quadratic variation commutes with arbitrary closed stopping -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped NNReal

open RightContinuousStoppedMartingale

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  {X : Process Ω}

/-- All semantic fields belong to the same closed-stopped variation.
No boundedness or finiteness of the stopping time is imposed. -/
noncomputable def LocalMartingaleQuadraticVariation.stopped
    (Q : LocalMartingaleQuadraticVariation X F mu)
    (hXRight : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hXLeft : ProcessHasLeftLimits X) (hXZero : X 0 = 0)
    {tau : Ω → WithTop NNReal} (hTau : IsStoppingTime F tau) :
    LocalMartingaleQuadraticVariation (stoppedProcess X tau) F mu := by
  have hMono : ∀ w, Monotone (stoppedProcess Q.variation tau · w) := by
    intro w s t hst
    change Q.variation (boundedTime s tau w) w ≤ Q.variation (boundedTime t tau w) w
    apply Q.monotone w
    apply WithTop.coe_le_coe.mp
    rw [coe_boundedTime, coe_boundedTime]
    exact min_le_min_right _ (WithTop.coe_le_coe.mpr hst)
  refine {
    variation := stoppedProcess Q.variation tau
    stronglyAdapted := StronglyAdapted.stoppedProcess_of_rightContinuous
      Q.stronglyAdapted hTau Q.rightContinuous
    rightContinuous := stoppedProcess_rightContinuous Q.variation Q.rightContinuous
    leftLimits := Q.leftLimits.stoppedProcess tau
    locallyBoundedVariation := fun w => ((hMono w).monotoneOn univ).locallyBoundedVariationOn
    monotone := hMono
    zero := ?_
    jump_sq := ?_
    squareResidual := ?_ }
  · funext w
    rw [stoppedProcess_eq_of_le (show ((0 : NNReal) : WithTop NNReal) ≤ tau w from bot_le)]
    exact congrFun Q.zero w
  · filter_upwards [Q.jump_sq] with w hw
    intro t
    by_cases ht : (t : WithTop NNReal) ≤ tau w
    · rw [processLeftJump_stoppedProcess_eq_of_le Q.variation Q.leftLimits tau t w ht,
        processLeftJump_stoppedProcess_eq_of_le X hXLeft tau t w ht]
      exact hw t
    · rw [processLeftJump_stoppedProcess_eq_zero_of_lt Q.variation tau t w (lt_of_not_ge ht),
        processLeftJump_stoppedProcess_eq_zero_of_lt X tau t w (lt_of_not_ge ht)]
      norm_num
  · have hZero : (fun w => X 0 w ^ 2 - Q.variation 0 w) = 0 := by
      funext w
      simp only [hXZero, Q.zero, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), sub_self]
    have h := Q.squareResidual.stoppedProcess_of_zero_of_rightContinuous hZero
      (fun w t => ((hXRight w t).pow 2).sub (Q.rightContinuous w t)) hTau
    exact h

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## Removing a common localization from capped quadratic-root convergence -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  [IsFiniteMeasure mu]

theorem LocalMartingaleQuadraticVariation.tendsto_capped_root_of_localized
    {X : Nat → Process Ω} (P : ∀ n, LocalMartingaleQuadraticVariation (X n) F mu)
    {tau : Nat → Ω → NNReal}
    (hLoc : IsLocalizingSequence F (fun r w => (tau r w : WithTop NNReal)) mu)
    (hLimit : ∀ r, Tendsto (fun n => ∫⁻ w,
      ENNReal.ofReal (Real.sqrt ((P n).variation (tau r w) w)) ∂mu) atTop (𝓝 0))
    (T : NNReal) :
    Tendsto (fun n => ∫⁻ w, min (ENNReal.ofReal (Real.sqrt ((P n).variation T w))) 1 ∂mu)
      atTop (𝓝 0) := by
  classical
  let bad := fun r => {w | (tau r w : WithTop NNReal) ≤ (T : WithTop NNReal)}
  let g := fun r => (bad r).indicator (fun _ => (1 : ENNReal))
  have hMeas (r : Nat) : Measurable (g r) :=
    measurable_const.indicator (F.le T _ ((hLoc.isStoppingTime r).measurableSet_le T))
  have hG : Tendsto (fun r => ∫⁻ w, g r w ∂mu) atTop (𝓝 0) := by
    have hAE : ∀ᵐ w ∂mu, Tendsto (fun r => g r w) atTop (𝓝 0) := by
      filter_upwards [hLoc.tendsto_top] with w hw
      apply tendsto_const_nhds.congr'
      filter_upwards [(WithTop.tendsto_nhds_top_iff _).mp hw T] with r hr
      have hNot : w ∉ bad r := not_le.mpr hr
      exact (Set.indicator_of_notMem hNot (fun _ : Ω => (1 : ENNReal))).symm
    have h := tendsto_lintegral_of_dominated_convergence' (fun _ : Ω => (1 : ENNReal))
      (fun r => (hMeas r).aemeasurable)
      (fun r => Eventually.of_forall (fun w =>
        Set.indicator_le_self' (fun _ _ => bot_le) w))
      (by simp) hAE
    simpa only [lintegral_zero] using h
  have hBound (n r : Nat) :
      (∫⁻ w, min (ENNReal.ofReal (Real.sqrt ((P n).variation T w))) 1 ∂mu) ≤
        (∫⁻ w, ENNReal.ofReal (Real.sqrt ((P n).variation (tau r w) w)) ∂mu) +
          ∫⁻ w, g r w ∂mu := by
    rw [← lintegral_add_right _ (hMeas r)]
    apply lintegral_mono
    intro w
    by_cases hw : w ∈ bad r
    · simp only [g, Set.indicator_of_mem hw]
      exact (min_le_right _ _).trans (le_add_left le_rfl)
    · have ht : T ≤ tau r w :=
        (WithTop.coe_lt_coe.mp (not_le.mp hw)).le
      apply (min_le_left _ _).trans
      exact (ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ((P n).monotone w ht))).trans
        (le_add_right le_rfl)
  apply ENNReal.tendsto_nhds_zero.mpr
  intro e he
  have hHalf : 0 < e / 2 := ENNReal.div_pos he.ne' (by norm_num)
  obtain ⟨r, hr⟩ := (ENNReal.tendsto_nhds_zero.mp hG (e / 2) hHalf).exists
  filter_upwards [ENNReal.tendsto_nhds_zero.mp (hLimit r) (e / 2) hHalf] with n hn
  exact (hBound n r).trans ((add_le_add hn hr).trans_eq (ENNReal.add_halves e))

end FTAPTheorem42
