/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.DoleansDadeYen.Basic
import FTAPTheorem42.Stochastic.Stopping.LocalVariationPassage
import FTAPTheorem42.Stochastic.Martingale.Basic.ZeroInitialLocalMartingaleStopping
import FTAPTheorem42.Stochastic.Martingale.Quadratic.MartingaleQuadraticStoppingConsistency
import FTAPTheorem42.Stochastic.Integral.Elementary.StoppedFiniteGridIntegral

/-! # Common DDY localization with integrable closed variation -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  [F.IsRightContinuous] {X : Process Ω} {c : Real}

omit [F.IsRightContinuous] in
private theorem stopped_martingale_of_le_localSeq {M : Process Ω}
    (hM : LocalMartingale M F mu) (hZero : M 0 = 0)
    (hRight : ∀ omega t, ContinuousWithinAt (M · omega) (Ici t) t)
    (n : Nat) {rho : Ω → WithTop NNReal} (hRho : IsStoppingTime F rho)
    (hLe : ∀ omega, rho omega ≤ hM.localSeq n omega) :
    Martingale (stoppedProcess M rho) F mu := by
  have h := RightContinuousStoppedMartingale.Martingale.stoppedProcess_of_rightContinuous
    (hM.closed_localSeq_of_zero hZero n) hRho
    (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous M hRight)
  rw [stoppedProcess_stoppedProcess_of_le_right hLe] at h
  exact h

structure DoleansDadeYenL1Localization (d : DoleansDadeYenData X F mu c) where
  tau : Nat → Ω → NNReal
  isLocalizingSequence :
    IsLocalizingSequence F (fun n omega => (tau n omega : WithTop NNReal)) mu
  le_horizon : ∀ n omega, tau n omega ≤ cadlagPassageHorizon n
  L_martingale : ∀ n,
    Martingale (stoppedProcess d.L (fun omega => (tau n omega : WithTop NNReal))) F mu
  Q_martingale : ∀ n,
    Martingale (stoppedProcess d.Q (fun omega => (tau n omega : WithTop NNReal))) F mu
  L_bound : ∀ n, ∀ᵐ omega ∂mu, ∀ t,
        |stoppedProcess d.L (fun omega => (tau n omega : WithTop NNReal)) t omega| ≤
          cadlagPassageLevel n + 2 * c
  Q_pre_bound : ∀ n omega s, s < tau n omega → |d.Q s omega| ≤ cadlagPassageLevel n
  variation_integrable : ∀ n, Integrable (fun omega => localVariation d.Q (tau n omega) omega) mu
  variation_bound : ∀ n omega t,
        localVariation (stoppedProcess d.Q (fun omega => (tau n omega : WithTop NNReal))) t omega ≤
          localVariation d.Q (tau n omega) omega
  grid_martingales : ∀ n (N : Nat) (G : ChronologicalGrid NNReal N),
        let L := stoppedProcess d.L (fun omega => (tau n omega : WithTop NNReal))
        let Q := stoppedProcess d.Q (fun omega => (tau n omega : WithTop NNReal))
        Martingale (G.martingaleIntegralProcess Q Q) F mu ∧
        Martingale (G.martingaleIntegralProcess Q L) F mu ∧
        Martingale (G.martingaleIntegralProcess L Q) F mu

/-- Construct all localization fields from the same DDY components. Only
first moments of the terminal FV component are used. -/
theorem DoleansDadeYenData.exists_common_localizer_integrableVariation
    (d : DoleansDadeYenData X F mu c) (hc : 0 ≤ c) :
    Nonempty (DoleansDadeYenL1Localization d) := by
  let A := localVariation d.Q
  have hAAdapted : StronglyAdapted F A :=
    localVariation_stronglyAdapted d.Q_isStronglyAdapted d.Q_rightContinuous
  have hARight : ∀ omega t, ContinuousWithinAt (A · omega) (Ici t) t :=
    localVariation_rightContinuous d.Q_locallyBoundedVariation d.Q_rightContinuous
  have hALeft : ProcessHasLeftLimits A := localVariation_leftLimits d.Q_locallyBoundedVariation
  let rho : Nat → Ω → WithTop NNReal := fun n omega =>
    min (min (d.L_isLocalMartingale.localSeq n omega) (d.Q_isLocalMartingale.localSeq n omega))
      (min (cadlagAbsolutePassageLocalizer d.L n omega) (cadlagAbsolutePassageLocalizer A n omega))
  have hLocal : IsLocalizingSequence F rho mu :=
    (d.L_isLocalMartingale.isLocalizingSequence_localSeq.min
      d.Q_isLocalMartingale.isLocalizingSequence_localSeq).min
      ((cadlagAbsolutePassageLocalizer_isLocalizingSequence
        d.L_isStronglyAdapted d.L_rightContinuous d.L_leftLimits).min
        (cadlagAbsolutePassageLocalizer_isLocalizingSequence hAAdapted hARight hALeft))
  have hHorizon : ∀ n omega, rho n omega ≤ (cadlagPassageHorizon n : WithTop NNReal) :=
    fun _ _ => (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hFinite : ∀ n omega, rho n omega ≠ ⊤ := fun n omega =>
    ne_top_of_le_ne_top WithTop.coe_ne_top (hHorizon n omega)
  let tau : Nat → Ω → NNReal := fun n omega => (rho n omega).untop (hFinite n omega)
  have hCoe : ∀ n, (fun omega => (tau n omega : WithTop NNReal)) = rho n := by
    intro n
    funext omega
    exact WithTop.coe_untop _ (hFinite n omega)
  have hTauHorizon : ∀ n omega, tau n omega ≤ cadlagPassageHorizon n := by
    intro n omega
    apply WithTop.coe_le_coe.mp
    rw [show (tau n omega : WithTop NNReal) = rho n omega from congrFun (hCoe n) omega]
    exact hHorizon n omega
  have hL : ∀ n, Martingale (stoppedProcess d.L (rho n)) F mu := fun n =>
    stopped_martingale_of_le_localSeq d.L_isLocalMartingale d.L_zero d.L_rightContinuous n
      (hLocal.isStoppingTime n) (fun _ => (min_le_left _ _).trans (min_le_left _ _))
  have hQ : ∀ n, Martingale (stoppedProcess d.Q (rho n)) F mu := fun n =>
    stopped_martingale_of_le_localSeq d.Q_isLocalMartingale d.Q_zero d.Q_rightContinuous n
      (hLocal.isStoppingTime n) (fun _ => (min_le_left _ _).trans (min_le_right _ _))
  have hHitA : ∀ n omega, rho n omega ≤ absoluteStrictHittingAfter A (cadlagPassageLevel n) omega :=
    fun _ _ => (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hLBound : ∀ n, ∀ᵐ omega ∂mu, ∀ t,
      |stoppedProcess d.L (rho n) t omega| ≤ cadlagPassageLevel n + 2 * c := by
    intro n
    filter_upwards [d.L_jump_bound] with omega hJump
    exact abs_stoppedProcess_le_add_leftJumpBound_of_le_hitting d.L d.L_leftLimits
      (cadlagPassageLevel n) (2 * c) (mul_nonneg (by norm_num) hc) omega
      (by simpa only [d.L_zero, Pi.zero_apply, abs_zero] using cadlagPassageLevel_nonnegative n)
      (rho n) ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))) hJump
  have hPre : ∀ n omega s, s < tau n omega → |d.Q s omega| ≤ cadlagPassageLevel n := by
    intro n omega s hs
    apply (abs_le_localVariation d.Q_locallyBoundedVariation d.Q_zero omega s).trans
    apply (le_abs_self _).trans
    apply abs_le_of_lt_absoluteStrictHittingAfter A (cadlagPassageLevel n) omega s
    have hs' : (s : WithTop NNReal) < rho n omega := by
      rw [← hCoe n]
      exact WithTop.coe_lt_coe.mpr hs
    exact hs'.trans_le (hHitA n omega)
  have hInt : ∀ n, Integrable (fun omega => A (tau n omega) omega) mu := by
    intro n
    have hEval (Y : Process Ω) : stoppedProcess Y (rho n) (cadlagPassageHorizon n) =
        fun omega => Y (tau n omega) omega := by
      funext omega
      rw [← hCoe n, BoundedMartingaleQuadraticKernel.Data.stoppedProcess_coe_apply,
        min_eq_right (hTauHorizon n omega)]
    have hQInt := (hQ n).integrable (cadlagPassageHorizon n)
    rw [hEval d.Q] at hQInt
    have hAStop :=
      RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
        hAAdapted (hLocal.isStoppingTime n) hARight
    have hAMeas := (hAStop (cadlagPassageHorizon n)).mono
        (F.le (cadlagPassageHorizon n))
    rw [hEval A] at hAMeas
    refine ((integrable_const (2 * cadlagPassageLevel n)).add hQInt.abs).mono'
      hAMeas.aestronglyMeasurable (Eventually.of_forall fun omega => ?_)
    have hNonneg : 0 ≤ A (tau n omega) omega := variationOnFromTo.nonneg_of_le _ _ bot_le
    rw [Real.norm_eq_abs, abs_of_nonneg hNonneg]
    apply localVariation_le_two_mul_add_abs_of_le_passage d.Q_locallyBoundedVariation
      d.Q_leftLimits d.Q_zero (cadlagPassageLevel_nonnegative n) omega
    rw [congrFun (hCoe n) omega]
    exact hHitA n omega
  refine ⟨⟨tau, ?_, hTauHorizon, ?_, ?_, ?_, hPre, hInt, ?_, ?_⟩⟩
  · have hEq : (fun n omega => (tau n omega : WithTop NNReal)) = rho := funext hCoe
    rw [hEq]
    exact hLocal
  · intro n; rw [hCoe n]; exact hL n
  · intro n; rw [hCoe n]; exact hQ n
  · intro n; rw [hCoe n]; exact hLBound n
  · intro n omega t
    have hPath : (fun s => stoppedProcess d.Q
        (fun omega => (tau n omega : WithTop NNReal)) s omega) =
        FiniteVariationStoppedPath.stopAt (d.Q · omega) (tau n omega) := by
      funext s
      exact BoundedMartingaleQuadraticKernel.Data.stoppedProcess_coe_apply d.Q (tau n) s omega
    change variationOnFromTo _ univ 0 t ≤ _
    rw [hPath, FiniteVariationStoppedPath.variationOnFromTo_stopAt]
    exact variationOnFromTo.monotoneOn (d.Q_locallyBoundedVariation omega)
      (mem_univ _) (mem_univ _) (mem_univ _) (min_le_right _ _)
  · intro n N G
    have hTau : IsStoppingTime F (fun omega => (tau n omega : WithTop NNReal)) := by
      rw [hCoe n]
      exact hLocal.isStoppingTime n
    have hLM : Martingale (stoppedProcess d.L
        (fun omega => (tau n omega : WithTop NNReal))) F mu := by
      rw [hCoe n]; exact hL n
    have hQM : Martingale (stoppedProcess d.Q
        (fun omega => (tau n omega : WithTop NNReal))) F mu := by
      rw [hCoe n]; exact hQ n
    refine ⟨G.martingaleIntegralProcess_stopped_isMartingale d.Q d.Q (tau n) hTau
      d.Q_isStronglyAdapted hQM d.Q_rightContinuous (cadlagPassageLevel_nonnegative n) (hPre n),
      G.martingaleIntegralProcess_stopped_isMartingale d.Q d.L (tau n) hTau
        d.Q_isStronglyAdapted hLM d.L_rightContinuous
        (cadlagPassageLevel_nonnegative n) (hPre n), ?_⟩
    apply G.martingaleIntegralProcess_isMartingale_of_stronglyAdapted hQM
      (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous d.Q d.Q_rightContinuous)
      hLM.stronglyAdapted (C := fun _ => cadlagPassageLevel n + 2 * c)
    intro t
    rw [hCoe n]
    filter_upwards [hLBound n] with omega hOmega
    exact hOmega t

end FTAPTheorem42
