/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Stopping.CadlagPassageLocalizer
import FTAPTheorem42.Stochastic.Martingale.Quadratic.MartingaleQuadraticLocalizingScheduleRoot
import FTAPTheorem42.Stochastic.Topology.Prelocal.QuadraticCore
import FTAPTheorem42.Stochastic.DS.Lemma47.StoppedMartingale
import FTAPTheorem42.Stochastic.Martingale.Basic.ZeroInitialLocalMartingaleStopping

/-!
# Quadratic schedules for bounded-jump local martingales

Refine the local martingale's own localizing sequence with the canonical
absolute passages. The zero initial value removes the time-zero indicator
in the local martingale convention. The resulting closed stops are true
martingales and have a deterministic terminal square-integrable majorant.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal ProbabilityTheory

namespace FTAPTheorem42.LocalMartingaleQuadratic

open SIntegrableFiniteVariationBridge SIntegrableProcessStoppingCalculus

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  {M : Process Ω}

/-- A zero-initial càdlàg local martingale with horizon-wise deterministic
jump bounds supplies a quadratic schedule. The schedule refines both the
martingale localizers and the absolute passages; no true-martingale property
of the unstopped source is assumed. -/
theorem exists_boundedJumpLocalMartingaleQuadraticSchedule
    [F.IsRightContinuous]
    (hUsual : Filtration.UsualConditions mu F)
    (hM : LocalMartingale M F mu)
    (hMAdapted : StronglyAdapted F M)
    (hMRight : ∀ omega t, ContinuousWithinAt (M · omega) (Ici t) t)
    (hMLeft : ProcessHasLeftLimits M) (hM0 : M 0 = 0)
    (jumpBound : Nat → Real) (hJumpNonnegative : ∀ n, 0 ≤ jumpBound n)
    (hJump : ∀ n, ∀ᵐ omega ∂mu, ∀ t, t ≤ cadlagPassageHorizon n →
      |processLeftJump M t omega| ≤ jumpBound n) :
    Nonempty (LocalMartingaleQuadraticSchedule (F := F) (mu := mu) (M := M)) := by
  let rho : Nat → Ω → WithTop NNReal := fun n omega =>
    min (hM.localSeq n omega) (cadlagAbsolutePassageLocalizer M n omega)
  have hLocalizing : ProbabilityTheory.IsLocalizingSequence F rho mu :=
    hM.isLocalizingSequence_localSeq.min
      (cadlagAbsolutePassageLocalizer_isLocalizingSequence hMAdapted hMRight hMLeft)
  have hLeHorizon : ∀ n omega, rho n omega ≤ (cadlagPassageHorizon n : WithTop NNReal) := by
    intro n omega
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hFinite : ∀ n omega, rho n omega ≠ ⊤ := by
    intro n omega
    exact ne_top_of_le_ne_top WithTop.coe_ne_top (hLeHorizon n omega)
  let tau : Nat → Ω → NNReal := fun n omega => (rho n omega).untop (hFinite n omega)
  have hCoe : ∀ n, (fun omega => (tau n omega : WithTop NNReal)) = rho n := by
    intro n
    funext omega
    exact WithTop.coe_untop _ (hFinite n omega)
  have hCoordinate : ∀ n, Nonempty (SquareIntegrableMartingaleQuadraticJ1Certificate F mu
      (MeasureTheory.stoppedProcess M (rho n)) (cadlagPassageHorizon n)) := by
    intro n
    have hRhoStop := hLocalizing.isStoppingTime n
    have hRhoLocal : ∀ omega, rho n omega ≤ hM.localSeq n omega :=
      fun _ => min_le_left _ _
    have hRhoHit : ∀ omega,
        rho n omega ≤ absoluteStrictHittingAfter M (cadlagPassageLevel n) omega :=
      fun _ => (min_le_right _ _).trans (min_le_left _ _)
    have hStoppedMartingale : Martingale (MeasureTheory.stoppedProcess M (rho n)) F mu := by
      have hStop := RightContinuousStoppedMartingale.Martingale.stoppedProcess_of_rightContinuous
        (hM.closed_localSeq_of_zero hM0 n) hRhoStop
        (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous M hMRight)
      rw [MeasureTheory.stoppedProcess_stoppedProcess_of_le_right hRhoLocal] at hStop
      exact hStop
    have hBound : ∀ᵐ omega ∂mu, ∀ t,
        |MeasureTheory.stoppedProcess M (rho n) t omega| ≤
          cadlagPassageLevel n + jumpBound n := by
      filter_upwards [hJump n] with omega hOmega
      apply abs_stoppedProcess_le_add_leftJumpBound_of_le_hitting_of_le_horizon
        M hMLeft (cadlagPassageLevel n) (jumpBound n) (hJumpNonnegative n) omega
        ?_ (rho n) (hRhoHit omega) (cadlagPassageHorizon n) (hLeHorizon n omega) hOmega
      simpa only [hM0, Pi.zero_apply, abs_zero] using cadlagPassageLevel_nonnegative n
    have hMem : MemLp (MeasureTheory.stoppedProcess M (rho n) (cadlagPassageHorizon n))
        (2 : ENNReal) mu := by
      apply MemLp.of_le (p := (2 : ENNReal)) (μ := mu)
        (memLp_const (p := (2 : ENNReal)) (μ := mu) (cadlagPassageLevel n + jumpBound n))
        ((hStoppedMartingale.stronglyAdapted _).mono (F.le _)).aestronglyMeasurable
      filter_upwards [hBound] with omega hOmega
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (add_nonneg (cadlagPassageLevel_nonnegative n) (hJumpNonnegative n))]
        using hOmega (cadlagPassageHorizon n)
    exact exists_squareIntegrableMartingaleQuadraticJ1Certificate hUsual hStoppedMartingale
      (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous M hMRight) hMem
  refine ⟨{
    localizer := tau
    horizon := cadlagPassageHorizon
    isLocalizingSequence := by
      have hTauEq : (fun n omega => (tau n omega : WithTop NNReal)) = rho := funext hCoe
      rw [hTauEq]
      exact hLocalizing
    localizer_le_horizon := by
      intro n omega
      apply WithTop.coe_le_coe.mp
      rw [congrFun (hCoe n) omega]
      exact hLeHorizon n omega
    coordinate := by
      intro n
      rw [hCoe n]
      exact Classical.choice (hCoordinate n) }⟩

end FTAPTheorem42.LocalMartingaleQuadratic
