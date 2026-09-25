/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Martingale.Basic.BoundedStoppingOptionalSampling
import FTAPTheorem42.Stochastic.Decomposition.LargeJump.Process
import FTAPTheorem42.Stochastic.DS.Lemma47.FirstPassage
import FTAPTheorem42.Stochastic.Martingale.Basic.LocalMartingaleAnnouncedJumpControl
import FTAPTheorem42.Stochastic.Predictable.PredictableStoppingGraph
import FTAPTheorem42.Stochastic.Stopping.StoppingTimeRightApproximation

/-!
# Integrability of a finite large-jump boundary sample

At a bounded stopping time below one localizing coordinate, the source
sample is integrable.  If the stopping time is also before an absolute
first passage, the left limit is bounded by the passage level; the finite
large-jump dichotomy then gives an integrable bound for the sampled left
jump of the removed process.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace FiniteLargeJumpProcess

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F] [F.IsRightContinuous]

/-- The left jump of the finite large-jump process is integrable at a
bounded finite stopping time which lies below one localizing coordinate and
below an absolute first passage of the source. -/
theorem integrable_processLeftJump_at_boundedStoppingTime_of_localizing_and_hitting
    {X : Process Ω} {c : Real} {T H : NNReal} {r : Real}
    (hX : LocalMartingale X F mu)
    (hXAdapted : StronglyAdapted F X)
    (hXRight : ∀ omega t,
      ContinuousWithinAt (X · omega) (Ici t) t)
    (hXLeft : ProcessHasLeftLimits X)
    (hXZero : X 0 = 0)
    (hc : 0 < c) (hr : 0 ≤ r)
    {tau : Ω → NNReal}
    (hTau : IsStoppingTime F
      (fun omega => (tau omega : WithTop NNReal)))
    (k : Nat)
    (hTauLocal : ∀ omega,
      (tau omega : WithTop NNReal) ≤ hX.localSeq k omega)
    (hTauHit : ∀ omega,
      (tau omega : WithTop NNReal) ≤ absoluteStrictHittingAfter X r omega)
    (hTauH : ∀ omega, tau omega ≤ H) :
    Integrable
      (fun omega => processLeftJump
        (FiniteLargeJumpProcess.process X c T) (tau omega) omega) mu := by
  let rho : Ω → WithTop NNReal := hX.localSeq k
  let L : Process Ω := localizingStoppedProcess X rho
  have hL : Martingale L F mu := by
    simpa only [L, rho, localizingStoppedProcess] using
      hX.stoppedProcess_localSeq k
  have hLRight : ∀ omega t,
      ContinuousWithinAt (L · omega) (Ici t) t := by
    simpa only [L] using
      localizingStoppedProcess_rightContinuous X rho hXRight
  have hLInt : Integrable (fun omega => L (tau omega) omega) mu :=
    Martingale.integrable_sample_of_boundedStoppingTime
      hL hTau hTauH hLRight
  have hSampleEq :
      (fun omega => L (tau omega) omega) =
        (fun omega => X (tau omega) omega) := by
    funext omega
    by_cases hTauZero : tau omega = 0
    · have hLZero : L 0 omega = 0 := by
        dsimp only [L, localizingStoppedProcess]
        rw [MeasureTheory.stoppedProcess_eq_of_le bot_le]
        by_cases hRho : (⊥ : WithTop NNReal) < rho omega
        · have hOmegaRho : omega ∈
              {omega | (⊥ : WithTop NNReal) < rho omega} := hRho
          rw [Set.indicator_of_mem hOmegaRho]
          simpa using congrFun hXZero omega
        · have hOmegaRho : omega ∉
              {omega | (⊥ : WithTop NNReal) < rho omega} := hRho
          rw [Set.indicator_of_notMem hOmegaRho]
      rw [hTauZero, hLZero]
      simpa using (congrFun hXZero omega).symm
    · have hTauPos : 0 < tau omega := (pos_iff_ne_zero).2 hTauZero
      have hTauRho : (tau omega : WithTop NNReal) ≤ rho omega := by
        simpa only [rho] using hTauLocal omega
      have hBotRho : (⊥ : WithTop NNReal) < rho omega :=
        (WithTop.coe_lt_coe.mpr hTauPos).trans_le hTauRho
      have hOmegaRho : omega ∈
          {omega | (⊥ : WithTop NNReal) < rho omega} := hBotRho
      dsimp only [L, localizingStoppedProcess]
      rw [MeasureTheory.stoppedProcess_eq_of_le hTauRho,
        Set.indicator_of_mem hOmegaRho]
  have hXInt : Integrable (fun omega => X (tau omega) omega) mu := by
    rw [← hSampleEq]
    exact hLInt
  let A : Process Ω := FiniteLargeJumpProcess.process X c T
  have hAAdapted : StronglyAdapted F A := by
    dsimp only [A]
    exact FiniteLargeJumpProcess.stronglyAdapted_process
      hXAdapted hXRight hXLeft hc T
  have hARight : ∀ omega t,
      ContinuousWithinAt (A · omega) (Ici t) t := by
    dsimp only [A]
    exact FiniteLargeJumpProcess.process_rightContinuous hXRight hXLeft hc
  have hALeft : ProcessHasLeftLimits A := by
    dsimp only [A]
    exact FiniteLargeJumpProcess.process_hasLeftLimits hXRight hXLeft hc
  have hAValueMeas : StronglyMeasurable
      (fun omega => A (tau omega) omega) :=
    StoppingTimeRightApproximation.stronglyMeasurable_sample_of_boundedStoppingTime
      hAAdapted hTau hTauH hARight
  have hALeftPred : IsStronglyPredictable F
      (fun t omega => Function.leftLim (A · omega) t) :=
    ProcessHasLeftLimits.stronglyPredictable_leftLim hALeft hAAdapted
  have hGraphMeas :
      predictableGraphMeasurableSpace F tau ≤
        (inferInstance : MeasurableSpace Ω) :=
    IsStoppingTime.predictableGraphMeasurableSpace_le hTau
  have hALeftValueMeas : StronglyMeasurable
      (fun omega => Function.leftLim (A · omega) (tau omega)) :=
    (IsStronglyPredictable.stronglyMeasurable_sampledGraph
      hALeftPred tau).mono hGraphMeas
  have hBoundaryMeas : AEStronglyMeasurable
      (fun omega => processLeftJump A (tau omega) omega) mu := by
    change AEStronglyMeasurable
      (fun omega => A (tau omega) omega -
        Function.leftLim (fun s => A s omega) (tau omega)) mu
    exact (hAValueMeas.sub hALeftValueMeas).aestronglyMeasurable
  have hBoundaryBound : ∀ omega,
      |processLeftJump A (tau omega) omega| ≤
        |X (tau omega) omega| + r := by
    intro omega
    by_cases hTauZero : tau omega = 0
    · have hNotLarge : (0 : NNReal) ∉
          largeJumpTimeSet (fun s => X s omega) c T := by
        simp [largeJumpTimeSet]
      have hJumpZero : processLeftJump A (tau omega) omega = 0 := by
        rw [hTauZero]
        dsimp only [A]
        exact FiniteLargeJumpProcess.process_leftJump_eq_of_not_large
          hXRight hXLeft hc hNotLarge
      rw [hJumpZero, abs_zero]
      exact add_nonneg (abs_nonneg _) hr
    · have hTauPos : 0 < tau omega := (pos_iff_ne_zero).2 hTauZero
      by_cases hLarge : tau omega ∈
          largeJumpTimeSet (fun s => X s omega) c T
      · have hLeftBound :
            |Function.leftLim (fun s => X s omega) (tau omega)| ≤ r := by
          let : NeBot (𝓝[<] tau omega) :=
            nhdsLT_neBot_of_exists_lt ⟨0, hTauPos⟩
          apply le_of_tendsto (hXLeft omega (tau omega)).abs
          filter_upwards [self_mem_nhdsWithin] with s hs
          exact abs_le_of_lt_absoluteStrictHittingAfter X r omega s
            ((WithTop.coe_lt_coe.mpr hs).trans_le (hTauHit omega))
        have hJumpEq :
            processLeftJump A (tau omega) omega =
              processLeftJump X (tau omega) omega := by
          dsimp only [A]
          exact FiniteLargeJumpProcess.process_leftJump_eq_of_large
            hXRight hXLeft hc hLarge
        calc
          |processLeftJump A (tau omega) omega| =
              |processLeftJump X (tau omega) omega| := by rw [hJumpEq]
          _ = |X (tau omega) omega -
              Function.leftLim (fun s => X s omega) (tau omega)| := rfl
          _ ≤ |X (tau omega) omega| +
              |Function.leftLim (fun s => X s omega) (tau omega)| :=
            abs_sub _ _
          _ ≤ |X (tau omega) omega| + r :=
            add_le_add le_rfl hLeftBound
      · have hJumpZero : processLeftJump A (tau omega) omega = 0 := by
          dsimp only [A]
          exact FiniteLargeJumpProcess.process_leftJump_eq_of_not_large
            hXRight hXLeft hc hLarge
        rw [hJumpZero, abs_zero]
        exact add_nonneg (abs_nonneg _) hr
  let G : Ω → Real := fun omega => |X (tau omega) omega| + r
  have hGInt : Integrable G mu := by
    change Integrable
      ((fun omega => |X (tau omega) omega|) + fun _ => r) mu
    simpa only [Real.norm_eq_abs] using
      hXInt.norm.add (integrable_const r)
  apply hGInt.mono' hBoundaryMeas
  filter_upwards [] with omega
  simpa only [G, Real.norm_eq_abs] using hBoundaryBound omega

end FiniteLargeJumpProcess

end FTAPTheorem42
