/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Quadratic.MartingaleQuadraticJump
import FTAPTheorem42.Stochastic.Martingale.Quadratic.BoundedMartingaleQuadraticKernelTerminalRootLimit
import FTAPTheorem42.Stochastic.Decomposition.Compensator.SignedProjectionCore
import FTAPTheorem42.Stochastic.Process.NullSetProcessRegularization
import FTAPTheorem42.Stochastic.Martingale.Basic.ZeroInitialLocalMartingaleStopping

/-! # Rigidity of almost surely continuous locally finite-variation local martingales -/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped NNReal

namespace FTAPTheorem42

open PredictableFiniteVariationLocalMartingale

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  [F.IsRightContinuous]

private theorem zero_of_ae_continuous_boundedVariation
    (hUsual : Filtration.UsualConditions mu F) {A : Process Ω}
    (hA : LocalMartingale A F mu) (hAdapted : StronglyAdapted F A)
    (hRight : ∀ w t, ContinuousWithinAt (A · w) (Ici t) t)
    (hBV : ∀ w, BoundedVariationOn (A · w) univ)
    (hContinuous : ∀ᵐ w ∂mu, Continuous (A · w)) (hZero : A 0 = 0) :
    ProcessIndistinguishable mu A (fun _ _ => 0) := by
  let B : Process Ω := fun t w => Function.leftLim (A · w) t
  have hLeft : ProcessHasLeftLimits A := fun w t => (hBV w).tendsto_leftLim t
  have hPred : IsStronglyPredictable F B := hLeft.stronglyPredictable_leftLim hAdapted
  have hBA : ProcessIndistinguishable mu B A := by
    filter_upwards [hContinuous] with w hw
    exact fun t => hw.continuousWithinAt.leftLim_eq
  have hRegular : ∀ᵐ w ∂mu,
      (∀ t, ContinuousWithinAt (B · w) (Ici t) t) ∧ BoundedVariationOn (B · w) univ := by
    filter_upwards [hBA] with w hw
    have hPath : (B · w) = (A · w) := funext hw
    rw [hPath]
    exact ⟨hRight w, hBV w⟩
  obtain ⟨P, hPPred, hPRight, hPBV, hPB⟩ :=
    ProcessNullSetRegularization.exists_predictable_rightContinuous_boundedVariation_version
      hUsual hPred hRegular
  have hPA : ProcessIndistinguishable mu P A := hPB.trans hBA
  have hP := hA.congr_indistinguishable hPPred.stronglyAdapted hPRight hPA.symm
  have hInitial := indistinguishable_initial_of_predictableFiniteVariationLocalMartingale
      hUsual P hP hPPred hPRight hPBV
  filter_upwards [hPA, hInitial] with w hw hi
  intro t
  calc
    A t w = P t w := (hw t).symm
    _ = P 0 w := hi t
    _ = A 0 w := hw 0
    _ = 0 := congrFun hZero w

theorem LocalMartingale.indistinguishable_zero_of_ae_continuous_locallyBoundedVariation
    (hUsual : Filtration.UsualConditions mu F) {A : Process Ω}
    (hA : LocalMartingale A F mu) (hAdapted : StronglyAdapted F A)
    (hRight : ∀ w t, ContinuousWithinAt (A · w) (Ici t) t)
    (hBV : ∀ w, LocallyBoundedVariationOn (A · w) univ)
    (hContinuous : ∀ᵐ w ∂mu, Continuous (A · w)) (hZero : A 0 = 0) :
    ProcessIndistinguishable mu A (fun _ _ => 0) := by
  have hStopped (T : NNReal) : ProcessIndistinguishable mu
      (stoppedProcess A (fun _ => (T : WithTop NNReal))) (fun _ _ => 0) := by
    let Y := stoppedProcess A (fun _ => (T : WithTop NNReal))
    have hYZero : Y 0 = 0 := by
      funext w
      change A (min 0 T) w = 0
      rw [min_eq_left (show (0 : NNReal) ≤ T from bot_le)]
      exact congrFun hZero w
    have hY : LocalMartingale Y F mu := by
      apply LocalMartingale.of_closed_stops_of_zero hYZero hA.localSeq
        hA.isLocalizingSequence_localSeq
      intro n
      have h := RightContinuousStoppedMartingale.Martingale.stoppedProcess_of_rightContinuous
        (hA.closed_localSeq_of_zero hZero n) (isStoppingTime_const F T)
        (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous A hRight)
      simpa only [Y, stoppedProcess_stoppedProcess, inf_comm] using h
    apply zero_of_ae_continuous_boundedVariation hUsual hY
      (RightContinuousStoppedMartingale.StronglyAdapted.stoppedProcess_of_rightContinuous
        hAdapted (isStoppingTime_const F T) hRight)
      (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous A hRight)
    · intro w
      have h := FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn
        (hBV w) T
      change BoundedVariationOn (fun s => A (min s T) w) univ at h
      simpa only [Y, stoppedProcess_const_apply] using h
    · filter_upwards [hContinuous] with w hw
      change Continuous (fun s => A (min s T) w)
      exact hw.comp (continuous_id.min continuous_const)
    · exact hYZero
  filter_upwards [ae_all_iff.mpr (fun n : Nat => hStopped n)] with w hw
  intro t
  have h := hw (Nat.ceil t) t
  simpa only [stoppedProcess_const_apply,
    min_eq_left (Nat.le_ceil t)] using h

end FTAPTheorem42
