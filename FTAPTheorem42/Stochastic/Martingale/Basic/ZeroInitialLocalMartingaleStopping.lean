/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Basic.RightContinuousStoppedMartingale

/-! # Closed localizing stops of zero-initial local martingales -/

open MeasureTheory Set
open scoped NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} {M : Process Ω}

/-- Closed martingale stops of a zero-initial process supply the local
property with mathlib's initial-time indicator convention. -/
theorem LocalMartingale.of_closed_stops_of_zero
    (hM0 : M 0 = 0) (tau : Nat → Ω → WithTop NNReal)
    (hTau : ProbabilityTheory.IsLocalizingSequence F tau mu)
    (hM : ∀ n, Martingale (stoppedProcess M (tau n)) F mu) :
    LocalMartingale M F mu := by
  refine ⟨tau, hTau, fun n => ?_⟩
  have hEq : stoppedProcess (fun t => {omega | ⊥ < tau n omega}.indicator (M t)) (tau n) =
      stoppedProcess M (tau n) := by
    rw [stoppedProcess_indicator_comm']
    funext t omega
    by_cases hpos : omega ∈ {w | ⊥ < tau n w}
    · exact Set.indicator_of_mem hpos _
    · rw [Set.indicator_of_notMem hpos]
      have hz : tau n omega = 0 := le_antisymm (le_of_not_gt hpos) bot_le
      rw [stoppedProcess_eq_of_ge (by rw [hz]; exact bot_le)]
      simp [hz, hM0]
  rw [hEq]
  exact hM n

/-- A zero initial value removes the indicator in the localizing convention. -/
theorem LocalMartingale.closed_localSeq_of_zero
    (hM : LocalMartingale M F mu) (hM0 : M 0 = 0) (n : Nat) :
    Martingale (stoppedProcess M (hM.localSeq n)) F mu := by
  let eta : Ω → WithTop NNReal := hM.localSeq n
  let B : Set Ω := {omega | (⊥ : WithTop NNReal) < eta omega}
  have h : Martingale (stoppedProcess (fun t => B.indicator (M t)) eta) F mu := by
    simpa only [eta, B] using hM.stoppedProcess_localSeq n
  have hEq : stoppedProcess (fun t => B.indicator (M t)) eta = stoppedProcess M eta := by
    rw [stoppedProcess_indicator_comm']
    funext t omega
    by_cases hpos : omega ∈ B
    · exact Set.indicator_of_mem hpos _
    · rw [Set.indicator_of_notMem hpos]
      have hz : eta omega = 0 := le_antisymm (le_of_not_gt hpos) bot_le
      rw [stoppedProcess_eq_of_ge (by rw [hz]; exact bot_le)]
      simp [hz, hM0]
  rw [hEq] at h
  exact h

/-- Arbitrary closed stopping preserves a zero-initial right-continuous
local martingale, including stopping times that can be infinite. -/
theorem LocalMartingale.stoppedProcess_of_zero_of_rightContinuous
    [IsFiniteMeasure mu] [SigmaFiniteFiltration mu F]
    (hM : LocalMartingale M F mu) (hM0 : M 0 = 0)
    (hRight : ∀ w t, ContinuousWithinAt (M · w) (Ici t) t)
    {tau : Ω → WithTop NNReal} (hTau : IsStoppingTime F tau) :
    LocalMartingale (stoppedProcess M tau) F mu := by
  refine LocalMartingale.of_closed_stops_of_zero ?_ hM.localSeq hM.isLocalizingSequence_localSeq ?_
  · funext w
    rw [stoppedProcess_eq_of_le (show ((0 : NNReal) : WithTop NNReal) ≤ tau w from bot_le)]
    exact congrFun hM0 w
  · intro n
    have h := RightContinuousStoppedMartingale.Martingale.stoppedProcess_of_rightContinuous
      (hM.closed_localSeq_of_zero hM0 n) hTau
      (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous M hRight)
    simpa only [stoppedProcess_stoppedProcess, inf_comm] using h

end FTAPTheorem42
