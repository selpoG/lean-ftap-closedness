/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.Process
import FTAPTheorem42.Foundations.FiniteVariationStoppedPath
import FTAPTheorem42.Foundations.RightContinuousHittingTime
import Mathlib.Probability.Process.Stopping

/-! # HahnStopping shared by the analytic interface and its implementation -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal ProbabilityTheory BigOperators

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace RightContinuousStoppedMartingale

/-- The finite version of `min t τ`, used to sample a process stopped at `τ`. -/
noncomputable def boundedTime
    (t : ℝ≥0) (τ : Ω → WithTop ℝ≥0) : Ω → ℝ≥0 :=
  fun ω => (min (t : WithTop ℝ≥0) (τ ω)).untopA

omit [MeasurableSpace Ω] in
@[simp]
theorem coe_boundedTime
    (t : ℝ≥0) (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    (boundedTime t τ ω : WithTop ℝ≥0) = min (t : WithTop ℝ≥0) (τ ω) := by
  unfold boundedTime
  rw [WithTop.untopA_eq_untop
    (ne_top_of_lt (lt_of_le_of_lt (min_le_left _ _) (WithTop.coe_lt_top t))),
    WithTop.coe_untop]

omit [MeasurableSpace Ω] in
theorem stoppedProcess_path_eq_stopAt_boundedTime
    (A : Process Ω) (tau : Ω -> WithTop NNReal) (T : NNReal)
    (hTauT : forall omega, tau omega <= (T : WithTop NNReal))
    (omega : Ω) :
    (fun t => MeasureTheory.stoppedProcess A tau t omega) =
      FiniteVariationStoppedPath.stopAt (fun t => A t omega)
        (RightContinuousStoppedMartingale.boundedTime T tau omega) := by
  funext t
  unfold MeasureTheory.stoppedProcess FiniteVariationStoppedPath.stopAt
  congr 1
  apply WithTop.coe_eq_coe.mp
  rw [WithTop.coe_min,
    RightContinuousStoppedMartingale.coe_boundedTime,
    min_eq_right (hTauT omega)]
  rw [WithTop.untopA_eq_untop
    (ne_top_of_lt (lt_of_le_of_lt (min_le_left _ _)
      (WithTop.coe_lt_top t))), WithTop.coe_untop]

theorem boundedTime_isStoppingTime
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) (t : ℝ≥0) :
    IsStoppingTime ℱ (fun ω => (boundedTime t τ ω : WithTop ℝ≥0)) := by
  simpa only [coe_boundedTime] using (isStoppingTime_const ℱ t).min hτ

omit [MeasurableSpace Ω] in
theorem boundedTime_le
    (t : ℝ≥0) (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    boundedTime t τ ω ≤ t := by
  exact WithTop.coe_le_coe.mp <| by
    rw [coe_boundedTime]
    exact min_le_left _ _

omit [MeasurableSpace Ω] in
theorem sample_boundedTime_eq_stoppedProcess
    (M : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0)
    (t : ℝ≥0) (ω : Ω) :
    M (boundedTime t τ ω) ω = MeasureTheory.stoppedProcess M τ t ω := by
  rw [MeasureTheory.stoppedProcess, boundedTime]

end RightContinuousStoppedMartingale

/-- First strict passage of `X` below `-r`. -/
noncomputable def lowerStrictHittingAfter
    (X : Process Ω) (r : ℝ) : Ω → WithTop ℝ≥0 :=
  RightContinuousHittingTime.strictHittingAfter (fun t ω => -X t ω) r

omit [MeasurableSpace Ω] in
/-- Strictly before the lower passage, the process is at least `-r`. -/
theorem neg_le_of_lt_lowerStrictHittingAfter
    (X : Process Ω) (r : ℝ) (ω : Ω) (t : ℝ≥0)
    (ht : (t : WithTop ℝ≥0) < lowerStrictHittingAfter X r ω) :
    -r ≤ X t ω := by
  have hnot := MeasureTheory.notMem_of_lt_hittingAfter
    (u := fun t ω => -X t ω) (s := Set.Ioi r) (n := (0 : ℝ≥0))
    (ω := ω) (k := t) ht bot_le
  have hle : -X t ω ≤ r := le_of_not_gt hnot
  linarith

/-- The lower passage of a right-continuous adapted process is a stopping
time. -/
theorem lowerStrictHittingAfter_isStoppingTime
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [ℱ.IsRightContinuous]
    {X : Process Ω} (hX : StronglyAdapted ℱ X)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (r : ℝ) :
    IsStoppingTime ℱ (lowerStrictHittingAfter X r) := by
  apply RightContinuousHittingTime.strictHittingAfter_isStoppingTime
  · intro t
    exact (hX t).neg
  · exact fun ω t => (hXRight ω t).neg

/-- The advantage of a Hahn martingale over the positive part of the
original martingale difference. -/
def hahnMartingaleAdvantage (N M : Process Ω) : Process Ω :=
  fun t ω => N t ω - max (M t ω) 0

/-- Finite closed downside stop for the Hahn improvement. -/
noncomputable def finiteHahnDownsideTime (N M : Process Ω) (δ : Real) (T : NNReal) :
    Ω → NNReal :=
  RightContinuousStoppedMartingale.boundedTime T
    (lowerStrictHittingAfter (hahnMartingaleAdvantage N M) δ)

/-- Stop the improvement on downside failure; otherwise resume the baseline
after `T`, up to a finite terminal horizon `U`. -/
noncomputable def finiteHahnPastedGain (Y V N M : Process Ω)
    (δ : Real) (T U : NNReal) : Process Ω :=
  fun t ω => (Y + V) (min t (finiteHahnDownsideTime N M δ T ω)) ω +
    if (T : WithTop NNReal) < lowerStrictHittingAfter (hahnMartingaleAdvantage N M) δ ω then
      Y (min t U) ω - Y (min t T) ω else 0

omit [MeasurableSpace Ω] in
/-- On survival, the terminal keeps the baseline value and the Hahn bonus. -/
theorem finiteHahnPastedGain_terminal_of_survival (Y V N M : Process Ω)
    {T U : NNReal} (hTU : T ≤ U) (δ : Real) (ω : Ω)
    (he : (T : WithTop NNReal) < lowerStrictHittingAfter (hahnMartingaleAdvantage N M) δ ω) :
    finiteHahnPastedGain Y V N M δ T U U ω = Y U ω + V T ω := by
  have hσ : finiteHahnDownsideTime N M δ T ω = T := by
    apply WithTop.coe_injective
    rw [finiteHahnDownsideTime, RightContinuousStoppedMartingale.coe_boundedTime,
      min_eq_left he.le]
  simp only [finiteHahnPastedGain, hσ, min_eq_right hTU, min_self, ite_eq_left he, Pi.add_apply]
  ring

end FTAPTheorem42
