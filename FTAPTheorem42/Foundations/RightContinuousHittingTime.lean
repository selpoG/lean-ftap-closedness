/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.FactorialChronologicalGrid
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.Stopping

/-!
# Strict first-passage times of right-continuous processes

For nonnegative real time, mathlib's discrete hitting-time theorem does not
apply.  A right-continuous adapted process nevertheless has a stopping first
passage into an open upper ray when the filtration is right-continuous.  The
proof represents the event `{τ < t}` by a countable union over the factorial
grids.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace FTAPTheorem42

namespace RightContinuousHittingTime

variable {Ω : Type*} [MeasurableSpace Ω]

/-- First time at which `X` is strictly above `c`. -/
noncomputable def strictHittingAfter
    (X : ℝ≥0 → Ω → ℝ) (c : ℝ) : Ω → WithTop ℝ≥0 :=
  MeasureTheory.hittingAfter X (Ioi c) 0

/-- A point in the countable union of all factorial grids. -/
noncomputable def gridPoint (r k : ℕ) : ℝ≥0 :=
  (k : ℝ≥0) / (r.factorial : ℝ≥0)

/-- The measurable grid event used to detect a strict passage before `t`. -/
def gridPassageEvent
    (X : ℝ≥0 → Ω → ℝ) (c : ℝ) (t : ℝ≥0) (r k : ℕ) : Set Ω :=
  if gridPoint r k < t then {ω | c < X (gridPoint r k) ω} else ∅

theorem measurableSet_gridPassageEvent
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {X : ℝ≥0 → Ω → ℝ} (hX : StronglyAdapted ℱ X)
    (c : ℝ) (t : ℝ≥0) (r k : ℕ) :
    MeasurableSet[ℱ t] (gridPassageEvent X c t r k) := by
  unfold gridPassageEvent
  split_ifs with hqt
  · exact measurableSet_Ioi.preimage
      (hX.stronglyMeasurable_le hqt.le).measurable
  · exact @MeasurableSet.empty Ω (ℱ t)

omit [MeasurableSpace Ω] in
/-- A strict passage before `t` is detected on one factorial-grid point
strictly before `t`. -/
theorem strictHittingAfter_lt_eq_iUnion_gridPassageEvent
    (X : ℝ≥0 → Ω → ℝ)
    (hRight : ∀ ω s, ContinuousWithinAt (X · ω) (Ici s) s)
    (c : ℝ) (t : ℝ≥0) :
    {ω | strictHittingAfter X c ω < t} =
      ⋃ r : ℕ, ⋃ k : ℕ, gridPassageEvent X c t r k := by
  ext ω
  simp only [mem_ofPred_eq, mem_iUnion]
  constructor
  · intro hτ
    have hτ' : MeasureTheory.hittingAfter X (Ioi c) 0 ω < t := hτ
    rw [MeasureTheory.hittingAfter_lt_iff] at hτ'
    rcases hτ' with ⟨s, hs, hsX⟩
    have happWithin : Tendsto
        (fun r => FactorialChronologicalGrid.approx r s) atTop
        (𝓝[Set.Ici s] s) :=
      tendsto_nhdsWithin_iff.2
        ⟨FactorialChronologicalGrid.tendsto_approx s,
          Filter.Eventually.of_forall fun r =>
            FactorialChronologicalGrid.le_approx r s⟩
    have hXt : ∀ᶠ r in atTop,
        c < X (FactorialChronologicalGrid.approx r s) ω :=
      ((hRight ω s).tendsto.comp happWithin).eventually
        (Ioi_mem_nhds hsX)
    have hqt : ∀ᶠ r in atTop,
        FactorialChronologicalGrid.approx r s < t :=
      (FactorialChronologicalGrid.tendsto_approx s).eventually_lt_const hs.2
    obtain ⟨r, hrX, hrt⟩ := (hXt.and hqt).exists
    let k := Nat.ceil (s * (r.factorial : ℝ≥0))
    refine ⟨r, k, ?_⟩
    change ω ∈ if gridPoint r k < t then
      {ω | c < X (gridPoint r k) ω} else ∅
    rw [show gridPoint r k = FactorialChronologicalGrid.approx r s by rfl,
      ite_eq_left hrt]
    exact hrX
  · rintro ⟨r, k, hrk⟩
    unfold gridPassageEvent at hrk
    split_ifs at hrk with hqt
    · change MeasureTheory.hittingAfter X (Ioi c) 0 ω < t
      rw [MeasureTheory.hittingAfter_lt_iff]
      exact ⟨gridPoint r k, ⟨bot_le, hqt⟩, hrk⟩
    · exact False.elim hrk

/-- The first strict upper-level passage of a right-continuous adapted
process is a stopping time for a right-continuous filtration. -/
theorem strictHittingAfter_isStoppingTime
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [ℱ.IsRightContinuous]
    {X : ℝ≥0 → Ω → ℝ}
    (hX : StronglyAdapted ℱ X)
    (hRight : ∀ ω s, ContinuousWithinAt (X · ω) (Ici s) s)
    (c : ℝ) :
    IsStoppingTime ℱ (strictHittingAfter X c) := by
  apply MeasureTheory.isStoppingTime_of_measurableSet_lt_of_isRightContinuous
  intro t
  rw [strictHittingAfter_lt_eq_iUnion_gridPassageEvent X hRight c t]
  exact MeasurableSet.iUnion fun r => MeasurableSet.iUnion fun k =>
    measurableSet_gridPassageEvent hX c t r k

end RightContinuousHittingTime

end FTAPTheorem42
