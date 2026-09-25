/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Predictable.LeftContinuousPredictable
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.Stopping

/-!
# Strict first-passage times of left-continuous processes

An adapted left-continuous process has a stopping first strict passage of an
upper level when the filtration is right-continuous.  The proof detects a
passage strictly before a deterministic time on the factorial grids
approaching from the left.  This is the form needed for the active-weight
cutoff in Delbaen--Schachermayer Lemma 4.8.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Topology

namespace FTAPTheorem42

namespace LeftContinuousHittingTime

variable {Ω : Type*} [MeasurableSpace Ω]

/-- First time at which `X` is strictly above `c`. -/
noncomputable def strictHittingAfter
    (X : Process Ω) (c : ℝ) : Ω → WithTop ℝ≥0 :=
  MeasureTheory.hittingAfter X (Ioi c) 0

/-- The measurable left-grid event used to detect a strict passage before
`t`. -/
def gridPassageEvent
    (X : Process Ω) (c : ℝ) (t : ℝ≥0) (r k : ℕ) : Set Ω :=
  if LeftContinuousPredictable.gridPoint r k < t then
    {ω | c < X (LeftContinuousPredictable.gridPoint r k) ω}
  else ∅

theorem measurableSet_gridPassageEvent
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {X : Process Ω} (hX : StronglyAdapted ℱ X)
    (c : ℝ) (t : ℝ≥0) (r k : ℕ) :
    MeasurableSet[ℱ t] (gridPassageEvent X c t r k) := by
  unfold gridPassageEvent
  split_ifs with hqt
  · exact measurableSet_Ioi.preimage
      (hX.stronglyMeasurable_le hqt.le).measurable
  · exact @MeasurableSet.empty Ω (ℱ t)

omit [MeasurableSpace Ω] in
/-- A strict passage before `t` is detected at one factorial-grid time
strictly before `t`. -/
theorem strictHittingAfter_lt_eq_iUnion_gridPassageEvent
    (X : Process Ω)
    (hLeft : ∀ ω s, ContinuousWithinAt (X · ω) (Iic s) s)
    (c : ℝ) (t : ℝ≥0) :
    {ω | strictHittingAfter X c ω < t} =
      ⋃ r : ℕ, ⋃ k : ℕ, gridPassageEvent X c t r k := by
  ext ω
  simp only [mem_ofPred_eq, mem_iUnion]
  constructor
  · intro hτ
    have hτ' : MeasureTheory.hittingAfter X (Ioi c) 0 ω < t := hτ
    rw [MeasureTheory.hittingAfter_lt_iff] at hτ'
    obtain ⟨s, hs, hsX⟩ := hτ'
    by_cases hs0 : s = 0
    · subst s
      refine ⟨0, 0, ?_⟩
      change ω ∈ if LeftContinuousPredictable.gridPoint 0 0 < t then
        {ω | c < X (LeftContinuousPredictable.gridPoint 0 0) ω} else ∅
      have ht0 : (0 : ℝ≥0) < t := hs.2
      simpa [LeftContinuousPredictable.gridPoint, ht0] using hsX
    · have happWithin : Tendsto
          (fun r => LeftContinuousPredictable.approx r s) atTop
          (𝓝[Iic s] s) :=
        tendsto_nhdsWithin_iff.2
          ⟨LeftContinuousPredictable.tendsto_approx s,
            Filter.Eventually.of_forall fun r =>
              LeftContinuousPredictable.approx_le r s⟩
      have hXs : ∀ᶠ r in atTop,
          c < X (LeftContinuousPredictable.approx r s) ω :=
        ((hLeft ω s).tendsto.comp happWithin).eventually
          (Ioi_mem_nhds hsX)
      obtain ⟨r, hrX⟩ := hXs.exists
      let k := LeftContinuousPredictable.leftIndex r s
      refine ⟨r, k, ?_⟩
      change ω ∈ if LeftContinuousPredictable.gridPoint r k < t then
        {ω | c < X (LeftContinuousPredictable.gridPoint r k) ω} else ∅
      have hgrid : LeftContinuousPredictable.gridPoint r k =
          LeftContinuousPredictable.approx r s := rfl
      rw [hgrid, ite_eq_left
        ((LeftContinuousPredictable.approx_lt hs0 r).trans hs.2)]
      exact hrX
  · rintro ⟨r, k, hrk⟩
    unfold gridPassageEvent at hrk
    split_ifs at hrk with hqt
    · change MeasureTheory.hittingAfter X (Ioi c) 0 ω < t
      rw [MeasureTheory.hittingAfter_lt_iff]
      exact ⟨LeftContinuousPredictable.gridPoint r k,
        ⟨bot_le, hqt⟩, hrk⟩
    · exact False.elim hrk

/-- The first strict upper-level passage of a left-continuous adapted process
is a stopping time for a right-continuous filtration. -/
theorem strictHittingAfter_isStoppingTime
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [ℱ.IsRightContinuous]
    {X : Process Ω}
    (hX : StronglyAdapted ℱ X)
    (hLeft : ∀ ω s, ContinuousWithinAt (X · ω) (Iic s) s)
    (c : ℝ) :
    IsStoppingTime ℱ (strictHittingAfter X c) := by
  apply MeasureTheory.isStoppingTime_of_measurableSet_lt_of_isRightContinuous
  intro t
  rw [strictHittingAfter_lt_eq_iUnion_gridPassageEvent X hLeft c t]
  exact MeasurableSet.iUnion fun r => MeasurableSet.iUnion fun k =>
    measurableSet_gridPassageEvent hX c t r k

omit [MeasurableSpace Ω] in
/-- Before the first strict upper passage, the process is at most the level. -/
theorem le_of_lt_strictHittingAfter
    (X : Process Ω) (c : ℝ) (ω : Ω) (t : ℝ≥0)
    (ht : (t : WithTop ℝ≥0) < strictHittingAfter X c ω) :
    X t ω ≤ c := by
  have hnot := MeasureTheory.notMem_of_lt_hittingAfter
    (u := X) (s := Ioi c) (n := (0 : ℝ≥0)) (ω := ω) ht bot_le
  simpa only [mem_Ioi, not_lt] using hnot

omit [MeasurableSpace Ω] in
/-- If the process starts below the level, left continuity prevents a strict
overshoot at the first strict-passage time itself. -/
theorem value_at_strictHittingAfter_le
    (X : Process Ω)
    (hLeft : ∀ s, ContinuousWithinAt (X · ω) (Iic s) s)
    (c : ℝ) (hX0 : X 0 ω ≤ c)
    (hτ : strictHittingAfter X c ω ≠ ⊤) :
    X ((strictHittingAfter X c ω).untop hτ) ω ≤ c := by
  let τ := (strictHittingAfter X c ω).untop hτ
  by_cases hτ0 : τ = 0
  · simpa [τ, hτ0] using hX0
  · by_contra hle
    have hAbove : c < X τ ω := lt_of_not_ge hle
    have happWithin : Tendsto
        (fun r => LeftContinuousPredictable.approx r τ) atTop
        (𝓝[Iic τ] τ) :=
      tendsto_nhdsWithin_iff.2
        ⟨LeftContinuousPredictable.tendsto_approx τ,
          Filter.Eventually.of_forall fun r =>
            LeftContinuousPredictable.approx_le r τ⟩
    have hEarlierAbove : ∀ᶠ r in atTop,
        c < X (LeftContinuousPredictable.approx r τ) ω :=
      ((hLeft τ).tendsto.comp happWithin).eventually
        (Ioi_mem_nhds hAbove)
    obtain ⟨r, hr⟩ := hEarlierAbove.exists
    have hHitLe : strictHittingAfter X c ω ≤
        (LeftContinuousPredictable.approx r τ : WithTop ℝ≥0) :=
      MeasureTheory.hittingAfter_le_of_mem bot_le hr
    have hCoeτ : (τ : WithTop ℝ≥0) = strictHittingAfter X c ω := by
      exact WithTop.coe_untop _ hτ
    rw [← hCoeτ] at hHitLe
    exact (not_le_of_gt (LeftContinuousPredictable.approx_lt hτ0 r))
      (WithTop.coe_le_coe.mp hHitLe)

end LeftContinuousHittingTime

end FTAPTheorem42
