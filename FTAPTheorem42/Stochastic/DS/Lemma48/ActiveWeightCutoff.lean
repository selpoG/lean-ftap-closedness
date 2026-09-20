/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Stopping.LeftContinuousHittingTime
import FTAPTheorem42.Stochastic.DS.Lemma48.PostStoppingTail

/-!
# Active-weight cutoff for Lemma 4.8

The convex tail strategy of Lemma 4.8 is admissible only while the total
weight of components whose individual first passages have occurred remains
small.  This module proves that active-weight process is adapted and
left-continuous, constructs its first strict passage as a stopping time, and
stops the actual tail strategy there.  The resulting strategy inherits the
pathwise lower bound required by the Lemma 4.7 contradiction.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal Topology

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- The indicator of the interval strictly after an extended time is
left-continuous. -/
theorem afterExtendedTimeIndicator_leftContinuous
    (τ : WithTop ℝ≥0) (t : ℝ≥0) :
    ContinuousWithinAt
      (fun s : ℝ≥0 => if τ < (s : WithTop ℝ≥0) then (1 : ℝ) else 0)
      (Iic t) t := by
  by_cases ht : τ < (t : WithTop ℝ≥0)
  · have hτne : τ ≠ ⊤ := ne_top_of_lt ht
    let u := τ.untop hτne
    have hτcoe : (u : WithTop ℝ≥0) = τ := WithTop.coe_untop τ hτne
    have hut : u < t := by
      rw [← hτcoe] at ht
      exact WithTop.coe_lt_coe.mp ht
    rw [ContinuousWithinAt, ite_eq_left ht]
    apply tendsto_const_nhds.congr'
    have hIoi : ∀ᶠ s in 𝓝[Iic t] t, s ∈ Ioi u :=
      Filter.Eventually.filter_mono inf_le_left (Ioi_mem_nhds hut)
    filter_upwards [hIoi] with s hsu
    rw [ite_eq_left]
    rw [← hτcoe]
    exact WithTop.coe_lt_coe.mpr hsu
  · rw [ContinuousWithinAt, ite_eq_right ht]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [ite_eq_right]
    intro hτs
    exact ht (hτs.trans_le (WithTop.coe_le_coe.mpr hs))

namespace SIntegrableProcessStoppingCalculus

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  [ℱ.IsRightContinuous]
  {μ : Measure Ω} [IsFiniteMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

omit [IsFiniteMeasure μ] [SigmaFiniteFiltration μ ℱ] in
/-- The active-weight process is adapted. -/
theorem lemma48ActiveMass_isStronglyAdapted
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c : ℝ) :
    StronglyAdapted ℱ (lemma48ActiveMass H weight n c) := by
  intro t
  change StronglyMeasurable[ℱ t] (fun ω =>
    ∑ i ∈ Finset.range n, weight i *
      if lemma48FirstPassage (H i) c ω <
        (t : WithTop ℝ≥0) then (1 : ℝ) else 0)
  apply Finset.stronglyMeasurable_fun_sum
  intro i hi
  have hIndicator : StronglyMeasurable[ℱ t]
      (fun ω => if lemma48FirstPassage (H i) c ω <
        (t : WithTop ℝ≥0) then (1 : ℝ) else 0) := by
    exact StronglyMeasurable.ite
      ((lemma48FirstPassage_isStoppingTime (H i) c).measurableSet_lt t)
      stronglyMeasurable_const stronglyMeasurable_const
  exact stronglyMeasurable_const.mul hIndicator

omit [ℱ.IsRightContinuous] [IsFiniteMeasure μ]
  [SigmaFiniteFiltration μ ℱ] in
/-- Every path of the active-weight process is left-continuous. -/
theorem lemma48ActiveMass_isLeftContinuous
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c : ℝ) :
    ∀ ω t, ContinuousWithinAt
      (lemma48ActiveMass H weight n c · ω) (Iic t) t := by
  intro ω t
  induction n with
  | zero =>
      simpa [lemma48ActiveMass] using
        (continuousWithinAt_const :
          ContinuousWithinAt (fun _ : ℝ≥0 => (0 : ℝ)) (Iic t) t)
  | succ n ih =>
      have hTerm : ContinuousWithinAt
          (fun s : ℝ≥0 => weight n *
            if lemma48FirstPassage (H n) c ω <
              (s : WithTop ℝ≥0) then (1 : ℝ) else 0)
          (Iic t) t :=
        continuousWithinAt_const.mul
          (afterExtendedTimeIndicator_leftContinuous
            (lemma48FirstPassage (H n) c ω) t)
      convert ih.add hTerm using 1
      ext s
      simp only [lemma48ActiveMass, Finset.sum_range_succ, Pi.add_apply]

/-- First strict passage of the active weight above `δ`. -/
noncomputable def lemma48ActiveMassCutoff
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c δ : ℝ) : Ω → WithTop ℝ≥0 :=
  LeftContinuousHittingTime.strictHittingAfter
    (lemma48ActiveMass H weight n c) δ

omit [IsFiniteMeasure μ] [SigmaFiniteFiltration μ ℱ] in
theorem lemma48ActiveMassCutoff_isStoppingTime
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c δ : ℝ) :
    IsStoppingTime ℱ (lemma48ActiveMassCutoff H weight n c δ) :=
  LeftContinuousHittingTime.strictHittingAfter_isStoppingTime
    (lemma48ActiveMass_isStronglyAdapted H weight n c)
    (lemma48ActiveMass_isLeftContinuous H weight n c) δ

omit [ℱ.IsRightContinuous] [IsFiniteMeasure μ]
  [SigmaFiniteFiltration μ ℱ] in
@[simp]
theorem lemma48ActiveMass_zero
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c : ℝ) (ω : Ω) :
    lemma48ActiveMass H weight n c 0 ω = 0 := by
  rw [lemma48ActiveMass]
  apply Finset.sum_eq_zero
  intro i hi
  simp

omit [ℱ.IsRightContinuous] [IsFiniteMeasure μ]
  [SigmaFiniteFiltration μ ℱ] in
/-- Stopping the active-weight process at its first strict upper passage
keeps it at most `δ`, including at the cutoff time itself. -/
theorem lemma48ActiveMass_stopped_le
    (H : ℕ → SIntegrableStrategy D) (weight : ℕ → ℝ)
    (n : ℕ) (c δ : ℝ) (hδ : 0 ≤ δ) :
    ∀ t ω, MeasureTheory.stoppedProcess
      (lemma48ActiveMass H weight n c)
      (lemma48ActiveMassCutoff H weight n c δ) t ω ≤ δ := by
  intro t ω
  let F := lemma48ActiveMass H weight n c
  let τ := lemma48ActiveMassCutoff H weight n c δ
  by_cases hτt : τ ω ≤ (t : WithTop ℝ≥0)
  · rw [MeasureTheory.stoppedProcess_eq_of_ge hτt]
    have hτne : τ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hτt
    rw [WithTop.untopA_eq_untop hτne]
    exact LeftContinuousHittingTime.value_at_strictHittingAfter_le
      F (lemma48ActiveMass_isLeftContinuous H weight n c ω)
      δ (by simpa [F] using hδ) (by simpa [τ, lemma48ActiveMassCutoff])
  · have htτ : (t : WithTop ℝ≥0) < τ ω := lt_of_not_ge hτt
    rw [MeasureTheory.stoppedProcess_eq_of_le htτ.le]
    exact LeftContinuousHittingTime.le_of_lt_strictHittingAfter
      F δ ω t (by simpa [τ, lemma48ActiveMassCutoff] using htτ)

end SIntegrableProcessStoppingCalculus

end FTAPTheorem42
