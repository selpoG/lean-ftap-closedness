/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.FactorialChronologicalGrid
import Mathlib.Probability.Process.Adapted

/-!
# Right-continuous adapted processes are progressive

On each deterministic finite horizon, round time upward to a factorial grid
and clamp at the horizon.  The resulting process has countably many time
sections, all measurable at the terminal sigma algebra.  Right continuity
identifies its pointwise limit with the original process.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal Topology

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace RightContinuousProgressive

omit [MeasurableSpace Ω] in
/-- The horizon-clamped right approximation has countable range. -/
theorem countable_range_min_approx (r : ℕ) (T : ℝ≥0) :
    (Set.range fun t : Set.Iic T =>
      min (FactorialChronologicalGrid.approx r t.1) T).Countable := by
  apply Set.Countable.mono ?_
    (Set.countable_range fun k : ℕ =>
      min ((k : ℝ≥0) / (r.factorial : ℝ≥0)) T)
  rintro _ ⟨t, rfl⟩
  exact ⟨Nat.ceil (t.1 * (r.factorial : ℝ≥0)), rfl⟩

/-- One clamped right-grid step process is jointly strongly measurable on
the finite horizon. -/
theorem stronglyMeasurable_step
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {X : ℝ≥0 → Ω → ℝ} (hX : StronglyAdapted ℱ X)
    (r : ℕ) (T : ℝ≥0) :
    StronglyMeasurable[Subtype.instMeasurableSpace.prod (ℱ T)]
      (fun p : Set.Iic T × Ω =>
        X (min (FactorialChronologicalGrid.approx r p.1.1) T) p.2) := by
  let q : Set.Iic T → ℝ≥0 := fun t =>
    min (FactorialChronologicalGrid.approx r t.1) T
  have hqMeas : Measurable q := by
    exact ((FactorialChronologicalGrid.approx_mono r).min monotone_const).measurable.comp
      measurable_subtype_coe
  have hqCountable : (Set.range q).Countable :=
    countable_range_min_approx r T
  apply Measurable.stronglyMeasurable
  intro s hs
  have heq :
      {p : Set.Iic T × Ω | X (q p.1) p.2 ∈ s} =
        ⋃ u ∈ Set.range q,
          (q ⁻¹' {u}) ×ˢ (X u ⁻¹' s) := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_range,
      Set.mem_prod, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hp
      exact ⟨q p.1, ⟨p.1, rfl⟩, rfl, hp⟩
    · rintro ⟨u, -, hu, hp⟩
      simpa only [hu] using hp
  change MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ T)]
    {p : Set.Iic T × Ω | X (q p.1) p.2 ∈ s}
  rw [heq]
  apply MeasurableSet.biUnion hqCountable
  intro u hu
  have huT : u ≤ T := by
    obtain ⟨t, rfl⟩ := hu
    exact min_le_right _ _
  exact (hqMeas (measurableSet_singleton u)).prod
    (((hX u).mono (ℱ.mono huT)).measurable hs)

end RightContinuousProgressive

/-- A strongly adapted real process with right-continuous paths is strongly
progressive. -/
theorem StronglyAdapted.isStronglyProgressive_of_rightContinuous
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {X : ℝ≥0 → Ω → ℝ} (hX : StronglyAdapted ℱ X)
    (hRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t) :
    IsStronglyProgressive ℱ X := by
  intro T
  refine stronglyMeasurable_of_tendsto atTop
    (f := fun r (p : Set.Iic T × Ω) =>
      X (min (FactorialChronologicalGrid.approx r p.1.1) T) p.2)
    (g := fun p : Set.Iic T × Ω => X p.1.1 p.2) ?_ ?_
  · exact fun r =>
      RightContinuousProgressive.stronglyMeasurable_step hX r T
  · rw [tendsto_pi_nhds]
    intro p
    apply (hRight p.2 p.1.1).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hmin := (FactorialChronologicalGrid.tendsto_approx p.1.1).min
          (tendsto_const_nhds :
            Tendsto (fun _ : ℕ => T) atTop (𝓝 T))
      have hpT : p.1.1 ≤ T := p.1.2
      simpa only [min_eq_left hpT] using hmin
    · exact Filter.Eventually.of_forall fun r =>
        le_min (FactorialChronologicalGrid.le_approx r p.1.1) p.1.2

end FTAPTheorem42
