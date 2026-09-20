/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.ElementaryPredictableProcess
import Mathlib.Probability.Process.HittingTime

/-!
# Finite chronological observation grids

A countable right-dense skeleton is useful for observing right-continuous
paths, but its enumeration need not respect chronological order.  It therefore
cannot in general be used as the trading clock of a first-hit strategy.

This module introduces a separate finite chronological grid.  Pulling a
filtration back along its monotone grid map makes the discrete first-hit index
a stopping time.  Since the grid is finite, that index maps to a globally
finite stopping time in the original clock.  The corresponding stopping-time
σ-algebra is also transported to the original clock, so the resulting time
and event can be passed directly to predictable elementary pasting.
-/

open MeasureTheory

namespace FTAPTheorem42

variable {Ω Time : Type*} [MeasurableSpace Ω] [LinearOrder Time]

/--
A finite collection of observation times listed in chronological order.
Repeated times are permitted; strictness is not needed for the filtration
pullback or the stopping-time transport.
-/
structure ChronologicalGrid (Time : Type*) [LinearOrder Time] (N : ℕ) where
  /-- The `N + 1` grid times. -/
  time : Fin (N + 1) → Time
  /-- Grid indices respect the order of the original clock. -/
  monotone_time : Monotone time

namespace ChronologicalGrid

variable {N : ℕ} (G : ChronologicalGrid Time N)

/-- Pull a filtration back to the finite chronological grid. -/
def filtration
    (ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)) :
    Filtration (Fin (N + 1)) (inferInstance : MeasurableSpace Ω) where
  seq k := ℱ (G.time k)
  mono' _ _ h := ℱ.mono (G.monotone_time h)
  le' k := ℱ.le (G.time k)

@[simp]
theorem filtration_apply
    (ℱ : Filtration Time (inferInstance : MeasurableSpace Ω))
    (k : Fin (N + 1)) :
    G.filtration ℱ k = ℱ (G.time k) :=
  rfl

/-- Sample a process on the chronological grid. -/
def sample (X : Time → Ω → ℝ) : Fin (N + 1) → Ω → ℝ :=
  fun k => X (G.time k)

/-- Strong adaptedness is preserved by chronological sampling. -/
theorem stronglyAdapted_sample
    {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}
    {X : Time → Ω → ℝ}
    (hX : StronglyAdapted ℱ X) :
    StronglyAdapted (G.filtration ℱ) (G.sample X) :=
  fun k => hX (G.time k)

/-- The norm gap between two processes, sampled on the grid. -/
def gapProcess
    (X Y : Time → Ω → ℝ) : Fin (N + 1) → Ω → ℝ :=
  fun k ω => ‖X (G.time k) ω - Y (G.time k) ω‖

/-- The event that the two processes have a gap of at least `ε` somewhere on the grid. -/
def gapEvent
    (X Y : Time → Ω → ℝ) (ε : ℝ) : Set Ω :=
  {ω | ∃ k : Fin (N + 1), ε ≤ ‖X (G.time k) ω - Y (G.time k) ω‖}

/-- The sampled norm gap is adapted when both processes are strongly adapted. -/
theorem adapted_gapProcess
    {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}
    {X Y : Time → Ω → ℝ}
    (hX : StronglyAdapted ℱ X)
    (hY : StronglyAdapted ℱ Y) :
    Adapted (G.filtration ℱ) (G.gapProcess X Y) :=
  ((G.stronglyAdapted_sample hX).sub
    (G.stronglyAdapted_sample hY)).norm.adapted

/--
The first grid index at which the norm gap is at least `ε`.  If there is no
hit, `hittingBtwn` returns the final grid index, so this index is always finite.
-/
noncomputable def firstGapIndex
    (X Y : Time → Ω → ℝ) (ε : ℝ) : Ω → Fin (N + 1) :=
  hittingBtwn (G.gapProcess X Y) (Set.Ici ε) ⊥ ⊤

omit [MeasurableSpace Ω] in
/-- On the grid-gap event, the finite first-hit index is an actual hit. -/
theorem firstGapIndex_mem_Ici
    (X Y : Time → Ω → ℝ) (ε : ℝ) {ω : Ω}
    (hω : ω ∈ G.gapEvent X Y ε) :
    ε ≤ ‖X (G.time (G.firstGapIndex X Y ε ω)) ω -
      Y (G.time (G.firstGapIndex X Y ε ω)) ω‖ := by
  obtain ⟨k, hk⟩ := hω
  have hexists :
      ∃ j ∈ Set.Icc (⊥ : Fin (N + 1)) ⊤,
        G.gapProcess X Y j ω ∈ Set.Ici ε := by
    exact ⟨k, by simp, hk⟩
  exact hittingBtwn_mem_set hexists

/-- The finite-grid first-hit index is a stopping time for the grid filtration. -/
theorem isStoppingTime_firstGapIndex
    {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}
    {X Y : Time → Ω → ℝ}
    (hX : StronglyAdapted ℱ X)
    (hY : StronglyAdapted ℱ Y)
    (ε : ℝ) :
    IsStoppingTime (G.filtration ℱ)
      (fun ω => (G.firstGapIndex X Y ε ω : WithTop (Fin (N + 1)))) := by
  exact (G.adapted_gapProcess hX hY).isStoppingTime_hittingBtwn
    measurableSet_Ici

/-- Map the finite first-hit index back to the original time domain. -/
noncomputable def firstGapTime
    (X Y : Time → Ω → ℝ) (ε : ℝ) : Ω → Time :=
  fun ω => G.time (G.firstGapIndex X Y ε ω)

omit [MeasurableSpace Ω] in
private theorem firstGapTime_le_set
    (X Y : Time → Ω → ℝ) (ε : ℝ) (t : Time) :
    {ω | (G.firstGapTime X Y ε ω : WithTop Time) ≤ t} =
      ⋃ k : Fin (N + 1),
        if G.time k ≤ t then
          {ω | (G.firstGapIndex X Y ε ω : WithTop (Fin (N + 1))) = k}
        else ∅ := by
  ext ω
  constructor
  · intro hω
    simp only [firstGapTime, Set.mem_ofPred_eq, WithTop.coe_le_coe] at hω
    simp only [Set.mem_iUnion]
    refine ⟨G.firstGapIndex X Y ε ω, ?_⟩
    rw [ite_eq_left hω]
    simp
  · simp only [Set.mem_iUnion]
    rintro ⟨k, hk⟩
    by_cases hkt : G.time k ≤ t
    · rw [ite_eq_left hkt] at hk
      simp only [Set.mem_ofPred_eq, WithTop.coe_eq_coe] at hk
      simpa [firstGapTime, hk] using hkt
    · rw [ite_eq_right hkt] at hk
      exact hk.elim

/--
The finite-grid first-hit index, interpreted in the original clock, is a
globally finite stopping time.
-/
theorem isStoppingTime_firstGapTime
    {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}
    {X Y : Time → Ω → ℝ}
    (hX : StronglyAdapted ℱ X)
    (hY : StronglyAdapted ℱ Y)
    (ε : ℝ) :
    IsStoppingTime ℱ
      (fun ω => (G.firstGapTime X Y ε ω : WithTop Time)) := by
  let τ := G.firstGapIndex X Y ε
  have hτ :
      IsStoppingTime (G.filtration ℱ)
        (fun ω => (τ ω : WithTop (Fin (N + 1)))) :=
    G.isStoppingTime_firstGapIndex hX hY ε
  intro t
  rw [G.firstGapTime_le_set X Y ε t]
  refine MeasurableSet.iUnion fun k => ?_
  split_ifs with hkt
  · exact ℱ.mono hkt _
      (hτ.measurableSet_eq_of_countable k)
  · exact @MeasurableSet.empty Ω (ℱ t)

/--
An event known at the discrete first-hit index is known at the corresponding
actual grid time.
-/
theorem measurableSet_firstGapTime_of_firstGapIndex
    {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}
    {X Y : Time → Ω → ℝ}
    (hX : StronglyAdapted ℱ X)
    (hY : StronglyAdapted ℱ Y)
    (ε : ℝ) (s : Set Ω)
    (hs :
      MeasurableSet[(G.isStoppingTime_firstGapIndex hX hY ε).measurableSpace] s) :
    MeasurableSet[
      (G.isStoppingTime_firstGapTime hX hY ε).measurableSpace] s := by
  let τ := G.firstGapIndex X Y ε
  have hτ :
      IsStoppingTime (G.filtration ℱ)
        (fun ω => (τ ω : WithTop (Fin (N + 1)))) :=
    G.isStoppingTime_firstGapIndex hX hY ε
  have hs' : MeasurableSet[hτ.measurableSpace] s := hs
  refine ⟨?_, fun t => ?_⟩
  · have hle : (⨆ k, G.filtration ℱ k) ≤ (⨆ u, ℱ u) :=
      iSup_le fun k => by
      simpa only [G.filtration_apply] using
        (le_iSup ℱ (G.time k))
    exact hle s hs.1
  rw [G.firstGapTime_le_set X Y ε t, Set.inter_iUnion]
  refine MeasurableSet.iUnion fun k => ?_
  by_cases hkt : G.time k ≤ t
  · rw [ite_eq_left hkt]
    have hk :
        MeasurableSet[G.filtration ℱ k]
          (s ∩
            {ω |
              (τ ω : WithTop (Fin (N + 1))) = k}) := by
      have hlevel :
          MeasurableSet[hτ.measurableSpace]
            {ω | (τ ω : WithTop (Fin (N + 1))) = k} :=
        hτ.measurableSet_eq_of_countable' k
      exact
        (hτ.measurableSet_inter_eq_iff s k).mp
          (hs'.inter hlevel)
    exact ℱ.mono hkt _ hk
  · rw [ite_eq_right hkt, Set.inter_empty]
    exact @MeasurableSet.empty Ω (ℱ t)

end ChronologicalGrid

end FTAPTheorem42
