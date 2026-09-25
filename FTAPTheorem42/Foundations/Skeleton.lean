/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Core.Basic

/-! # Bounds from right-dense skeletons

Countable skeleton estimates extend to all times by right continuity. This
gives measurable common norm envelopes and simultaneous lower bounds. -/

namespace FTAPTheorem42

open Filter MeasureTheory Topology
open scoped BigOperators ENNReal MeasureTheory ProbabilityTheory

/-! ### The generic right-dense skeleton argument -/

theorem norm_le_of_rightDense_skeleton
    {Time : Type*} [TopologicalSpace Time] [LinearOrder Time] [OrderTopology Time]
    (skeleton : ℕ → Time)
    (hRightDense : ∀ t, t ∈ closure (Set.range skeleton ∩ Set.Ici t))
    (f : Time → ℝ)
    (hRightCont : ∀ t, ContinuousWithinAt f (Set.Ici t) t)
    {C : ℝ}
    (hC : ∀ k, ‖f (skeleton k)‖ ≤ C) :
    ∀ t, ‖f t‖ ≤ C := by
  intro t
  by_contra hnot
  have hlt : C < ‖f t‖ := lt_of_not_ge hnot
  have : NeBot (𝓝[Set.range skeleton ∩ Set.Ici t] t) :=
    mem_closure_iff_nhdsWithin_neBot.1 (hRightDense t)
  have hevI : ∀ᶠ s in 𝓝[Set.Ici t] t, C < ‖f s‖ := by
    have hnorm : ContinuousWithinAt (fun s => ‖f s‖) (Set.Ici t) t :=
      (hRightCont t).norm
    exact hnorm.eventually (Ioi_mem_nhds hlt)
  have hsubset : Set.range skeleton ∩ Set.Ici t ⊆ Set.Ici t :=
    Set.inter_subset_right
  have hevA : ∀ᶠ s in 𝓝[Set.range skeleton ∩ Set.Ici t] t,
      C < ‖f s‖ :=
    Filter.Eventually.filter_mono (nhdsWithin_mono t hsubset) hevI
  obtain ⟨s, hsGt, hsA⟩ := (hevA.and self_mem_nhdsWithin).exists
  rcases hsA.1 with ⟨k, rfl⟩
  exact (not_lt_of_ge (hC k)) hsGt

/-! ### Measurable scalar envelope on the skeleton -/

noncomputable def rightSkeletonNormEnvelope
    {Time Ω : Type*}
    (u : ℕ → Time → Ω → ℝ) (skeleton : ℕ → Time) (ω : Ω) : ℝ :=
  ⨆ p : ℕ × ℕ, ‖u p.1 (skeleton p.2) ω‖

theorem measurable_rightSkeletonNormEnvelope
    {Time Ω : Type*} [MeasurableSpace Ω]
    (u : ℕ → Time → Ω → ℝ) (skeleton : ℕ → Time)
    (hMeas : ∀ n k, Measurable (u n (skeleton k))) :
    Measurable (rightSkeletonNormEnvelope u skeleton) := by
  unfold rightSkeletonNormEnvelope
  apply Measurable.iSup
  intro p
  exact measurable_norm.comp (hMeas p.1 p.2)

theorem norm_le_rightSkeletonNormEnvelope_of_bddAbove
    {Time Ω : Type*} [TopologicalSpace Time] [LinearOrder Time] [OrderTopology Time]
    (u : ℕ → Time → Ω → ℝ) (skeleton : ℕ → Time)
    (hRightDense : ∀ t, t ∈ closure (Set.range skeleton ∩ Set.Ici t))
    (hRightCont : ∀ n ω t, ContinuousWithinAt (u n · ω) (Set.Ici t) t)
    {ω : Ω}
    (hbound : BddAbove (Set.range fun p : ℕ × ℕ =>
      ‖u p.1 (skeleton p.2) ω‖)) :
    ∀ n t, ‖u n t ω‖ ≤ rightSkeletonNormEnvelope u skeleton ω := by
  intro n t
  have hC : ∀ k, ‖u n (skeleton k) ω‖ ≤ rightSkeletonNormEnvelope u skeleton ω := by
    intro k
    unfold rightSkeletonNormEnvelope
    exact le_ciSup hbound (n, k)
  exact norm_le_of_rightDense_skeleton skeleton hRightDense (u n · ω)
    (fun s => hRightCont n ω s) hC t

/-!
## All-time gap events

For right-continuous paths, a strict norm gap at some time is also detected by
the endpoint-safe right-dense skeleton.  Consequently, the non-strict
all-time gap event is contained in a strict skeleton gap event at half the
threshold.  The last theorem packages this inclusion as a consumer for
pairwise Cauchy-in-measure estimates.
-/

/-! ### All-time and skeleton gap events -/

/-- The non-strict gap event at an arbitrary time. -/
def allTimeGapEvent
    {Time Ω : Type*} (X Y : Time → Ω → ℝ) (ε : ℝ) : Set Ω :=
  {ω | ∃ t, ε ≤ ‖X t ω - Y t ω‖}

end FTAPTheorem42

namespace FTAPTheorem42

open Filter MeasureTheory Topology

/--
Deterministic-time almost-everywhere lower bounds for a right-continuous
process hold simultaneously at every time outside one null set.
-/
theorem ae_all_lowerBound_of_rightDense_skeleton
    {Time Ω : Type*} [TopologicalSpace Time] [LinearOrder Time]
    [OrderTopology Time] [MeasurableSpace Ω]
    {μ : Measure Ω} (u : Time → Ω → ℝ)
    (skeleton : ℕ → Time)
    (hRightDense : ∀ t,
      t ∈ closure (Set.range skeleton ∩ Set.Ici t))
    (hRightCont : ∀ ω t,
      ContinuousWithinAt (u · ω) (Set.Ici t) t)
    {c : ℝ} (hlower : ∀ t, AELowerBoundedBy μ c (u t)) :
    ∀ᵐ ω ∂μ, ∀ t, c ≤ u t ω := by
  have hskeleton : ∀ᵐ ω ∂μ, ∀ k, c ≤ u (skeleton k) ω := by
    rw [ae_all_iff]
    exact fun k => hlower (skeleton k)
  filter_upwards [hskeleton] with ω hω
  intro t
  by_contra hnot
  have hlt : u t ω < c := lt_of_not_ge hnot
  have : NeBot
      (𝓝[Set.range skeleton ∩ Set.Ici t] t) :=
    mem_closure_iff_nhdsWithin_neBot.1 (hRightDense t)
  have hevI : ∀ᶠ s in 𝓝[Set.Ici t] t, u s ω < c :=
    (hRightCont ω t).eventually (Iio_mem_nhds hlt)
  have hsubset : Set.range skeleton ∩ Set.Ici t ⊆ Set.Ici t :=
    Set.inter_subset_right
  have hevA : ∀ᶠ s in
      𝓝[Set.range skeleton ∩ Set.Ici t] t, u s ω < c :=
    Filter.Eventually.filter_mono
      (nhdsWithin_mono t hsubset) hevI
  obtain ⟨s, hsLt, hsMem⟩ :=
    (hevA.and self_mem_nhdsWithin).exists
  rcases hsMem.1 with ⟨k, rfl⟩
  exact (not_lt_of_ge (hω k)) hsLt

end FTAPTheorem42
