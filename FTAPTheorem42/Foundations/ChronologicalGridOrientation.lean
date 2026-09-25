/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.FactorialChronologicalGrid

/-!
# Orienting a finite-grid first hit

The first-hit index lives on a finite discrete filtration, even when the
original market clock is continuous.  On that index filtration, stopped
values are measurable and the norm gap splits into two measurable oriented
events.  At least one orientation retains half of any prescribed lower bound
on the mass of the grid-gap event.
-/

open Filter MeasureTheory
open scoped ENNReal NNReal

namespace FTAPTheorem42

variable {Ω Time : Type*} [MeasurableSpace Ω] [LinearOrder Time]

namespace ChronologicalGrid

variable {N : ℕ} (G : ChronologicalGrid Time N)

/-- The sampled process stopped at the finite first-gap index. -/
noncomputable def stoppedAtFirstGap
    (X Y : Time → Ω → ℝ) (ε : ℝ) (Z : Time → Ω → ℝ) :
    Ω → ℝ :=
  stoppedValue (G.sample Z)
    (fun ω => (G.firstGapIndex X Y ε ω : WithTop (Fin (N + 1))))

/-- The orientation where `X - Y` is positive at the first grid hit. -/
def positiveFirstGapEvent
    (X Y : Time → Ω → ℝ) (ε : ℝ) : Set Ω :=
  {ω |
    ε ≤ G.stoppedAtFirstGap X Y ε X ω -
      G.stoppedAtFirstGap X Y ε Y ω}

/-- The orientation where `Y - X` is positive at the first grid hit. -/
def negativeFirstGapEvent
    (X Y : Time → Ω → ℝ) (ε : ℝ) : Set Ω :=
  {ω |
    ε ≤ G.stoppedAtFirstGap X Y ε Y ω -
      G.stoppedAtFirstGap X Y ε X ω}

omit [MeasurableSpace Ω] in
@[simp]
theorem stoppedAtFirstGap_eq
    (X Y : Time → Ω → ℝ) (ε : ℝ) (Z : Time → Ω → ℝ)
    (ω : Ω) :
    G.stoppedAtFirstGap X Y ε Z ω =
      Z (G.firstGapTime X Y ε ω) ω := by
  rfl

omit [MeasurableSpace Ω] in
theorem gapProcess_swap
    (X Y : Time → Ω → ℝ) :
    G.gapProcess Y X = G.gapProcess X Y := by
  funext k ω
  exact norm_sub_rev _ _

omit [MeasurableSpace Ω] in
theorem firstGapIndex_swap
    (X Y : Time → Ω → ℝ) (ε : ℝ) :
    G.firstGapIndex Y X ε = G.firstGapIndex X Y ε := by
  unfold firstGapIndex
  rw [G.gapProcess_swap X Y]

omit [MeasurableSpace Ω] in
theorem stoppedAtFirstGap_swap
    (X Y Z : Time → Ω → ℝ) (ε : ℝ) :
    G.stoppedAtFirstGap Y X ε Z =
      G.stoppedAtFirstGap X Y ε Z := by
  unfold stoppedAtFirstGap
  rw [G.firstGapIndex_swap X Y ε]

omit [MeasurableSpace Ω] in
theorem positiveFirstGapEvent_swap
    (X Y : Time → Ω → ℝ) (ε : ℝ) :
    G.positiveFirstGapEvent Y X ε =
      G.negativeFirstGapEvent X Y ε := by
  unfold positiveFirstGapEvent negativeFirstGapEvent
  rw [G.stoppedAtFirstGap_swap X Y Y ε,
    G.stoppedAtFirstGap_swap X Y X ε]

/-- The positive orientation is measurable at the discrete first-hit index. -/
theorem measurableSet_positiveFirstGapEvent
    {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}
    {X Y : Time → Ω → ℝ}
    (hX : StronglyAdapted ℱ X)
    (hY : StronglyAdapted ℱ Y)
    (ε : ℝ) :
    MeasurableSet[
      (G.isStoppingTime_firstGapIndex hX hY ε).measurableSpace]
      (G.positiveFirstGapEvent X Y ε) := by
  let τ : Ω → WithTop (Fin (N + 1)) :=
    fun ω => (G.firstGapIndex X Y ε ω : WithTop (Fin (N + 1)))
  have hτ : IsStoppingTime (G.filtration ℱ) τ :=
    G.isStoppingTime_firstGapIndex hX hY ε
  have hXprogressive :
      IsStronglyProgressive (G.filtration ℱ) (G.sample X) :=
    (G.stronglyAdapted_sample hX).isStronglyProgressive_of_discrete
  have hYprogressive :
      IsStronglyProgressive (G.filtration ℱ) (G.sample Y) :=
    (G.stronglyAdapted_sample hY).isStronglyProgressive_of_discrete
  have hXstop :
      Measurable[hτ.measurableSpace]
        (stoppedValue (G.sample X) τ) :=
    measurable_stoppedValue hXprogressive hτ
  have hYstop :
      Measurable[hτ.measurableSpace]
        (stoppedValue (G.sample Y) τ) :=
    measurable_stoppedValue hYprogressive hτ
  have hset :
      MeasurableSet[hτ.measurableSpace]
        {ω |
          ε ≤ stoppedValue (G.sample X) τ ω -
            stoppedValue (G.sample Y) τ ω} :=
    measurableSet_Ici.preimage (hXstop.sub hYstop)
  exact hset

omit [MeasurableSpace Ω] in
/-- A grid hit belongs to one of the two oriented events. -/
theorem gapEvent_subset_positive_union_negative
    (X Y : Time → Ω → ℝ) (ε : ℝ) :
    G.gapEvent X Y ε ⊆
      G.positiveFirstGapEvent X Y ε ∪
        G.negativeFirstGapEvent X Y ε := by
  intro ω hω
  have hnorm :=
    G.firstGapIndex_mem_Ici X Y ε hω
  change
    ε ≤ ‖G.stoppedAtFirstGap X Y ε X ω -
      G.stoppedAtFirstGap X Y ε Y ω‖ at hnorm
  rw [Real.norm_eq_abs] at hnorm
  by_cases hsign :
      0 ≤ G.stoppedAtFirstGap X Y ε X ω -
        G.stoppedAtFirstGap X Y ε Y ω
  · left
    have hsign' :
        0 ≤ X (G.firstGapTime X Y ε ω) ω -
          Y (G.firstGapTime X Y ε ω) ω := by
      simpa using hsign
    change
      ε ≤ G.stoppedAtFirstGap X Y ε X ω -
        G.stoppedAtFirstGap X Y ε Y ω
    simpa [abs_of_nonneg hsign'] using hnorm
  · right
    have hneg :
        G.stoppedAtFirstGap X Y ε X ω -
          G.stoppedAtFirstGap X Y ε Y ω < 0 :=
      lt_of_not_ge hsign
    have hneg' :
        X (G.firstGapTime X Y ε ω) ω -
          Y (G.firstGapTime X Y ε ω) ω < 0 := by
      simpa using hneg
    change
      ε ≤ G.stoppedAtFirstGap X Y ε Y ω -
        G.stoppedAtFirstGap X Y ε X ω
    simpa [abs_of_neg hneg'] using hnorm

/--
If the grid-gap event has mass greater than `δ`, one orientation has mass at
least `δ / 2`.
-/
theorem measure_gt_imp_oriented_measure_ge_half
    {μ : Measure Ω} (X Y : Time → Ω → ℝ)
    (ε : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hmass : ENNReal.ofReal δ < μ (G.gapEvent X Y ε)) :
    ENNReal.ofReal (δ / 2) ≤
        μ (G.positiveFirstGapEvent X Y ε) ∨
      ENNReal.ofReal (δ / 2) ≤
        μ (G.negativeFirstGapEvent X Y ε) := by
  let positive := G.positiveFirstGapEvent X Y ε
  let negative := G.negativeFirstGapEvent X Y ε
  have hcover : G.gapEvent X Y ε ⊆ positive ∪ negative := by
    simpa [positive, negative] using
      G.gapEvent_subset_positive_union_negative X Y ε
  by_cases hpositive : ENNReal.ofReal (δ / 2) ≤ μ positive
  · exact Or.inl (by simpa [positive] using hpositive)
  right
  by_contra hnegative
  have hpositive' : μ positive < ENNReal.ofReal (δ / 2) :=
    lt_of_not_ge hpositive
  have hnegative' : μ negative < ENNReal.ofReal (δ / 2) :=
    lt_of_not_ge hnegative
  have hsum : μ positive + μ negative < ENNReal.ofReal δ := by
    calc
      μ positive + μ negative <
          ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) :=
        ENNReal.add_lt_add_of_lt_of_le
          (hnegative'.trans ENNReal.ofReal_lt_top).ne
          hpositive' hnegative'.le
      _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_add (half_pos hδ).le (half_pos hδ).le]
        congr 1
        ring
  have hle :
      μ (G.gapEvent X Y ε) ≤ μ (positive ∪ negative) :=
    measure_mono hcover
  have hunion_lt : μ (positive ∪ negative) < ENNReal.ofReal δ :=
    (measure_union_le positive negative).trans_lt hsum
  exact (lt_irrefl (ENNReal.ofReal δ))
    (hmass.trans_le hle |>.trans hunion_lt)

end ChronologicalGrid

namespace FactorialChronologicalGrid

noncomputable section

/--
A persistent all-time gap supplies strategy-index pairs escaping to infinity,
one factorial-grid level for each pair, and a uniformly positive-mass
orientation of the finite first hit.  The orientation is normalized by
swapping the pair when necessary.
-/
theorem exists_oriented_pair_grid_sequences_of_persistent_allTimeGap
    {μ : Measure Ω}
    (X : ℕ → ℝ≥0 → Ω → ℝ)
    (hXrc : ∀ n ω t,
      ContinuousWithinAt (X n · ω) (Set.Ici t) t)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hpersistent : ∀ N : ℕ, ∃ n m : ℕ,
      N ≤ n ∧ N ≤ m ∧
        ENNReal.ofReal δ <
          μ (allTimeGapEvent (X n) (X m) ε)) :
    ∃ first second level : ℕ → ℕ,
      Tendsto first atTop atTop ∧
      Tendsto second atTop atTop ∧
      ∀ k,
        ENNReal.ofReal (δ / 2) ≤
          μ ((grid (level k)).positiveFirstGapEvent
            (X (first k)) (X (second k)) (ε / 2)) := by
  classical
  choose left right hleft hright hmass using hpersistent
  have hgrid_exists : ∀ k, ∃ r,
      ENNReal.ofReal δ <
        μ (gapEvent r (X (left k)) (X (right k)) (ε / 2)) := by
    intro k
    exact exists_gapEvent_measure_gt
      (X (left k)) (X (right k))
      (hXrc (left k)) (hXrc (right k)) hε (hmass k)
  choose level hlevel_mass using hgrid_exists
  let positive : ℕ → Prop := fun k =>
    ENNReal.ofReal (δ / 2) ≤
      μ ((grid (level k)).positiveFirstGapEvent
        (X (left k)) (X (right k)) (ε / 2))
  have horiented : ∀ k,
      positive k ∨
        ENNReal.ofReal (δ / 2) ≤
          μ ((grid (level k)).negativeFirstGapEvent
            (X (left k)) (X (right k)) (ε / 2)) := by
    intro k
    exact (grid (level k)).measure_gt_imp_oriented_measure_ge_half
      (X (left k)) (X (right k)) (ε / 2) hδ (hlevel_mass k)
  let first : ℕ → ℕ := fun k =>
    if positive k then left k else right k
  let second : ℕ → ℕ := fun k =>
    if positive k then right k else left k
  have hfirst_lower : ∀ k, k ≤ first k := by
    intro k
    dsimp [first]
    split_ifs
    · exact hleft k
    · exact hright k
  have hsecond_lower : ∀ k, k ≤ second k := by
    intro k
    dsimp [second]
    split_ifs
    · exact hright k
    · exact hleft k
  have hfirst_tendsto : Tendsto first atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    exact ⟨b, fun k hk => hk.trans (hfirst_lower k)⟩
  have hsecond_tendsto : Tendsto second atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    exact ⟨b, fun k hk => hk.trans (hsecond_lower k)⟩
  refine ⟨first, second, level, hfirst_tendsto, hsecond_tendsto, ?_⟩
  intro k
  by_cases h : positive k
  · rw [show first k = left k by simp [first, h],
      show second k = right k by simp [second, h]]
    exact h
  · have hnegative := (horiented k).resolve_left h
    rw [show first k = right k by simp [first, h],
      show second k = left k by simp [second, h],
      (grid (level k)).positiveFirstGapEvent_swap
        (X (left k)) (X (right k)) (ε / 2)]
    exact hnegative

end

end FactorialChronologicalGrid

end FTAPTheorem42
