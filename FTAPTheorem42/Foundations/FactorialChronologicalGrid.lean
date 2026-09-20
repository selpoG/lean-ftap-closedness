/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.ChronologicalGrid
import Mathlib.Analysis.SpecificLimits.Basic
import FTAPTheorem42.Foundations.Skeleton

/-!
# Nested factorial grids on nonnegative time

At level `r`, the factorial grid consists of the points

`k / r!`, for `0 ≤ k ≤ r * r!`.

Thus it covers `[0, r]` with mesh `1 / r!`.  Consecutive grids are nested
because `r!` divides `(r + 1)!`.  For a fixed time `t`, rounding `t * r!`
upward gives a grid point converging to `t` from the right.  Consequently a
strict gap between right-continuous paths is detected on one finite
chronological grid.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Topology
open scoped ENNReal NNReal

namespace FactorialChronologicalGrid

/-- The natural-number index of the factorial approximation of `x`. -/
noncomputable def approxNatIndex (r : ℕ) (x : ℝ≥0) : ℕ :=
  Nat.ceil (x * (r.factorial : ℝ≥0))

/-- The level-`r` factorial grid on `ℝ≥0`. -/
noncomputable def grid (r : ℕ) :
    ChronologicalGrid ℝ≥0 (r * r.factorial) where
  time k := (k : ℝ≥0) / (r.factorial : ℝ≥0)
  monotone_time := by
    intro k l hkl
    exact div_le_div_of_nonneg_right (by exact_mod_cast hkl) (by positivity)

/-- Every level-`r` grid time also occurs at level `r + 1`. -/
theorem range_grid_subset_succ (r : ℕ) :
    Set.range (grid r).time ⊆ Set.range (grid (r + 1)).time := by
  rintro _ ⟨k, rfl⟩
  have hk_le : k.1 ≤ r * r.factorial :=
    Nat.le_of_lt_succ k.2
  have hfactorial :
      r * r.factorial ≤ (r + 1).factorial := by
    rw [Nat.factorial_succ]
    exact Nat.mul_le_mul_right r.factorial (Nat.le_succ r)
  have hindex_le :
      (r + 1) * k.1 ≤
        (r + 1) * (r + 1).factorial :=
    Nat.mul_le_mul_left (r + 1) (hk_le.trans hfactorial)
  let l : Fin ((r + 1) * (r + 1).factorial + 1) :=
    ⟨(r + 1) * k.1, Nat.lt_succ_of_le hindex_le⟩
  refine ⟨l, ?_⟩
  change
    (((r + 1) * k.1 : ℕ) : ℝ≥0) /
        (((r + 1).factorial : ℕ) : ℝ≥0) =
      (k.1 : ℝ≥0) / (r.factorial : ℝ≥0)
  simp only [Nat.cast_mul, Nat.factorial_succ]
  rw [mul_div_mul_left]
  positivity

/-- Factorial-grid ranges are nested with the level. -/
theorem range_grid_mono :
    Monotone (fun r => Set.range (grid r).time) :=
  monotone_nat_of_le_succ range_grid_subset_succ

/-- Round `t` upward to the mesh `1 / r!`. -/
noncomputable def approx (r : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  (Nat.ceil (t * (r.factorial : ℝ≥0)) : ℝ≥0) /
    (r.factorial : ℝ≥0)

/-- At each level, right factorial approximation is monotone in the target
time. -/
theorem approx_mono (r : ℕ) : Monotone (approx r) := by
  intro s t hst
  unfold approx
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Nat.ceil_mono
      (mul_le_mul_of_nonneg_right hst (by positivity))
  · exact bot_le

/-- The factorial approximation lies to the right of the target time. -/
theorem le_approx (r : ℕ) (t : ℝ≥0) :
    t ≤ approx r t := by
  rw [approx, le_div_iff₀ (by positivity)]
  exact Nat.le_ceil _

/-- Rounding upward on the level-`r` factorial mesh adds at most one mesh
width. -/
theorem approx_le_add_inv_factorial (r : Nat) (t : NNReal) :
    approx r t ≤ t + (r.factorial : NNReal)⁻¹ := by
  rw [approx, div_le_iff₀ (by positivity)]
  have hceil :
      (Nat.ceil (t * (r.factorial : NNReal)) : NNReal) ≤
        t * (r.factorial : NNReal) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  calc
    (Nat.ceil (t * (r.factorial : NNReal)) : NNReal)
        ≤ t * (r.factorial : NNReal) + 1 := hceil
    _ = (t + (r.factorial : NNReal)⁻¹) *
        (r.factorial : NNReal) := by
      simp [add_mul, (show (r.factorial : NNReal) ≠ 0 by positivity)]

/-- The right factorial approximations converge to their target time. -/
theorem tendsto_approx (t : ℝ≥0) :
    Tendsto (fun r => approx r t) atTop (𝓝 t) := by
  have hfactorial :
      Tendsto (fun r : ℕ => (r.factorial : ℝ≥0)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp factorial_tendsto_atTop
  have hinv :
      Tendsto (fun r : ℕ => (r.factorial : ℝ≥0)⁻¹)
        atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hfactorial
  have hupper :
      Tendsto
        (fun r : ℕ => t + (r.factorial : ℝ≥0)⁻¹)
        atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.add hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
  · exact Filter.Eventually.of_forall fun r => le_approx r t
  · refine Filter.Eventually.of_forall fun r => ?_
    rw [approx, div_le_iff₀ (by positivity)]
    have hceil :
        (Nat.ceil (t * (r.factorial : ℝ≥0)) : ℝ≥0) ≤
          t * (r.factorial : ℝ≥0) + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    calc
      (Nat.ceil (t * (r.factorial : ℝ≥0)) : ℝ≥0)
          ≤ t * (r.factorial : ℝ≥0) + 1 := hceil
      _ = (t + (r.factorial : ℝ≥0)⁻¹) *
          (r.factorial : ℝ≥0) := by
        simp [add_mul, (show (r.factorial : ℝ≥0) ≠ 0 by positivity)]

/--
Once the level is beyond `⌈t⌉₊`, the rounded point belongs to the finite
level-`r` grid.
-/
theorem ceil_mul_factorial_lt_gridSize
    (t : ℝ≥0) {r : ℕ} (hr : Nat.ceil t ≤ r) :
    Nat.ceil (t * (r.factorial : ℝ≥0)) <
      r * r.factorial + 1 := by
  rw [Nat.lt_add_one_iff]
  apply Nat.ceil_le.mpr
  have htr : t ≤ (r : ℝ≥0) :=
    (Nat.le_ceil t).trans (by exact_mod_cast hr)
  simpa only [Nat.cast_mul, Nat.cast_factorial] using
    mul_le_mul_of_nonneg_right htr (by positivity)

/-- The rounded approximation as an actual point of the level-`r` grid. -/
noncomputable def approxIndex
    (t : ℝ≥0) {r : ℕ} (hr : Nat.ceil t ≤ r) :
    Fin (r * r.factorial + 1) :=
  ⟨Nat.ceil (t * (r.factorial : ℝ≥0)),
    ceil_mul_factorial_lt_gridSize t hr⟩

@[simp]
theorem grid_time_approxIndex
    (t : ℝ≥0) {r : ℕ} (hr : Nat.ceil t ≤ r) :
    (grid r).time (approxIndex t hr) = approx r t :=
  rfl

/-- The event that a level-`r` grid detects a gap of at least `ε`. -/
def gapEvent
    {Ω : Type*} (r : ℕ)
    (X Y : ℝ≥0 → Ω → ℝ) (ε : ℝ) : Set Ω :=
  (grid r).gapEvent X Y ε

/-- Grid-gap events increase with the factorial-grid level. -/
theorem gapEvent_mono
    {Ω : Type*} (X Y : ℝ≥0 → Ω → ℝ) (ε : ℝ) :
    Monotone (fun r => gapEvent r X Y ε) := by
  apply monotone_nat_of_le_succ
  intro r ω hω
  obtain ⟨k, hk⟩ := hω
  obtain ⟨l, hl⟩ :=
    range_grid_subset_succ r
      ⟨k, rfl⟩
  refine ⟨l, ?_⟩
  rw [hl]
  exact hk

/--
Every all-time non-strict gap is detected strictly above half the threshold
on one finite factorial grid.
-/
theorem allTimeGapEvent_subset_iUnion_gapEvent_half
    {Ω : Type*}
    (X Y : ℝ≥0 → Ω → ℝ)
    (hX : ∀ ω t, ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (hY : ∀ ω t, ContinuousWithinAt (Y · ω) (Set.Ici t) t)
    {ε : ℝ} (hε : 0 < ε) :
    allTimeGapEvent X Y ε ⊆
      ⋃ r, gapEvent r X Y (ε / 2) := by
  intro ω hω
  obtain ⟨t, ht⟩ := hω
  have happrox : Tendsto (fun r => approx r t) atTop (𝓝 t) :=
    tendsto_approx t
  have hwithin : ∀ᶠ r in atTop, approx r t ∈ Set.Ici t :=
    Filter.Eventually.of_forall fun r => le_approx r t
  have hXlim :
      Tendsto (fun r => X (approx r t) ω) atTop (𝓝 (X t ω)) :=
    (hX ω t).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨happrox, hwithin⟩)
  have hYlim :
      Tendsto (fun r => Y (approx r t) ω) atTop (𝓝 (Y t ω)) :=
    (hY ω t).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨happrox, hwithin⟩)
  have hnorm :
      Tendsto
        (fun r => ‖X (approx r t) ω - Y (approx r t) ω‖)
        atTop (𝓝 ‖X t ω - Y t ω‖) :=
    (hXlim.sub hYlim).norm
  have hhalf : ε / 2 < ‖X t ω - Y t ω‖ := by
    linarith
  have heventuallyGap :
      ∀ᶠ r in atTop,
        ε / 2 < ‖X (approx r t) ω - Y (approx r t) ω‖ :=
    hnorm.eventually (Ioi_mem_nhds hhalf)
  have heventuallyLevel : ∀ᶠ r : ℕ in atTop, Nat.ceil t ≤ r :=
    eventually_ge_atTop (Nat.ceil t)
  obtain ⟨r, hgap, hr⟩ :=
    (heventuallyGap.and heventuallyLevel).exists
  simp only [Set.mem_iUnion]
  refine ⟨r, ?_⟩
  change
    ∃ k : Fin (r * r.factorial + 1),
      ε / 2 ≤ ‖X ((grid r).time k) ω - Y ((grid r).time k) ω‖
  exact
    ⟨approxIndex t hr, by
      rw [grid_time_approxIndex]
      exact hgap.le⟩

/--
If the all-time gap event has measure strictly larger than `c`, one finite
factorial grid already detects the half-threshold gap with measure larger than
`c`.
-/
theorem exists_gapEvent_measure_gt
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X Y : ℝ≥0 → Ω → ℝ)
    (hX : ∀ ω t, ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (hY : ∀ ω t, ContinuousWithinAt (Y · ω) (Set.Ici t) t)
    {ε : ℝ} (hε : 0 < ε) {c : ℝ≥0∞}
    (hmass : c < μ (allTimeGapEvent X Y ε)) :
    ∃ r, c < μ (gapEvent r X Y (ε / 2)) := by
  have hsubset :
      allTimeGapEvent X Y ε ⊆
        ⋃ r, gapEvent r X Y (ε / 2) :=
    allTimeGapEvent_subset_iUnion_gapEvent_half X Y hX hY hε
  have hunion :
      c < μ (⋃ r, gapEvent r X Y (ε / 2)) :=
    hmass.trans_le (measure_mono hsubset)
  have hlim :
      Tendsto
        (fun r => μ (gapEvent r X Y (ε / 2)))
        atTop
        (𝓝 (μ (⋃ r, gapEvent r X Y (ε / 2)))) := by
    have h :=
      tendsto_measure_iUnion_atTop
        (μ := μ) (gapEvent_mono X Y (ε / 2))
    change
      Tendsto
        (fun r => μ (gapEvent r X Y (ε / 2)))
        atTop
        (𝓝 (μ (⋃ r, gapEvent r X Y (ε / 2)))) at h
    exact h
  exact (hlim.eventually (Ioi_mem_nhds hunion)).exists

end FactorialChronologicalGrid

end FTAPTheorem42

namespace FTAPTheorem42

/-!
## An explicit right-dense skeleton for nonnegative real time

The factorial chronological grids already provide right approximations of
every `t : ℝ≥0`.  Enumerating all pairs of a grid level and a numerator turns
those approximations into one countable skeleton.  The resulting theorem
removes the skeleton input from the predictable-elementary terminal lower-bound
consumer in the nonnegative-real-time model.
-/

open Filter MeasureTheory Topology
open scoped NNReal

namespace NNRealRightDenseSkeleton

/-- Enumerate all factorial-grid points by pairing a level with a numerator. -/
noncomputable def skeleton (n : ℕ) : ℝ≥0 :=
  let p := Nat.unpair n
  (p.2 : ℝ≥0) / (p.1.factorial : ℝ≥0)

theorem skeleton_rightDense :
    ∀ t : ℝ≥0,
      t ∈ closure (Set.range skeleton ∩ Set.Ici t) := by
  intro t
  apply mem_closure_of_tendsto (FactorialChronologicalGrid.tendsto_approx t)
  filter_upwards [] with r
  refine ⟨?_, FactorialChronologicalGrid.le_approx r t⟩
  refine ⟨Nat.pair r (Nat.ceil (t * (r.factorial : ℝ≥0))), ?_⟩
  simp [skeleton, FactorialChronologicalGrid.approx]

end NNRealRightDenseSkeleton

namespace FiniteVariationFactorialApproximation

open Set

/-- Clamped right factorial approximations converge from within `[x,∞)`. -/
theorem tendsto_min_approx
    {x t : ℝ≥0} (hxt : x ≤ t) :
    Tendsto (fun r => min (FactorialChronologicalGrid.approx r x) t)
      atTop (nhdsWithin x (Ici x)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · simpa [min_eq_left hxt] using
      (FactorialChronologicalGrid.tendsto_approx x).min
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => t) atTop (nhds t))
  · exact Filter.Eventually.of_forall fun r =>
      le_min (FactorialChronologicalGrid.le_approx r x) hxt

/-- A right-continuous path is recovered along the clamped factorial
approximations. -/
theorem tendsto_apply_min_approx
    {E : Type*} [TopologicalSpace E]
    (f : ℝ≥0 → E)
    (hRight : ∀ x, ContinuousWithinAt f (Ici x) x)
    {x t : ℝ≥0} (hxt : x ≤ t) :
    Tendsto
      (fun r => f (min (FactorialChronologicalGrid.approx r x) t))
      atTop (nhds (f x)) :=
  (hRight x).tendsto.comp (tendsto_min_approx hxt)

end FiniteVariationFactorialApproximation

end FTAPTheorem42
