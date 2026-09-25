/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.FactorialChronologicalGrid
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.EMetricSpace.VariationOnFromTo

/-!
# Factorial-grid approximation of path variation

For a right-continuous path on nonnegative time, its variation on a finite
interval is detected by the nested factorial grids.  The approximating
variation is a finite sum of fixed-time increments.  This countable
representation is the deterministic input needed to prove measurability of
the cumulative variation of an adapted finite-variation process.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace FTAPTheorem42

namespace FiniteVariationFactorialApproximation

/-- A monotone subsequence of a finite chain has no more variation than the
whole chain. -/
theorem sum_edist_comp_le_range_sum_edist
    {E : Type*} [PseudoEMetricSpace E]
    (f : ℕ → E) {j : ℕ → ℕ} {n N : ℕ}
    (hj : MonotoneOn j (Iic n)) (hN : j n ≤ N) :
    (∑ i ∈ Finset.range n, edist (f (j (i + 1))) (f (j i))) ≤
      ∑ k ∈ Finset.range N, edist (f (k + 1)) (f k) := by
  have hmono (i : ℕ) (hi : i < n) : j i ≤ j (i + 1) :=
    hj (mem_Iic.2 hi.le) (mem_Iic.2 (Nat.succ_le_iff.2 hi))
      (Nat.le_succ i)
  calc
    (∑ i ∈ Finset.range n, edist (f (j (i + 1))) (f (j i))) ≤
        ∑ i ∈ Finset.range n,
          ∑ k ∈ Finset.Ico (j i) (j (i + 1)), edist (f k) (f (k + 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [edist_comm] using
        edist_le_Ico_sum_edist f (hmono i (Finset.mem_range.1 hi))
    _ = ∑ k ∈ Finset.Ico (j 0) (j n), edist (f k) (f (k + 1)) := by
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Finset.sum_range_succ, ih
            (hj.mono (Iic_subset_Iic.2 (Nat.le_succ n)))
            ((hmono n (Nat.lt_succ_self n)).trans hN)
            (fun i hi => hmono i (hi.trans (Nat.lt_succ_self n)))]
          rw [Finset.sum_Ico_consecutive]
          · exact hj (mem_Iic.2 (Nat.zero_le _)) (mem_Iic.2 (Nat.le_succ n))
              (Nat.zero_le n)
          · exact hmono n (Nat.lt_succ_self n)
    _ ≤ ∑ k ∈ Finset.range N, edist (f (k + 1)) (f k) := by
      simpa only [edist_comm] using
        (Finset.sum_mono_set (fun k => edist (f k) (f (k + 1)))
          (fun k hk => by
            rw [Finset.mem_Ico] at hk
            rw [Finset.mem_range]
            exact hk.2.trans_le hN))

/-- The level-`r` factorial point, clamped at the terminal time `t`. -/
noncomputable def point (t : ℝ≥0) (r k : ℕ) : ℝ≥0 :=
  min ((k : ℝ≥0) / (r.factorial : ℝ≥0)) t

/-- Variation of a path along the level-`r` factorial grid, stopped at `t`. -/
noncomputable def eGridVariation
    {E : Type*} [PseudoEMetricSpace E]
    (f : ℝ≥0 → E) (t : ℝ≥0) (r : ℕ) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range (r * r.factorial),
    edist (f (point t r (k + 1))) (f (point t r k))

theorem point_monotone (t : ℝ≥0) (r : ℕ) :
    Monotone (point t r) := by
  intro k l hkl
  exact min_le_min_right t
    (div_le_div_of_nonneg_right (by exact_mod_cast hkl) (by positivity))

theorem point_mem_Icc (t : ℝ≥0) (r k : ℕ) :
    point t r k ∈ Icc 0 t :=
  ⟨bot_le, min_le_right _ _⟩

/-- Every factorial-grid variation is bounded by the full path variation. -/
theorem eGridVariation_le_eVariationOn
    {E : Type*} [PseudoEMetricSpace E]
    (f : ℝ≥0 → E) (t : ℝ≥0) (r : ℕ) :
    eGridVariation f t r ≤ eVariationOn f (Icc 0 t) := by
  exact eVariationOn.sum_le_of_monotoneOn_Iic
    (fun _ _ _ _ hij => point_monotone t r hij)
    (fun i _ => point_mem_Icc t r i)

@[simp]
theorem point_approxNatIndex (t x : ℝ≥0) (r : ℕ) :
    point t r (FactorialChronologicalGrid.approxNatIndex r x) =
      min (FactorialChronologicalGrid.approx r x) t :=
  rfl

theorem approxNatIndex_mono (r : ℕ) :
    Monotone (FactorialChronologicalGrid.approxNatIndex r) := by
  intro x y hxy
  exact Nat.ceil_mono
    (mul_le_mul_of_nonneg_right hxy (by positivity))

theorem approxNatIndex_le_gridSize
    {t x : ℝ≥0} (hxt : x ≤ t) {r : ℕ} (hr : Nat.ceil t ≤ r) :
    FactorialChronologicalGrid.approxNatIndex r x ≤ r * r.factorial := by
  exact (approxNatIndex_mono r hxt).trans
    (Nat.le_of_lt_succ
      (FactorialChronologicalGrid.ceil_mul_factorial_lt_gridSize t hr))

/-- Right-continuity reduces variation on `[0,t]` to the countable family of
finite factorial-grid variations. -/
theorem eVariationOn_Icc_eq_iSup_eGridVariation
    {E : Type*} [PseudoEMetricSpace E]
    (f : ℝ≥0 → E)
    (hRight : ∀ x, ContinuousWithinAt f (Ici x) x)
    (t : ℝ≥0) :
    eVariationOn f (Icc 0 t) = ⨆ r, eGridVariation f t r := by
  apply le_antisymm
  · rw [eVariationOn.eVariationOn_eq_strictMonoOn]
    apply iSup_le
    rintro ⟨n, u, hu, hmem⟩
    let j : ℕ → ℕ → ℕ := fun r i => FactorialChronologicalGrid.approxNatIndex r (u i)
    have hj (r : ℕ) : MonotoneOn (j r) (Iic n) :=
      (approxNatIndex_mono r).comp_monotoneOn
        hu.monotoneOn
    have hpoint (i : ℕ) (hi : i ≤ n) :
        Tendsto (fun r => f (point t r (j r i))) atTop (nhds (f (u i))) := by
      rw [show (fun r => f (point t r (j r i))) =
          fun r => f (min (FactorialChronologicalGrid.approx r (u i)) t) by
        funext r
        exact congrArg f (point_approxNatIndex t (u i) r)]
      exact tendsto_apply_min_approx f hRight (hmem i (mem_Iic.2 hi)).2
    have hlim :
        Tendsto
          (fun r => ∑ i ∈ Finset.range n,
            edist (f (point t r (j r (i + 1))))
              (f (point t r (j r i))))
          atTop
          (nhds (∑ i ∈ Finset.range n,
            edist (f (u (i + 1))) (f (u i)))) := by
      apply tendsto_finsetSum
      intro i hi
      have hi' : i < n := Finset.mem_range.1 hi
      exact Tendsto.edist
        (hpoint (i + 1) (Nat.succ_le_iff.2 hi'))
        (hpoint i hi'.le)
    apply le_of_tendsto hlim
    filter_upwards [eventually_ge_atTop (Nat.ceil t)] with r hr
    refine (sum_edist_comp_le_range_sum_edist
      (fun k => f (point t r k)) (hj r)
      (approxNatIndex_le_gridSize (hmem n (mem_Iic.2 le_rfl)).2 hr)).trans ?_
    exact le_iSup (fun q => eGridVariation f t q) r
  · exact iSup_le fun r => eGridVariation_le_eVariationOn f t r

/-- Real path variation is the real part of the countable factorial-grid
supremum. -/
theorem variationOnFromTo_eq_iSup_eGridVariation_toReal
    {E : Type*} [PseudoEMetricSpace E]
    (f : ℝ≥0 → E)
    (hRight : ∀ x, ContinuousWithinAt f (Ici x) x)
    (t : ℝ≥0) :
    variationOnFromTo f Set.univ 0 t =
      (⨆ r, eGridVariation f t r).toReal := by
  change variationOnFromTo f Set.univ (⊥ : ℝ≥0) t = _
  rw [variationOnFromTo.eq_of_le f Set.univ bot_le, Set.univ_inter]
  congr 1
  simpa using eVariationOn_Icc_eq_iSup_eGridVariation f hRight t

/-- Measurability up to the terminal time and right-continuous paths make
cumulative path variation measurable.  The bounded-horizon formulation is
the one needed to retain filtration measurability. -/
theorem measurable_variationOnFromTo_of_le
    {Ω E : Type*} [MeasurableSpace Ω]
    [PseudoEMetricSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    (X : ℝ≥0 → Ω → E)
    (t : ℝ≥0)
    (hMeas : ∀ s ≤ t, Measurable (X s))
    (hRight : ∀ ω s, ContinuousWithinAt (fun u => X u ω) (Ici s) s) :
    Measurable fun ω => variationOnFromTo (fun s => X s ω) Set.univ 0 t := by
  have hEq :
      (fun ω => variationOnFromTo (fun s => X s ω) Set.univ 0 t) =
        (fun ω => (⨆ r, eGridVariation (fun s => X s ω) t r).toReal) := by
    funext ω
    exact variationOnFromTo_eq_iSup_eGridVariation_toReal
      (fun s => X s ω) (hRight ω) t
  rw [hEq]
  apply Measurable.ennreal_toReal
  apply Measurable.iSup
  intro r
  unfold eGridVariation
  apply Finset.measurable_fun_sum
  intro k _
  exact (hMeas (point t r (k + 1)) (point_mem_Icc t r (k + 1)).2).edist
    (hMeas (point t r k) (point_mem_Icc t r k).2)

end FiniteVariationFactorialApproximation

end FTAPTheorem42
