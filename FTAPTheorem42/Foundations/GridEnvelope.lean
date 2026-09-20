/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.Envelope

/-! # Measurable grid envelopes and their pointwise bounds -/

open Filter MeasureTheory Set Topology
open scoped ENNReal MeasureTheory NNReal ProbabilityTheory

namespace FTAPTheorem42

namespace FactorialChronologicalGrid

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Squared extended envelope, convenient for monotone convergence. -/
noncomputable def eFactorialRunningMaxSqEnvelope
    (f : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) : Ω → ℝ≥0∞ :=
  fun ω => ⨆ r, ENNReal.ofReal ((factorialRunningMax f T r ω) ^ 2)

theorem measurable_factorialRunningMax
    (f : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (r : ℕ)
    (hf : ∀ t, Measurable (f t)) :
    Measurable (factorialRunningMax f T r) := by
  apply measurable_finiteRunningMax
  intro k hk
  exact hf ((stoppedGrid T r).sampledTime k)

theorem measurable_eFactorialRunningMaxSqEnvelope
    (f : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (hf : ∀ t, Measurable (f t)) :
    Measurable (eFactorialRunningMaxSqEnvelope f T) := by
  apply Measurable.iSup
  intro r
  exact ((measurable_factorialRunningMax f T r hf).pow_const 2).ennreal_ofReal

omit [MeasurableSpace Ω] in
theorem range_stoppedGrid_subset_succ (T : ℝ≥0) (r : ℕ) :
    Set.range (stoppedGrid T r).time ⊆
      Set.range (stoppedGrid T (r + 1)).time := by
  rintro _ ⟨k, rfl⟩
  obtain ⟨l, hl⟩ := range_grid_subset_succ r ⟨k, rfl⟩
  exact ⟨l, by simp only [stoppedGrid_time, hl]⟩

omit [MeasurableSpace Ω] in
theorem factorialRunningMax_mono
    (f : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) :
    Monotone (factorialRunningMax f T) := by
  apply monotone_nat_of_le_succ
  intro r ω
  obtain ⟨k, hk, hkEq⟩ := Finset.exists_mem_eq_sup'
    (s := Finset.range (r * r.factorial + 1))
    Finset.nonempty_range_add_one
    (fun j => (stoppedGrid T r).natSample f j ω)
  have hkN : k ≤ r * r.factorial :=
    Nat.le_of_lt_succ (Finset.mem_range.1 hk)
  have hkIndex : (stoppedGrid T r).natIndex k =
      ⟨k, Nat.lt_succ_of_le hkN⟩ := by
    apply Fin.ext
    exact min_eq_left hkN
  obtain ⟨l, hl⟩ := range_stoppedGrid_subset_succ T r
    ⟨(stoppedGrid T r).natIndex k, rfl⟩
  have hlN : l.1 ≤ (r + 1) * (r + 1).factorial :=
    Nat.le_of_lt_succ l.2
  have hlIndex : (stoppedGrid T (r + 1)).natIndex l.1 = l := by
    apply Fin.ext
    exact min_eq_left hlN
  rw [show factorialRunningMax f T r ω =
      (stoppedGrid T r).natSample f k ω by
    exact hkEq]
  calc
    (stoppedGrid T r).natSample f k ω =
        (stoppedGrid T (r + 1)).natSample f l.1 ω := by
      simp only [ChronologicalGrid.natSample,
        ChronologicalGrid.sampledTime, hkIndex, hlIndex, hl]
    _ ≤ factorialRunningMax f T (r + 1) ω := by
      exact Finset.le_sup' (fun j =>
        (stoppedGrid T (r + 1)).natSample f j ω)
        (Finset.mem_range.2 (Nat.lt_succ_iff.2 hlN))

omit [MeasurableSpace Ω] in
/-- The extended factorial envelope dominates every value up to `T` for a
right-continuous path after applying `ENNReal.ofReal`. -/
theorem ofReal_le_eFactorialRunningMaxEnvelope
    (f : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (hRight : ∀ ω t, ContinuousWithinAt (f · ω) (Ici t) t)
    (ω : Ω) {t : ℝ≥0} (ht : t ≤ T) :
    ENNReal.ofReal (f t ω) ≤ eFactorialRunningMaxEnvelope f T ω := by
  have hlim : Tendsto
      (fun r => f (min (approx r t) T) ω) atTop (𝓝 (f t ω)) :=
    FiniteVariationFactorialApproximation.tendsto_apply_min_approx
      (fun s => f s ω) (hRight ω) ht
  apply le_of_tendsto (ENNReal.tendsto_ofReal hlim)
  filter_upwards [eventually_ge_atTop (max (Nat.ceil t) (Nat.ceil T))]
    with r hr
  have hrt : Nat.ceil t ≤ r := le_max_left _ _ |>.trans hr
  have hrT : Nat.ceil T ≤ r := le_max_right _ _ |>.trans hr
  let k := FactorialChronologicalGrid.approxIndex t hrt
  have hkN : k.1 ≤ r * r.factorial := Nat.le_of_lt_succ k.2
  have hkIndex : (stoppedGrid T r).natIndex k.1 = k := by
    ext
    simp [ChronologicalGrid.natIndex, min_eq_left hkN]
  have hvalue : f (min (approx r t) T) ω ≤
      factorialRunningMax f T r ω := by
    calc
      f (min (approx r t) T) ω =
          (stoppedGrid T r).natSample f k.1 ω := by
        simp only [ChronologicalGrid.natSample,
          ChronologicalGrid.sampledTime, hkIndex, stoppedGrid_time]
        rw [show (grid r).time k = approx r t by
          exact grid_time_approxIndex t hrt]
      _ ≤ factorialRunningMax f T r ω :=
        Finset.le_sup' (fun j => (stoppedGrid T r).natSample f j ω)
          (Finset.mem_range.2 (Nat.lt_succ_iff.2 hkN))
  exact (ENNReal.ofReal_le_ofReal hvalue).trans
    (le_iSup (fun q => ENNReal.ofReal
      (factorialRunningMax f T q ω)) r)

omit [MeasurableSpace Ω] in
theorem ofReal_sq_le_eFactorialRunningMaxSqEnvelope
    (f : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (hf_nonneg : 0 ≤ f)
    (hRight : ∀ ω t, ContinuousWithinAt (f · ω) (Ici t) t)
    (ω : Ω) {t : ℝ≥0} (ht : t ≤ T) :
    ENNReal.ofReal ((f t ω) ^ 2) ≤
      eFactorialRunningMaxSqEnvelope f T ω := by
  have hlim : Tendsto
      (fun r => (f (min (approx r t) T) ω) ^ 2)
      atTop (𝓝 ((f t ω) ^ 2)) := by
    have hbase :=
      FiniteVariationFactorialApproximation.tendsto_apply_min_approx
        (fun s => f s ω) (hRight ω) ht
    simpa only [pow_two] using hbase.mul hbase
  apply le_of_tendsto (ENNReal.tendsto_ofReal hlim)
  filter_upwards [eventually_ge_atTop (max (Nat.ceil t) (Nat.ceil T))]
    with r hr
  have hrt : Nat.ceil t ≤ r := le_max_left _ _ |>.trans hr
  let k := FactorialChronologicalGrid.approxIndex t hrt
  have hkN : k.1 ≤ r * r.factorial := Nat.le_of_lt_succ k.2
  have hkIndex : (stoppedGrid T r).natIndex k.1 = k := by
    apply Fin.ext
    exact min_eq_left hkN
  have hvalue : f (min (approx r t) T) ω ≤
      factorialRunningMax f T r ω := by
    calc
      f (min (approx r t) T) ω =
          (stoppedGrid T r).natSample f k.1 ω := by
        simp only [ChronologicalGrid.natSample,
          ChronologicalGrid.sampledTime, hkIndex, stoppedGrid_time]
        rw [show (grid r).time k = approx r t by
          exact grid_time_approxIndex t hrt]
      _ ≤ factorialRunningMax f T r ω :=
        Finset.le_sup' (fun j => (stoppedGrid T r).natSample f j ω)
          (Finset.mem_range.2 (Nat.lt_succ_iff.2 hkN))
  have hsquare : (f (min (approx r t) T) ω) ^ 2 ≤
      (factorialRunningMax f T r ω) ^ 2 := by
    apply (sq_le_sq₀ (hf_nonneg _ ω) ?_).2 hvalue
    exact finiteRunningMax_nonneg _ _
      (fun k ω => hf_nonneg ((stoppedGrid T r).sampledTime k) ω) ω
  exact (ENNReal.ofReal_le_ofReal hsquare).trans
    (le_iSup (fun q => ENNReal.ofReal
      ((factorialRunningMax f T q ω) ^ 2)) r)

end FactorialChronologicalGrid

end FTAPTheorem42
