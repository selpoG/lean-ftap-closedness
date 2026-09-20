/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Bounded variation of limits with summable variation steps

A pointwise limit of real paths remains of bounded variation if all paths
have bounded variation and the variations of the consecutive differences are
eventually dominated by a summable real sequence.
-/

namespace FTAPTheorem42

open Filter Set Topology
open scoped BigOperators ENNReal

/-- Extended variation is subadditive for sums of real-valued paths. -/
theorem eVariationOn_add_le_real
    {Time : Type*} [LinearOrder Time]
    (f g : Time → ℝ) (s : Set Time) :
    eVariationOn (fun t => f t + g t) s ≤
      eVariationOn f s + eVariationOn g s := by
  rw [eVariationOn]
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  calc
    (∑ i ∈ Finset.range n,
        edist (f (u (i + 1)) + g (u (i + 1)))
          (f (u i) + g (u i))) ≤
        ∑ i ∈ Finset.range n,
          (edist (f (u (i + 1))) (f (u i)) +
            edist (g (u (i + 1))) (g (u i))) := by
      apply Finset.sum_le_sum
      intro i _
      exact edist_add_add_le
        (f (u (i + 1)) : ℝ) (g (u (i + 1))) (f (u i)) (g (u i))
    _ = (∑ i ∈ Finset.range n,
          edist (f (u (i + 1))) (f (u i))) +
        ∑ i ∈ Finset.range n,
          edist (g (u (i + 1))) (g (u i)) := by
      rw [Finset.sum_add_distrib]
    _ ≤ eVariationOn f s + eVariationOn g s :=
      add_le_add (eVariationOn.sum_le hu hus) (eVariationOn.sum_le hu hus)

/-- A pointwise limit has bounded variation when the consecutive difference
variations are eventually bounded by a summable real sequence. -/
theorem boundedVariationOn_limit_of_summable_step_variation
    {Time : Type*} [LinearOrder Time]
    (F : ℕ → Time → ℝ) (f : Time → ℝ) (q : ℕ → ℝ)
    (hF : ∀ k, BoundedVariationOn (F k) Set.univ)
    (hq : Summable q)
    (hStep : ∀ᶠ k in atTop,
      eVariationOn (fun t => F (k + 1) t - F k t) Set.univ ≤
        ENNReal.ofReal (q k))
    (hLimit : ∀ t, Tendsto (fun k => F k t) atTop (𝓝 (f t))) :
    BoundedVariationOn f Set.univ := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 hStep
  have hShiftSummable : Summable (fun n => q (n + K)) :=
    hq.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  let C : ℝ≥0∞ := eVariationOn (F K) Set.univ +
    ∑' n, ENNReal.ofReal (q (n + K))
  have hCLtTop : C < ⊤ := by
    rw [ENNReal.add_lt_top]
    exact ⟨(hF K).lt_top, hShiftSummable.tsum_ofReal_lt_top⟩
  have hVariationBound : ∀ n,
      eVariationOn (F (n + K)) Set.univ ≤
        eVariationOn (F K) Set.univ +
          ∑ i ∈ Finset.range n, ENNReal.ofReal (q (i + K)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          eVariationOn (F (n + 1 + K)) Set.univ =
              eVariationOn
                (fun t => F (n + K) t +
                  (F (n + K + 1) t - F (n + K) t)) Set.univ := by
            congr 1
            funext t
            rw [show n + 1 + K = n + K + 1 by omega]
            ring
          _ ≤ eVariationOn (F (n + K)) Set.univ +
              eVariationOn
                (fun t => F (n + K + 1) t - F (n + K) t) Set.univ :=
            eVariationOn_add_le_real _ _ _
          _ ≤ (eVariationOn (F K) Set.univ +
                ∑ i ∈ Finset.range n, ENNReal.ofReal (q (i + K))) +
              ENNReal.ofReal (q (n + K)) := by
            exact add_le_add ih (hK (n + K) (by omega))
          _ = eVariationOn (F K) Set.univ +
              ∑ i ∈ Finset.range (n + 1), ENNReal.ofReal (q (i + K)) := by
            rw [Finset.sum_range_succ]
            ac_rfl
  have hVariationLimit : eVariationOn f Set.univ ≤ C := by
    rw [eVariationOn]
    apply iSup_le
    rintro ⟨n, u, hu, hus⟩
    have hPartitionTendsto : Tendsto
        (fun k => ∑ i ∈ Finset.range n,
          edist (F (k + K) (u (i + 1))) (F (k + K) (u i)))
        atTop
        (𝓝 (∑ i ∈ Finset.range n,
          edist (f (u (i + 1))) (f (u i)))) := by
      apply tendsto_finsetSum
      intro i _
      exact ((hLimit (u (i + 1))).comp
        (Filter.tendsto_add_atTop_nat K)).edist
          ((hLimit (u i)).comp (Filter.tendsto_add_atTop_nat K))
    apply le_of_tendsto hPartitionTendsto
    exact Filter.Eventually.of_forall fun k =>
      (eVariationOn.sum_le hu hus).trans <|
        (hVariationBound k).trans <|
          add_le_add le_rfl (ENNReal.sum_le_tsum (Finset.range k))
  exact (hVariationLimit.trans_lt hCLtTop).ne

/-- The variation of the difference between one approximating path and its
pointwise limit is bounded by the tail sum of the consecutive variation
bounds. -/
theorem eVariationOn_limit_sub_le_tsum_tail
    {Time : Type*} [LinearOrder Time]
    (F : ℕ → Time → ℝ) (f : Time → ℝ) (q : ℕ → ℝ)
    (n : ℕ)
    (hStep : ∀ k, n ≤ k →
      eVariationOn (fun t => F (k + 1) t - F k t) Set.univ ≤
        ENNReal.ofReal (q k))
    (hLimit : ∀ t, Tendsto (fun k => F k t) atTop (𝓝 (f t))) :
    eVariationOn (fun t => f t - F n t) Set.univ ≤
      ∑' k, ENNReal.ofReal (q (k + n)) := by
  have hVariationBound : ∀ m,
      eVariationOn (fun t => F (m + n) t - F n t) Set.univ ≤
        ∑ k ∈ Finset.range m, ENNReal.ofReal (q (k + n)) := by
    intro m
    induction m with
    | zero =>
        simp only [zero_add, Finset.range_zero, Finset.sum_empty]
        rw [eVariationOn]
        simp
    | succ m ih =>
        calc
          eVariationOn (fun t => F (m + 1 + n) t - F n t) Set.univ =
              eVariationOn
                (fun t =>
                  (F (m + n) t - F n t) +
                    (F (m + n + 1) t - F (m + n) t)) Set.univ := by
            congr 1
            funext t
            rw [show m + 1 + n = m + n + 1 by omega]
            ring
          _ ≤ eVariationOn (fun t => F (m + n) t - F n t) Set.univ +
                eVariationOn
                  (fun t => F (m + n + 1) t - F (m + n) t) Set.univ :=
            eVariationOn_add_le_real _ _ _
          _ ≤ (∑ k ∈ Finset.range m, ENNReal.ofReal (q (k + n))) +
                ENNReal.ofReal (q (m + n)) :=
            add_le_add ih (hStep (m + n) (by omega))
          _ = ∑ k ∈ Finset.range (m + 1),
                ENNReal.ofReal (q (k + n)) := by
            rw [Finset.sum_range_succ]
  rw [eVariationOn]
  apply iSup_le
  rintro ⟨m, u, hu, hus⟩
  have hPartitionTendsto : Tendsto
      (fun k => ∑ i ∈ Finset.range m,
        edist
          (F (k + n) (u (i + 1)) - F n (u (i + 1)))
          (F (k + n) (u i) - F n (u i)))
      atTop
      (𝓝 (∑ i ∈ Finset.range m,
        edist
          (f (u (i + 1)) - F n (u (i + 1)))
          (f (u i) - F n (u i)))) := by
    apply tendsto_finsetSum
    intro i _
    exact (((hLimit (u (i + 1))).comp
      (Filter.tendsto_add_atTop_nat n)).sub tendsto_const_nhds).edist
        (((hLimit (u i)).comp
          (Filter.tendsto_add_atTop_nat n)).sub tendsto_const_nhds)
  apply le_of_tendsto hPartitionTendsto
  exact Filter.Eventually.of_forall fun k =>
    (eVariationOn.sum_le hu hus).trans <|
      (hVariationBound k).trans <|
        ENNReal.sum_le_tsum (Finset.range k)

/-- Eventually summable bounds on consecutive difference variations force
the full variation distance from the pointwise limit to tend to zero. -/
theorem tendsto_eVariationOn_limit_sub_zero_of_summable_step_variation
    {Time : Type*} [LinearOrder Time]
    (F : ℕ → Time → ℝ) (f : Time → ℝ) (q : ℕ → ℝ)
    (hq : Summable q)
    (hStep : ∀ᶠ k in atTop,
      eVariationOn (fun t => F (k + 1) t - F k t) Set.univ ≤
        ENNReal.ofReal (q k))
    (hLimit : ∀ t, Tendsto (fun k => F k t) atTop (𝓝 (f t))) :
    Tendsto
      (fun k => eVariationOn (fun t => f t - F k t) Set.univ)
      atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 hStep
  have hShiftSummable : Summable (fun k => q (k + K)) :=
    hq.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hTailFinite : (∑' k, ENNReal.ofReal (q (k + K))) ≠ ∞ :=
    hShiftSummable.tsum_ofReal_ne_top
  have hTail : Tendsto
      (fun n => ∑' k, ENNReal.ofReal (q (k + (n + K))))
      atTop (𝓝 0) := by
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ENNReal.tendsto_sum_nat_add
        (fun k => ENNReal.ofReal (q (k + K))) hTailFinite
  have hShift : Tendsto
      (fun n => eVariationOn (fun t => f t - F (n + K) t) Set.univ)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hTail
    · exact fun _ => bot_le
    · intro n
      apply eVariationOn_limit_sub_le_tsum_tail F f q (n + K)
      · intro k hk
        exact hK k (by omega)
      · exact hLimit
  exact (Filter.tendsto_add_atTop_iff_nat K).mp hShift

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## Uniform and variation convergence of centered finite-variation series -/

open Filter Set Topology
open scoped ENNReal

theorem variation_series_convergence {Time : Type*} [LinearOrder Time]
    (f : Nat → Time → Real) (t0 : Time) (hZero : ∀ k, f k t0 = 0)
    (hSum : (∑' k, eVariationOn (f k) univ) ≠ ∞) :
    BoundedVariationOn (fun t => ∑' k, f k t) univ ∧
      TendstoUniformly (fun n t => ∑ k ∈ Finset.range n, f k t) (fun t => ∑' k, f k t) atTop ∧
      Tendsto (fun n => eVariationOn
        (fun t => (∑' k, f k t) - ∑ k ∈ Finset.range n, f k t) univ) atTop (𝓝 0) := by
  let q : Nat → Real := fun k => (eVariationOn (f k) univ).toReal
  have hFinite (k : Nat) : eVariationOn (f k) univ ≠ ∞ :=
    ne_top_of_le_ne_top hSum (ENNReal.le_tsum (f := fun k => eVariationOn (f k) univ) k)
  have hq : Summable q := ENNReal.summable_toReal hSum
  have hBound (k : Nat) (t : Time) : ‖f k t‖ ≤ q k := by
    have h := ENNReal.toReal_mono (hFinite k)
      (eVariationOn.edist_le (f k) (mem_univ t) (mem_univ t0))
    simpa only [hZero k, edist_dist, Real.dist_eq, sub_zero,
      ENNReal.toReal_ofReal (abs_nonneg _), Real.norm_eq_abs] using h
  have hUniform := tendstoUniformly_tsum_nat hq hBound
  let P : Nat → Time → Real := fun n t => ∑ k ∈ Finset.range n, f k t
  have hP : ∀ n, BoundedVariationOn (P n) univ := by
    intro n
    induction n with
    | zero =>
      apply eVariationOn.constant_on (by
        rintro _ ⟨_, _, rfl⟩ _ ⟨_, _, rfl⟩
        rfl) |>.trans_ne ENNReal.zero_ne_top
    | succ n ih =>
      have hEq : P (n + 1) = fun t => P n t + f n t := by
        funext t
        exact Finset.sum_range_succ _ _
      rw [hEq]
      exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨ih, hFinite n⟩)
        (eVariationOn_add_le_real (P n) (f n) univ)
  have hStep : ∀ k, eVariationOn (fun t => P (k + 1) t - P k t) univ ≤ ENNReal.ofReal (q k) := by
    intro k
    have hEq : (fun t => P (k + 1) t - P k t) = f k := by
      funext t
      simp only [P, Finset.sum_range_succ, add_sub_cancel_left]
    rw [hEq, ENNReal.ofReal_toReal (hFinite k)]
  exact ⟨boundedVariationOn_limit_of_summable_step_variation P _ q hP hq
      (Eventually.of_forall hStep) hUniform.tendsto_at, hUniform,
    tendsto_eVariationOn_limit_sub_zero_of_summable_step_variation P _ q hq
      (Eventually.of_forall hStep) hUniform.tendsto_at⟩

end FTAPTheorem42
