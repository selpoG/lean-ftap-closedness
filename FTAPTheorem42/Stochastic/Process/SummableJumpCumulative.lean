/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.FiniteVariation.BoundedVariationLimit
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableStrategyAlgebra
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-! # Right-continuous bounded-variation cumulative sums of summable jumps -/

namespace FTAPTheorem42.SummableJumpCumulative

open Filter Set Topology
open scoped NNReal

noncomputable def cumulative {ι : Type*} (time : ι → NNReal) (a : ι → Real) : NNReal → Real :=
  fun t => ∑' i, if time i ≤ t then a i else 0

private theorem summable_step {ι : Type*} (time : ι → NNReal) {a : ι → Real}
    (ha : Summable a) (t : NNReal) : Summable (fun i => if time i ≤ t then a i else 0) := by
  classical
  exact (ha.indicator {i | time i ≤ t}).congr (fun i => by
    simp only [Set.indicator_apply, Set.mem_ofPred_eq])

theorem rightContinuous {ι : Type*} (time : ι → NNReal) {a : ι → Real}
    (ha : Summable a) (t : NNReal) :
    ContinuousWithinAt (cumulative time a) (Ici t) t := by
  classical
  apply tendsto_tsum_of_dominated_convergence ha.abs
  · intro i
    by_cases hi : time i ≤ t
    · have hEq : (fun u : NNReal => if time i ≤ u then a i else 0) =ᶠ[𝓝[Ici t] t]
          (fun _ => a i) := by
        filter_upwards [self_mem_nhdsWithin] with u hu
        simp [hi.trans hu]
      simpa only [ite_eq_left hi] using tendsto_const_nhds.congr' hEq.symm
    · have hEq : (fun u : NNReal => if time i ≤ u then a i else 0) =ᶠ[𝓝[Ici t] t]
          (fun _ => 0) := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_of_not_ge hi))] with u hu
        simp [not_le_of_gt (show u < time i from hu)]
      simpa only [ite_eq_right hi] using tendsto_const_nhds.congr' hEq.symm
  · apply Eventually.of_forall
    intro u i
    split_ifs <;> simp

private theorem monotone_of_nonneg {ι : Type*} (time : ι → NNReal) {a : ι → Real}
    (ha : Summable a) (hpos : ∀ i, 0 ≤ a i) : Monotone (cumulative time a) := by
  classical
  intro s t hst
  apply (summable_step time ha s).tsum_le_tsum _ (summable_step time ha t)
  intro i
  split_ifs with hs ht ht
  · exact le_rfl
  · exact (ht (hs.trans hst)).elim
  · exact hpos i
  · exact le_rfl

private theorem boundedVariation_of_nonneg {ι : Type*} (time : ι → NNReal) {a : ι → Real}
    (ha : Summable a) (hpos : ∀ i, 0 ≤ a i) : BoundedVariationOn (cumulative time a) univ := by
  classical
  apply ((monotone_of_nonneg time ha hpos).monotoneOn univ).boundedVariationOn
    (C := ∑' i, a i)
  intro t _
  have hp : 0 ≤ cumulative time a t := tsum_nonneg (fun i => by split_ifs <;> simp [hpos])
  rw [abs_of_nonneg hp]
  apply (summable_step time ha t).tsum_le_tsum _ ha
  intro i
  split_ifs <;> simp [hpos]

theorem boundedVariation {ι : Type*} (time : ι → NNReal) {a : ι → Real}
    (ha : Summable a) : BoundedVariationOn (cumulative time a) univ := by
  classical
  have hAbs : Summable (fun i => |a i|) := ha.abs
  have hPlus := ha.add hAbs
  have hBV := boundedVariationOn_add
    (boundedVariation_of_nonneg time hPlus (fun i => by linarith [neg_abs_le (a i)]))
    (boundedVariationOn_neg (boundedVariation_of_nonneg time hAbs (fun i => abs_nonneg _)))
  have hEq : cumulative time a = fun t =>
      cumulative time (fun i => a i + |a i|) t + -cumulative time (fun i => |a i|) t := by
    funext t
    unfold cumulative
    rw [← tsum_neg, ← (summable_step time hPlus t).tsum_add
      (summable_step time hAbs t).neg]
    apply tsum_congr
    intro i
    split_ifs <;> ring
  rw [hEq]
  exact hBV

/-- A fixed finite horizon supplies one index type for all earlier times. -/
theorem cumulative_Ioc_eq (a : NNReal → Real) {t T : NNReal} (ht : t ≤ T) :
    cumulative (fun s : Ioc (0 : NNReal) T => s.val) (fun s => a s) t =
      ∑' s : Ioc (0 : NNReal) t, a s := by
  classical
  unfold cumulative
  rw [tsum_subtype (Ioc (0 : NNReal) T) (fun s => if s ≤ t then a s else 0),
    tsum_subtype (Ioc (0 : NNReal) t) a]
  apply tsum_congr
  intro s
  by_cases hs : s ∈ Ioc (0 : NNReal) t
  · have hsT : s ∈ Ioc (0 : NNReal) T := ⟨hs.1, hs.2.trans ht⟩
    simp [hs, hsT, hs.2]
  · by_cases hsT : s ∈ Ioc (0 : NNReal) T
    · have hst : ¬s ≤ t := fun h => hs ⟨hsT.1, h⟩
      simp [hs, hsT, hst]
    · simp [hs, hsT]

/-- Local absolute summability gives right continuity of the cumulative
sum, without choosing an enumeration of its jump support. -/
theorem rightContinuous_Ioc (a : NNReal → Real)
    (ha : ∀ T : NNReal, Summable (fun s : Ioc (0 : NNReal) T => a s)) (t : NNReal) :
    ContinuousWithinAt (fun u => ∑' s : Ioc (0 : NNReal) u, a s) (Ici t) t := by
  have h := rightContinuous (fun s : Ioc (0 : NNReal) (t + 1) => s.val) (ha (t + 1)) t
  apply h.congr_of_eventuallyEq_of_mem _ (mem_Ici.mpr le_rfl)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by
    exact lt_add_one t))] with u hu
  exact (cumulative_Ioc_eq a (show u ≤ t + 1 from le_of_lt hu)).symm

theorem locallyBoundedVariation_Ioc (a : NNReal → Real)
    (ha : ∀ T : NNReal, Summable (fun s : Ioc (0 : NNReal) T => a s)) :
    LocallyBoundedVariationOn (fun u => ∑' s : Ioc (0 : NNReal) u, a s) univ := by
  intro u v _ _
  have h := (boundedVariation (fun s : Ioc (0 : NNReal) v => s.val) (ha v)).mono
    (inter_subset_left : univ ∩ Icc u v ⊆ univ)
  change eVariationOn _ _ ≠ ⊤ at h ⊢
  rw [eVariationOn.congr (f := cumulative (fun s : Ioc (0 : NNReal) v => s.val) (fun s => a s))
    (fun t ht => cumulative_Ioc_eq a ht.2.2)] at h
  exact h

end FTAPTheorem42.SummableJumpCumulative

namespace FTAPTheorem42.SummableJumpCumulative

/-! ## Left jumps of locally summable cumulative jump series -/

open Filter Function Set Topology
open scoped NNReal

theorem tendsto_left {ι : Type*} (time : ι → NNReal) {a : ι → Real}
    (ha : Summable a) (t : NNReal) :
    Tendsto (cumulative time a) (𝓝[<] t)
      (𝓝 (∑' i, if time i < t then a i else 0)) := by
  classical
  apply tendsto_tsum_of_dominated_convergence ha.abs
  · intro i
    by_cases hi : time i < t
    · have hEq : (fun u : NNReal => if time i ≤ u then a i else 0) =ᶠ[𝓝[<] t]
          (fun _ => a i) := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hi)] with u hu
        simp [le_of_lt (show time i < u from hu)]
      simpa only [ite_eq_left hi] using tendsto_const_nhds.congr' hEq.symm
    · have hEq : (fun u : NNReal => if time i ≤ u then a i else 0) =ᶠ[𝓝[<] t]
          (fun _ => 0) := by
        filter_upwards [self_mem_nhdsWithin] with u hu
        simp [not_le_of_gt (lt_of_lt_of_le (show u < t from hu) (le_of_not_gt hi))]
      simpa only [ite_eq_right hi] using tendsto_const_nhds.congr' hEq.symm
  · apply Eventually.of_forall
    intro u i
    split_ifs <;> simp

theorem leftJump_Ioc (a : NNReal → Real)
    (ha : ∀ T : NNReal, Summable (fun s : Ioc (0 : NNReal) T => a s))
    {t : NNReal} (ht : 0 < t) :
    (∑' s : Ioc (0 : NNReal) t, a s) -
      leftLim (fun u => ∑' s : Ioc (0 : NNReal) u, a s) t = a t := by
  classical
  let b : Ioc (0 : NNReal) t → Real := fun s => if s.val < t then a s else 0
  have hb : Summable b := ((ha t).indicator {s | s.val < t}).congr (fun s => by
    simp only [b, Set.indicator_apply, Set.mem_ofPred_eq])
  have hLim : Tendsto (fun u => ∑' s : Ioc (0 : NNReal) u, a s) (𝓝[<] t)
      (𝓝 (∑' s, b s)) := by
    apply (tendsto_left (fun s : Ioc (0 : NNReal) t => s.val) (ha t) t).congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact cumulative_Ioc_eq a (le_of_lt hu)
  have : (𝓝[<] t).NeBot := nhdsWithin_Iio_neBot' ⟨0, ht⟩ le_rfl
  rw [leftLim_eq_of_tendsto hLim, ← (ha t).tsum_sub hb]
  let top : Ioc (0 : NNReal) t := ⟨t, ht, le_rfl⟩
  rw [tsum_eq_single top]
  · simp [b, top]
  · intro s hs
    have hst : s.val < t := lt_of_le_of_ne s.property.2 (fun h => hs (Subtype.ext h))
    simp [b, hst]

end FTAPTheorem42.SummableJumpCumulative
