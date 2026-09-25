/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Core.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# A common almost-everywhere subsequence for countably many coordinates

Coordinatewise convergence in measure has one strictly increasing
subsequence which converges almost everywhere in every coordinate. At stage
`k` we control the first `k + 1` coordinates with geometric error, and then
use the first Borel--Cantelli lemma.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Countably many convergences in measure have one common a.e.-convergent
strict subsequence. -/
theorem exists_strictMono_tendstoAE_of_countable_tendstoInMeasure
    {f : Nat → Nat → Omega → Real} {g : Nat → Omega → Real}
    {mu : Measure Omega}
    (hfg : ∀ j, TendstoInMeasure mu (fun n => f n j) atTop (g j)) :
    ∃ cutoff : Nat → Nat, StrictMono cutoff ∧
      ∀ j, TendstoAE mu (fun k => f (cutoff k) j) (g j) := by
  classical
  let q : Nat → ENNReal := fun k => (2 : ENNReal)⁻¹ ^ (k + 1)
  have hqPos : ∀ k, 0 < q k := by
    intro k
    exact ENNReal.pow_pos (ENNReal.inv_pos.mpr (by norm_num)) _
  have hFinite : ∀ k, ∃ N, ∀ j, j ≤ k → ∀ n, N ≤ n →
      mu {omega | q k ≤ edist (f n j omega) (g j omega)} ≤ q k := by
    intro k
    have hOne : ∀ j, ∃ N, ∀ n, N ≤ n →
        mu {omega | q k ≤ edist (f n j omega) (g j omega)} ≤ q k := by
      intro j
      have hlim := hfg j (q k) (hqPos k)
      have hev : ∀ᶠ n in atTop,
          mu {omega | q k ≤ edist (f n j omega) (g j omega)} < q k :=
        (tendsto_order.1 hlim).2 _ (hqPos k)
      rcases eventually_atTop.1 hev with ⟨N, hN⟩
      exact ⟨N, fun n hn => (hN n hn).le⟩
    choose N hN using hOne
    refine ⟨(Finset.range (k + 1)).sup N, ?_⟩
    intro j hj n hn
    have hjMem : j ∈ Finset.range (k + 1) := Finset.mem_range.2 (by omega)
    exact hN j n ((Finset.le_sup hjMem).trans hn)
  choose threshold hThreshold using hFinite
  let cutoff : Nat → Nat := fun k =>
    Nat.rec (threshold 0)
      (fun i previous => max (previous + 1) (threshold (i + 1))) k
  have hThresholdCutoff : ∀ k, threshold k ≤ cutoff k := by
    intro k
    induction k with
    | zero => simp [cutoff]
    | succ k _ =>
        dsimp only [cutoff]
        exact le_max_right _ _
  have hCutoffLt : ∀ k, cutoff k < cutoff (k + 1) := by
    intro k
    dsimp only [cutoff]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  have hCutoff : StrictMono cutoff := strictMono_nat_of_lt_succ hCutoffLt
  have hqSummable : (∑' k, q k) ≠ ∞ := by
    simp only [q]
    rw [ENNReal.tsum_geometric_add_one]
    norm_num
  have hqTendsto : Tendsto q atTop (nhds 0) := by
    change Tendsto
      ((fun k : Nat => (2 : ENNReal)⁻¹ ^ k) ∘ fun k => k + 1)
      atTop (nhds 0)
    exact (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (2 : ENNReal)⁻¹ < 1)).comp (tendsto_add_atTop_nat 1)
  refine ⟨cutoff, hCutoff, ?_⟩
  intro j
  let bad : Nat → Set Omega := fun k =>
    if j ≤ k then
      {omega | q k ≤ edist (f (cutoff k) j omega) (g j omega)}
    else ∅
  have hbad : ∀ k, mu (bad k) ≤ q k := by
    intro k
    by_cases hjk : j ≤ k
    · simp only [bad, ite_eq_left hjk]
      exact hThreshold k j hjk (cutoff k) (hThresholdCutoff k)
    · simp [bad, hjk]
  have hsumBad : (∑' k, mu (bad k)) ≠ ∞ := by
    apply ne_top_of_le_ne_top hqSummable
    exact ENNReal.tsum_le_tsum hbad
  have haeGood : ∀ᵐ omega ∂mu, ∀ᶠ k in atTop, omega ∉ bad k :=
    MeasureTheory.ae_eventually_notMem (μ := mu) (s := bad) hsumBad
  filter_upwards [haeGood] with omega homega
  apply EMetric.tendsto_atTop.2
  intro epsilon hepsilon
  have hqSmall : ∀ᶠ k in atTop, q k < epsilon :=
    (tendsto_order.1 hqTendsto).2 epsilon hepsilon
  apply eventually_atTop.1
  filter_upwards [homega, hqSmall, eventually_ge_atTop j] with k hgood hsmall hjk
  have hnot : ¬ q k ≤ edist (f (cutoff k) j omega) (g j omega) := by
    simpa only [bad, ite_eq_left hjk, Set.mem_ofPred_eq] using hgood
  exact (lt_of_not_ge hnot).trans hsmall

end FTAPTheorem42
