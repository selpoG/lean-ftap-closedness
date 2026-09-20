import FTAPTheorem42.Foundations.CommonHilbertConvexification
import FTAPTheorem42.Trading.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Maximal-difference Cauchy extraction

This file contains the concrete subsequence extraction used when all time
coordinates are controlled by one maximal pairwise difference.  The selected
subsequence is independent of the time coordinate, and the conclusion is a
pathwise bound for every one of the countably many coordinates.
-/

open Filter MeasureTheory Topology
open scoped BigOperators ENNReal MeasureTheory ProbabilityTheory lp

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

section MaximalDifference

variable {μ : Measure Ω}

/-- Retain the summable all-time increments of the existing extraction.
This form also supplies uniform limits, without a boundedness anchor. -/
theorem exists_strictMono_ae_fast_steps_of_allTimeGap_cauchyInMeasure
    {Time : Type*} (u : ℕ → Time → Ω → ℝ)
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ →
      ∃ N, ∀ n m, N ≤ n → N ≤ m →
        μ {ω | ∃ t, ε ≤ ‖u n t ω - u m t ω‖} ≤ ENNReal.ofReal δ) :
    ∃ cutoff : ℕ → ℕ, StrictMono cutoff ∧
      ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, ∀ t,
        ‖u (cutoff (k + 1)) t ω - u (cutoff k) t ω‖ <
          ((1 : ℝ) / 2) ^ (k + 1) := by
  classical
  let q : ℕ → ℝ := fun k => ((1 : ℝ) / 2) ^ (k + 1)
  have hraw : ∀ k : ℕ, ∃ N : ℕ, ∀ n m, N ≤ n → N ≤ m →
      μ {ω | ∃ t, q k ≤ ‖u n t ω - u m t ω‖} ≤
        ENNReal.ofReal (q k) := by
    intro k
    exact hcauchy (q k) (by positivity) (q k) (by positivity)
  choose witness hwitness using hraw
  let cutoff : ℕ → ℕ := fun k =>
    Nat.rec (witness 0)
      (fun i previous => max (previous + 1) (witness (i + 1))) k
  have hwitness_le_cutoff : ∀ k, witness k ≤ cutoff k := by
    intro k
    induction k with
    | zero =>
        simp [cutoff]
    | succ k ih =>
        dsimp [cutoff]
        exact le_max_right _ _
  have cutoff_lt_succ : ∀ k, cutoff k < cutoff (k + 1) := by
    intro k
    dsimp [cutoff]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  have hcutoff : StrictMono cutoff :=
    strictMono_nat_of_lt_succ cutoff_lt_succ
  let bad : ℕ → Set Ω := fun k =>
    {ω | ∃ t, q k ≤
      ‖u (cutoff (k + 1)) t ω - u (cutoff k) t ω‖}
  have hbad_measure : ∀ k, μ (bad k) ≤ ENNReal.ofReal (q k) := by
    intro k
    have h := hwitness k (cutoff (k + 1)) (cutoff k)
      (le_trans (hwitness_le_cutoff k)
        (hcutoff.monotone (Nat.le_succ k)))
      (hwitness_le_cutoff k)
    simpa [bad] using h
  have hqsum : Summable q := by
    simpa [q, pow_succ, mul_comm] using
      (summable_geometric_two.mul_left ((1 : ℝ) / 2))
  have hsum_ennreal : (∑' k, ENNReal.ofReal (q k)) ≠ ∞ :=
    hqsum.tsum_ofReal_ne_top
  have hsum_bad : (∑' k, μ (bad k)) ≠ ∞ := by
    apply ne_top_of_le_ne_top hsum_ennreal
    exact ENNReal.tsum_le_tsum hbad_measure
  have hae_bad : ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, ω ∉ bad k :=
    MeasureTheory.ae_eventually_notMem (μ := μ) (s := bad) hsum_bad
  refine ⟨cutoff, hcutoff, ?_⟩
  filter_upwards [hae_bad] with ω hω
  filter_upwards [hω] with k hk
  intro t
  exact lt_of_not_ge (fun hge => hk ⟨t, hge⟩)

/--
The all-time gap-event form of the uniform extraction theorem.  No separate
real-valued maximal-difference majorant is required: the all-time gap events
themselves are the summable bad events.
-/
theorem exists_strictMono_ae_uniform_bddAbove_of_allTimeGap_cauchyInMeasure
    {Time : Type*}
    (u : ℕ → Time → Ω → ℝ)
    (hanchor : ∀ n, ∀ᵐ ω ∂μ,
      BddAbove (Set.range fun t => ‖u n t ω‖))
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ →
      ∃ N, ∀ n m, N ≤ n → N ≤ m →
        μ {ω | ∃ t, ε ≤ ‖u n t ω - u m t ω‖} ≤
          ENNReal.ofReal δ) :
    ∃ cutoff : ℕ → ℕ, StrictMono cutoff ∧
      ∀ᵐ ω ∂μ,
        BddAbove (Set.range fun p : ℕ × Time =>
          ‖u (cutoff p.1) p.2 ω‖) := by
  classical
  let q : ℕ → ℝ := fun k => ((1 : ℝ) / 2) ^ (k + 1)
  obtain ⟨cutoff, hcutoff, hfast⟩ :=
    exists_strictMono_ae_fast_steps_of_allTimeGap_cauchyInMeasure u hcauchy
  let bad : ℕ → Set Ω := fun k =>
    {ω | ∃ t, q k ≤ ‖u (cutoff (k + 1)) t ω - u (cutoff k) t ω‖}
  have hae_bad : ∀ᵐ ω ∂μ, ∀ᶠ k in atTop, ω ∉ bad k := by
    filter_upwards [hfast] with ω hω
    filter_upwards [hω] with k hk
    rintro ⟨t, ht⟩
    exact (not_le_of_gt (hk t)) ht
  have hqsum : Summable q := by
    simpa [q, pow_succ, mul_comm] using
      (summable_geometric_two.mul_left ((1 : ℝ) / 2))
  have hanchor_ae : ∀ᵐ ω ∂μ, ∀ n,
      BddAbove (Set.range fun t => ‖u n t ω‖) := by
    rw [ae_all_iff]
    intro n
    exact hanchor n
  refine ⟨cutoff, hcutoff, ?_⟩
  filter_upwards [hae_bad, hanchor_ae] with ω hωbad hωanchor
  obtain ⟨K, hK⟩ := eventually_atTop.1 hωbad
  choose anchor hanchor using hωanchor
  let c : ℕ → ℝ := fun k => max (anchor (cutoff k)) 0
  let S : ℝ := ∑' k, q k
  let C : ℝ := ∑ k ∈ Finset.range K, c k
  have hc_nonneg : ∀ k, 0 ≤ c k := by
    intro k
    exact le_max_right _ _
  have hc_le_sum : ∀ {k}, k < K → c k ≤ C := by
    intro k hk
    simpa [C] using
      (Finset.single_le_sum (s := Finset.range K)
        (f := c) (a := k) (fun i _ => hc_nonneg i)
        (Finset.mem_range.2 hk))
  have hstep : ∀ {k}, K ≤ k → ∀ t,
      dist (u (cutoff k) t ω) (u (cutoff (k + 1)) t ω) ≤ q k := by
    intro k hk t
    have hnot : ω ∉ bad k := hK _ hk
    have hprefix :
        ‖u (cutoff (k + 1)) t ω - u (cutoff k) t ω‖ < q k := by
      exact lt_of_not_ge (by
        intro hge
        exact hnot ⟨t, hge⟩)
    simpa [dist_eq_norm, norm_sub_rev] using hprefix.le
  refine ⟨max C (c K + S), ?_⟩
  rintro _ ⟨⟨k, t⟩, rfl⟩
  by_cases hk : k < K
  · apply le_max_of_le_left
    exact (hanchor (cutoff k) ⟨t, rfl⟩).trans
      ((le_max_left _ _).trans (hc_le_sum hk))
  · have hKk : K ≤ k := Nat.le_of_not_gt hk
    have hdist : dist (u (cutoff K) t ω) (u (cutoff k) t ω) ≤
        ∑ i ∈ Finset.Ico K k, q i := by
      apply dist_le_Ico_sum_of_dist_le hKk
      intro i hiK hik
      exact hstep hiK t
    have hsum : (∑ i ∈ Finset.Ico K k, q i) ≤ S := by
      dsimp [S]
      exact hqsum.sum_le_tsum _ (fun i _ => by positivity)
    apply le_max_of_le_right
    calc
      ‖u (cutoff k) t ω‖ ≤ ‖u (cutoff K) t ω‖ +
          dist (u (cutoff K) t ω) (u (cutoff k) t ω) := by
        exact norm_le_norm_add_norm_sub _ _
      _ ≤ c K + ∑ i ∈ Finset.Ico K k, q i := by
        gcongr
        exact (hanchor (cutoff K) ⟨t, rfl⟩).trans
          (le_max_left _ _)
      _ ≤ c K + S := by
        simpa [add_comm, add_left_comm, add_assoc] using
          (add_le_add_left hsum (c K))

end MaximalDifference
end FTAPTheorem42
