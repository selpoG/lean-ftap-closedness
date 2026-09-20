/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Trading.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Fixed-tail convex combinations in a normed vector space

The stochastic Banach--Saks input is not part of the local mathlib API.  This
file nevertheless records the finite-dimensional algebra and the variational
objects needed for a direct Hilbert-space proof: fixed-tail weights act on
vectors, their squared norms have a tail infimum, and concrete
near-minimizers can be chosen.  The same definitions instantiate directly at
`Lp ℝ (2 : ℝ≥0∞) μ`.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace TailConvexWeights

/-!
## Vector-valued applications
-/

/-- Apply fixed-tail convex weights to a sequence in a real normed vector space. -/
def applyVector {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (w : TailConvexWeights n) (x : ℕ → E) : E :=
  ∑ i ∈ w.support, w.weight i • x i

omit [MeasurableSpace Ω] in
@[simp]
theorem applyVector_singleton {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (n : ℕ) (x : ℕ → E) :
    (singleton n).applyVector x = x n := by
  simp [applyVector, singleton]

omit [MeasurableSpace Ω] in
@[simp]
theorem applyVector_mono {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {n m : ℕ} (hnm : n ≤ m) (w : TailConvexWeights m) (x : ℕ → E) :
    (w.mono hnm).applyVector x = w.applyVector x := by
  rfl

private theorem applyVector_eq_sum_coeff_superset
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {n : ℕ} (w : TailConvexWeights n) {s : Finset ℕ}
    (hsub : w.support ⊆ s) (x : ℕ → E) :
    (∑ i ∈ s, w.coeff i • x i) = w.applyVector x := by
  have hsum :
      ∑ i ∈ w.support, w.coeff i • x i =
        ∑ i ∈ s, w.coeff i • x i := by
    refine Finset.sum_subset hsub ?_
    intro i _his hiw
    simp [coeff_of_not_mem w hiw]
  calc
    (∑ i ∈ s, w.coeff i • x i) =
        ∑ i ∈ w.support, w.coeff i • x i := hsum.symm
    _ = ∑ i ∈ w.support, w.weight i • x i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [coeff_of_mem w hi]
    _ = w.applyVector x := rfl

omit [MeasurableSpace Ω] in
theorem applyVector_eq_sum_coeff_superset'
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {n : ℕ} (w : TailConvexWeights n) {s : Finset ℕ}
    (hsub : w.support ⊆ s) (x : ℕ → E) :
    (∑ i ∈ s, w.coeff i • x i) = w.applyVector x :=
  applyVector_eq_sum_coeff_superset w hsub x

/-- Canonical `Lp` representatives commute almost everywhere with one fixed
finite-tail convex combination. -/
theorem applyVector_coeFn_ae
    {μ : Measure Ω} {n : ℕ} (w : TailConvexWeights n)
    (x : ℕ → Lp ℝ (2 : ℝ≥0∞) μ) (f : ℕ → Ω → ℝ)
    (hx : ∀ i, ((x i : Ω → ℝ) =ᵐ[μ] f i)) :
    ((w.applyVector x : Lp ℝ (2 : ℝ≥0∞) μ) : Ω → ℝ) =ᵐ[μ]
      w.apply f := by
  classical
  have hsum :
      (((∑ i ∈ w.support, w.weight i • x i :
          Lp ℝ (2 : ℝ≥0∞) μ) : Ω → ℝ)) =ᵐ[μ]
        (fun ω => ∑ i ∈ w.support, w.weight i * f i ω) := by
    induction w.support using Finset.induction_on with
    | empty =>
        filter_upwards [Lp.coeFn_zero (E := ℝ)
          (p := (2 : ℝ≥0∞)) μ] with ω hω
        simpa only [Finset.sum_empty, Pi.zero_apply] using hω
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi]
        filter_upwards [Lp.coeFn_add
            (w.weight i • x i) (∑ j ∈ s, w.weight j • x j),
          Lp.coeFn_smul (w.weight i) (x i), ih, hx i]
            with ω hadd hsmul htail hterm
        calc
          (((w.weight i • x i) + ∑ j ∈ s, w.weight j • x j :
              Lp ℝ (2 : ℝ≥0∞) μ) : Ω → ℝ) ω =
              ((w.weight i • x i : Lp ℝ (2 : ℝ≥0∞) μ) :
                Ω → ℝ) ω +
                ((∑ j ∈ s, w.weight j • x j :
                  Lp ℝ (2 : ℝ≥0∞) μ) : Ω → ℝ) ω := hadd
          _ = (w.weight i • ((x i : Lp ℝ (2 : ℝ≥0∞) μ) :
                Ω → ℝ)) ω +
                ∑ j ∈ s, w.weight j * f j ω := by
              rw [hsmul, htail]
          _ = w.weight i * f i ω +
                ∑ j ∈ s, w.weight j * f j ω := by
              simp only [Pi.smul_apply, smul_eq_mul]
              rw [hterm]
          _ = ∑ j ∈ insert i s, w.weight j * f j ω := by
              rw [Finset.sum_insert hi]
  exact hsum

omit [MeasurableSpace Ω] in
@[simp]
theorem applyVector_average
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (w v : TailConvexWeights n) (x : ℕ → E) :
    (w.average v).applyVector x =
      (1 / 2 : ℝ) • (w.applyVector x + v.applyVector x) := by
  have hwsub : w.support ⊆ w.support ∪ v.support := by
    intro i hi
    exact Finset.mem_union.mpr (Or.inl hi)
  have hvsub : v.support ⊆ w.support ∪ v.support := by
    intro i hi
    exact Finset.mem_union.mpr (Or.inr hi)
  simp only [average, applyVector]
  calc
    (∑ i ∈ w.support ∪ v.support,
        ((w.coeff i + v.coeff i) / 2) • x i) =
        ∑ i ∈ w.support ∪ v.support,
          (1 / 2 : ℝ) • (w.coeff i • x i + v.coeff i • x i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      simp [div_eq_inv_mul, mul_smul, add_smul]
    _ = (1 / 2 : ℝ) •
        (∑ i ∈ w.support ∪ v.support,
          (w.coeff i • x i + v.coeff i • x i)) := by
      rw [Finset.smul_sum]
    _ = (1 / 2 : ℝ) •
        ((∑ i ∈ w.support ∪ v.support, w.coeff i • x i) +
          ∑ i ∈ w.support ∪ v.support, v.coeff i • x i) := by
      rw [Finset.sum_add_distrib]
    _ = (1 / 2 : ℝ) • (w.applyVector x + v.applyVector x) := by
      rw [applyVector_eq_sum_coeff_superset' w hwsub x,
        applyVector_eq_sum_coeff_superset' v hvsub x]

/-!
## Tail squared-norm infima
-/

/-- The infimum of squared norms of all convex combinations in the `n`-tail. -/
noncomputable def tailNormSqInf
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : ℕ → E) (n : ℕ) : ℝ :=
  sInf (Set.range fun w : TailConvexWeights n => ‖w.applyVector x‖ ^ 2)

theorem tailNormSqInf_range_nonempty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : ℕ → E) (n : ℕ) :
    (Set.range fun w : TailConvexWeights n => ‖w.applyVector x‖ ^ 2).Nonempty := by
  exact ⟨‖(singleton n).applyVector x‖ ^ 2,
    ⟨singleton n, rfl⟩⟩

theorem tailNormSqInf_range_bddBelow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : ℕ → E) (n : ℕ) :
    BddBelow (Set.range fun w : TailConvexWeights n => ‖w.applyVector x‖ ^ 2) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨w, rfl⟩
  exact sq_nonneg _

theorem tailNormSqInf_le_singleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : ℕ → E) (n : ℕ) :
    tailNormSqInf x n ≤ ‖x n‖ ^ 2 := by
  unfold tailNormSqInf
  refine csInf_le (tailNormSqInf_range_bddBelow x n) ?_
  refine ⟨singleton n, ?_⟩
  simp

theorem tailNormSqInf_mono
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : ℕ → E} {n m : ℕ} (hnm : n ≤ m) :
    tailNormSqInf x n ≤ tailNormSqInf x m := by
  unfold tailNormSqInf
  apply csInf_le_csInf (tailNormSqInf_range_bddBelow x n)
    (tailNormSqInf_range_nonempty x m)
  rintro _ ⟨w, rfl⟩
  refine ⟨w.mono hnm, ?_⟩
  change ‖(w.mono hnm).applyVector x‖ ^ 2 = ‖w.applyVector x‖ ^ 2
  rw [applyVector_mono]

/-!
## Concrete near-minimizers
-/

theorem exists_near_tailNormSqInf
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : ℕ → E} {n : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ∃ w : TailConvexWeights n,
      ‖w.applyVector x‖ ^ 2 < tailNormSqInf x n + ε := by
  have hlt : tailNormSqInf x n < tailNormSqInf x n + ε :=
    lt_add_of_pos_right _ hε
  rcases exists_lt_of_csInf_lt (tailNormSqInf_range_nonempty x n) hlt with
    ⟨a, ⟨w, rfl⟩, hwa⟩
  exact ⟨w, hwa⟩

/-- The canonical positive error budget used to choose one near-minimizer per tail. -/
noncomputable def tailNormSqError (n : ℕ) : ℝ := 1 / (n + 1)

theorem tailNormSqError_pos (n : ℕ) : 0 < tailNormSqError n := by
  unfold tailNormSqError
  positivity

/-- A chosen near-minimizer for every tail, with error `1 / (n + 1)`. -/
noncomputable def tailNormSqNearMinimizers
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : ℕ → E) : ∀ n, TailConvexWeights n :=
  fun n => Classical.choose (exists_near_tailNormSqInf
    (x := x) (n := n) (tailNormSqError_pos n))

theorem tailNormSqNearMinimizers_spec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : ℕ → E) (n : ℕ) :
    ‖(tailNormSqNearMinimizers x n).applyVector x‖ ^ 2 <
      tailNormSqInf x n + tailNormSqError n := by
  exact Classical.choose_spec (exists_near_tailNormSqInf
    (x := x) (n := n) (tailNormSqError_pos n))

/-!
## The parallelogram estimate
-/

/--
The midpoint estimate behind the Hilbert-space Banach--Saks construction.  A
near-minimizer in the `n`-tail controls the squared distance between two
near-minimizers from tails `n` and `m`.
-/
theorem near_tailNormSqDist_lt_of_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x : ℕ → E} {η : ℕ → ℝ} (w : ∀ n, TailConvexWeights n)
    (hw_near : ∀ n,
      ‖(w n).applyVector x‖ ^ 2 < tailNormSqInf x n + η n)
    {n m : ℕ} (hnm : n ≤ m) :
    ‖(w n).applyVector x - (w m).applyVector x‖ ^ 2 <
      2 * ((tailNormSqInf x m - tailNormSqInf x n) + η n + η m) := by
  let wm : TailConvexWeights n := (w m).mono hnm
  have hmid_le :
      tailNormSqInf x n ≤
        ‖((w n).average wm).applyVector x‖ ^ 2 := by
    unfold tailNormSqInf
    exact csInf_le (tailNormSqInf_range_bddBelow x n)
      ⟨(w n).average wm, rfl⟩
  have hmid_fun :
      ((w n).average wm).applyVector x =
        (1 / 2 : ℝ) • ((w n).applyVector x + (w m).applyVector x) := by
    rw [applyVector_average]
    dsimp [wm]
    rw [applyVector_mono]
  rw [hmid_fun] at hmid_le
  have hpar := parallelogram_law_with_norm ℝ
    ((w n).applyVector x) ((w m).applyVector x)
  have hmid_sq :
      ‖(1 / 2 : ℝ) • ((w n).applyVector x + (w m).applyVector x)‖ ^ 2 =
        (1 / 4 : ℝ) * ‖(w n).applyVector x + (w m).applyVector x‖ ^ 2 := by
    rw [norm_smul]
    simp only [Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    ring
  have hn_near := hw_near n
  have hm_near := hw_near m
  nlinarith

/-!
## Cauchy convergence of the variationally selected averages
-/

/-- A bounded sequence gives a uniform upper bound for all tail infima. -/
theorem tailNormSqInf_bddAbove
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : ℕ → E} {C : ℝ}
    (hbound : ∀ n, ‖x n‖ ≤ C) (hC : 0 ≤ C) :
    BddAbove (Set.range (tailNormSqInf x)) := by
  refine ⟨C ^ 2, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact (tailNormSqInf_le_singleton x n).trans
    ((sq_le_sq₀ (norm_nonneg _) hC).2 (hbound n))

/--
Any near-minimizing fixed-tail weight sequence for a bounded Hilbert sequence
is Cauchy.  This is the direct Banach--Saks variational estimate; no Cauchy
assumption on the original sequence is used.
-/
theorem tailNormSqWeights_cauchySeq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x : ℕ → E} {C : ℝ} (hbound : ∀ n, ‖x n‖ ≤ C) (hC : 0 ≤ C)
    {η : ℕ → ℝ} (hη_nonneg : ∀ n, 0 ≤ η n)
    (hη_tendsto : Tendsto η atTop (𝓝 0))
    (w : ∀ n, TailConvexWeights n)
    (hw_near : ∀ n,
      ‖(w n).applyVector x‖ ^ 2 < tailNormSqInf x n + η n) :
    CauchySeq (fun n => (w n).applyVector x) := by
  let S : ℕ → ℝ := fun n => tailNormSqInf x n
  have hS_mono : Monotone S := by
    intro n m hnm
    exact tailNormSqInf_mono hnm
  have hS_bdd : BddAbove (Set.range S) := by
    simpa [S] using (tailNormSqInf_bddAbove hbound hC)
  have hS_tendsto : Tendsto S atTop (𝓝 (⨆ n, S n)) :=
    tendsto_atTop_ciSup hS_mono hS_bdd
  have hS_cauchy : CauchySeq S := hS_tendsto.cauchySeq
  rw [Metric.cauchySeq_iff] at hS_cauchy
  rw [Metric.cauchySeq_iff]
  rw [Metric.tendsto_atTop] at hη_tendsto
  intro r hr
  have heps : 0 < r ^ 2 / 8 := by positivity
  rcases hS_cauchy (r ^ 2 / 8) heps with ⟨NS, hNS⟩
  rcases hη_tendsto (r ^ 2 / 8) heps with ⟨Nη, hNη⟩
  refine ⟨max NS Nη, ?_⟩
  have hordered : ∀ n m, max NS Nη ≤ n → max NS Nη ≤ m → n ≤ m →
      ‖(w n).applyVector x - (w m).applyVector x‖ ^ 2 < r ^ 2 := by
    intro n m hn hm hnm
    have hnS : NS ≤ n := le_trans (le_max_left _ _) hn
    have hmS : NS ≤ m := le_trans (le_max_left _ _) hm
    have hnη : Nη ≤ n := le_trans (le_max_right _ _) hn
    have hmη : Nη ≤ m := le_trans (le_max_right _ _) hm
    have hSdist := hNS n hnS m hmS
    have hηn_dist := hNη n hnη
    have hηm_dist := hNη m hmη
    have hSdiff_lt : S m - S n < r ^ 2 / 8 := by
      have hSn_le : S n ≤ S m := hS_mono hnm
      have habs : |S n - S m| < r ^ 2 / 8 := by
        simpa [Real.dist_eq] using hSdist
      have habs' : |S m - S n| < r ^ 2 / 8 := by
        simpa [abs_sub_comm] using habs
      rwa [abs_of_nonneg (sub_nonneg.mpr hSn_le)] at habs'
    have hηn_lt : η n < r ^ 2 / 8 := by
      have habs : |η n| < r ^ 2 / 8 := by
        simpa [Real.dist_eq] using hηn_dist
      exact (abs_of_nonneg (hη_nonneg n)) ▸ habs
    have hηm_lt : η m < r ^ 2 / 8 := by
      have habs : |η m| < r ^ 2 / 8 := by
        simpa [Real.dist_eq] using hηm_dist
      exact (abs_of_nonneg (hη_nonneg m)) ▸ habs
    have hD := near_tailNormSqDist_lt_of_le
      (x := x) (η := η) w hw_near hnm
    dsimp [S] at hSdiff_lt
    nlinarith
  intro n hn m hm
  by_cases hnm : n ≤ m
  · have hsq := hordered n m hn hm hnm
    have hnorm :
        ‖(w n).applyVector x - (w m).applyVector x‖ < r :=
      (sq_lt_sq₀ (norm_nonneg _) (le_of_lt hr)).mp hsq
    rw [dist_eq_norm]
    exact hnorm
  · have hmn : m ≤ n := le_of_not_ge hnm
    have hswap := hordered m n hm hn hmn
    have hnorm :
        ‖(w m).applyVector x - (w n).applyVector x‖ < r :=
      (sq_lt_sq₀ (norm_nonneg _) (le_of_lt hr)).mp hswap
    rw [dist_eq_norm, norm_sub_rev]
    exact hnorm

theorem tailNormSqError_tendsto_zero :
    Tendsto tailNormSqError atTop (𝓝 0) := by
  have herr : tailNormSqError = fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) := by
    funext n
    simp [tailNormSqError]
  rw [herr]
  simpa only [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- The canonical `1 / (n + 1)` near-minimizers form a Cauchy sequence. -/
theorem tailNormSqNearMinimizers_cauchySeq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x : ℕ → E} {C : ℝ}
    (hbound : ∀ n, ‖x n‖ ≤ C) (hC : 0 ≤ C) :
    CauchySeq (fun n => (tailNormSqNearMinimizers x n).applyVector x) := by
  apply tailNormSqWeights_cauchySeq hbound hC
    (fun n => (tailNormSqError_pos n).le)
    tailNormSqError_tendsto_zero (tailNormSqNearMinimizers x)
  intro n
  exact tailNormSqNearMinimizers_spec x n

/-- In a complete Hilbert space, the canonical convexified sequence converges. -/
theorem exists_tendsto_tailNormSqNearMinimizers
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {x : ℕ → E} {C : ℝ}
    (hbound : ∀ n, ‖x n‖ ≤ C) (hC : 0 ≤ C) :
    ∃ y : E,
      Tendsto (fun n => (tailNormSqNearMinimizers x n).applyVector x)
        atTop (𝓝 y) :=
  cauchySeq_tendsto_of_complete (tailNormSqNearMinimizers_cauchySeq hbound hC)

end TailConvexWeights
end FTAPTheorem42
