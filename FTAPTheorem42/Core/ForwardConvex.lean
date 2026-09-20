import FTAPTheorem42.Core.Basic

/-!
# Forward-convex terminal-gain interfaces

This file contains the terminal-gain Fatou interfaces and finite forward-convex
weight APIs used by the compactness bridges.
-/

open Filter MeasureTheory
open scoped BigOperators

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/--
The stochastic core of the Fatou-closedness argument: if claims dominated by
terminal gains converge a.e. under a common lower bound, the limit is again
dominated by a terminal gain.
-/
def TerminalGainFatouStable (μ : Measure Ω) (K0 : Set (Ω → ℝ)) : Prop :=
  ∀ ⦃f : ℕ → Ω → ℝ⦄ ⦃g : Ω → ℝ⦄ ⦃G : ℕ → Ω → ℝ⦄,
    (∀ n, G n ∈ K0) →
    (∀ n, AEDominatedBy μ (f n) (G n)) →
    (∀ n, AELowerBoundedBy μ (-1) (f n)) →
    TendstoAE μ f g →
    ∃ G_lim ∈ K0, AEDominatedBy μ g G_lim

/--
Forward convex weights.  For each output index `n`, only terminal gains from
the tail `{i | n ≤ i}` may appear, with nonnegative weights summing to one.
-/
structure ForwardConvexWeights where
  support : ℕ → Finset ℕ
  weight : ℕ → ℕ → ℝ
  tail : ∀ n i, i ∈ support n → n ≤ i
  nonneg : ∀ n i, i ∈ support n → 0 ≤ weight n i
  sum_eq_one : ∀ n, ∑ i ∈ support n, weight n i = 1

namespace ForwardConvexWeights

/-- Apply forward convex weights to a sequence of claims. -/
def apply (W : ForwardConvexWeights) (G : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun n ω => ∑ i ∈ W.support n, W.weight n i * G i ω

omit [MeasurableSpace Ω] in
theorem apply_add_const
    (W : ForwardConvexWeights) (G : ℕ → Ω → ℝ) (c : ℝ) :
    W.apply (fun n ω => G n ω + c) =
      fun n ω => W.apply G n ω + c := by
  ext n ω
  simp only [apply]
  calc
    (∑ i ∈ W.support n, W.weight n i * (G i ω + c)) =
        ∑ i ∈ W.support n,
          (W.weight n i * G i ω + W.weight n i * c) := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
    _ = (∑ i ∈ W.support n, W.weight n i * G i ω) +
          ∑ i ∈ W.support n, W.weight n i * c := by
            rw [Finset.sum_add_distrib]
    _ = (∑ i ∈ W.support n, W.weight n i * G i ω) + c := by
          rw [← Finset.sum_mul, W.sum_eq_one n, one_mul]

omit [MeasurableSpace Ω] in
@[simp]
theorem apply_constSequence (W : ForwardConvexWeights) (u : Ω → ℝ) :
    W.apply (fun _ : ℕ => u) = fun _ : ℕ => u := by
  ext n ω
  simp [apply, ← Finset.sum_mul, W.sum_eq_one n]

omit [MeasurableSpace Ω] in
theorem apply_add
    (W : ForwardConvexWeights) (f g : ℕ → Ω → ℝ) :
    W.apply (fun n ω => f n ω + g n ω) =
      fun n ω => W.apply f n ω + W.apply g n ω := by
  ext n ω
  simp [apply, mul_add, Finset.sum_add_distrib]

omit [MeasurableSpace Ω] in
theorem apply_neg
    (W : ForwardConvexWeights) (f : ℕ → Ω → ℝ) :
    W.apply (fun n ω => -f n ω) = fun n ω => -W.apply f n ω := by
  ext n ω
  simp [apply, ← Finset.sum_neg_distrib]

omit [MeasurableSpace Ω] in
theorem apply_sub
    (W : ForwardConvexWeights) (f g : ℕ → Ω → ℝ) :
    W.apply (fun n ω => f n ω - g n ω) =
      fun n ω => W.apply f n ω - W.apply g n ω := by
  ext n ω
  simp [sub_eq_add_neg, apply_add, apply_neg]

omit [MeasurableSpace Ω] in
theorem apply_sub_constFunction
    (W : ForwardConvexWeights) (H : ℕ → Ω → ℝ) (u : Ω → ℝ) :
    W.apply (fun i ω => H i ω - u ω) =
      fun n ω => W.apply H n ω - u ω := by
  calc
    W.apply (fun i ω => H i ω - u ω) =
        fun n ω => W.apply H n ω - W.apply (fun _ : ℕ => u) n ω :=
      W.apply_sub H (fun _ : ℕ => u)
    _ = fun n ω => W.apply H n ω - u ω := by
      rw [W.apply_constSequence u]

/--
Forward convex combinations of a convergent real sequence converge to the same
limit.  The tail condition ensures that, for large `n`, every index used by the
`n`-th convex combination is already in the convergence tail.
-/
theorem tendsto_apply_real
    (W : ForwardConvexWeights) {u : ℕ → ℝ} {a : ℝ}
    (hu : Tendsto u atTop (nhds a)) :
    Tendsto (fun n => ∑ i ∈ W.support n, W.weight n i * u i) atTop
      (nhds a) := by
  rw [Metric.tendsto_atTop] at hu ⊢
  intro ε hε
  rcases hu (ε / 2) (half_pos hε) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hclose : ∀ i ∈ W.support n, |u i - a| ≤ ε / 2 := by
    intro i hi
    have hNi : N ≤ i := le_trans hn (W.tail n i hi)
    have hdist := hN i hNi
    exact le_of_lt (by simpa [Real.dist_eq] using hdist)
  have hsum_const :
      (∑ i ∈ W.support n, W.weight n i * a) = a := by
    rw [← Finset.sum_mul, W.sum_eq_one n, one_mul]
  have hsub_eq :
      (∑ i ∈ W.support n, W.weight n i * u i) - a =
        ∑ i ∈ W.support n, W.weight n i * (u i - a) := by
    calc
      (∑ i ∈ W.support n, W.weight n i * u i) - a
          = (∑ i ∈ W.support n, W.weight n i * u i) -
              ∑ i ∈ W.support n, W.weight n i * a := by rw [hsum_const]
      _ = ∑ i ∈ W.support n,
            (W.weight n i * u i - W.weight n i * a) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ i ∈ W.support n, W.weight n i * (u i - a) := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
  have hnorm_le :
      ‖(∑ i ∈ W.support n, W.weight n i * u i) - a‖ ≤ ε / 2 := by
    calc
      ‖(∑ i ∈ W.support n, W.weight n i * u i) - a‖
          = ‖∑ i ∈ W.support n, W.weight n i * (u i - a)‖ := by
            rw [hsub_eq]
      _ ≤ ∑ i ∈ W.support n, ‖W.weight n i * (u i - a)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ W.support n, W.weight n i * (ε / 2) := by
            apply Finset.sum_le_sum
            intro i hi
            rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (W.nonneg n i hi),
              Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_left (hclose i hi) (W.nonneg n i hi)
      _ = ε / 2 := by
            rw [← Finset.sum_mul, W.sum_eq_one n, one_mul]
  have hdist_le :
      dist (∑ i ∈ W.support n, W.weight n i * u i) a ≤ ε / 2 := by
    simpa [Real.dist_eq, Real.norm_eq_abs] using hnorm_le
  linarith

/--
The weights preserve a.e. convergence of arbitrary real-valued claim sequences.
This is the analytic part of the forward-convex-combination argument.
-/
def PreservesTendstoAE (W : ForwardConvexWeights) (μ : Measure Ω) : Prop :=
  ∀ ⦃f : ℕ → Ω → ℝ⦄ ⦃g : Ω → ℝ⦄,
    TendstoAE μ f g → TendstoAE μ (W.apply f) g

theorem preservesTendstoAE (W : ForwardConvexWeights) (μ : Measure Ω) :
    W.PreservesTendstoAE μ := by
  intro f g hlim
  filter_upwards [hlim] with ω hω
  exact W.tendsto_apply_real hω

omit [MeasurableSpace Ω] in
theorem apply_mem_of_claimCone
    (W : ForwardConvexWeights) {K0 : Set (Ω → ℝ)}
    (hK : ClaimCone K0) {G : ℕ → Ω → ℝ}
    (hG : ∀ n, G n ∈ K0) (n : ℕ) :
    W.apply G n ∈ K0 := by
  change (fun ω => ∑ i ∈ W.support n, W.weight n i * G i ω) ∈ K0
  exact hK.finset_nonneg_sum_mem (W.support n) (W.weight n) G
    (W.nonneg n) (fun i _hi => hG i)

omit [MeasurableSpace Ω] in
theorem apply_mem_of_convexInvariant
    (W : ForwardConvexWeights) {K0 : Set (Ω → ℝ)}
    (hK : ConvexInvariant K0) {G : ℕ → Ω → ℝ}
    (hG : ∀ n, G n ∈ K0) (n : ℕ) :
    W.apply G n ∈ K0 := by
  change (fun ω => ∑ i ∈ W.support n, W.weight n i * G i ω) ∈ K0
  exact hK.finset_nonneg_sum_mem (W.support n) (W.weight n) G
    (W.nonneg n) (W.sum_eq_one n) (fun i _hi => hG i)

theorem apply_dominated
    (W : ForwardConvexWeights) {μ : Measure Ω}
    {f G : ℕ → Ω → ℝ}
    (hdom : ∀ n, AEDominatedBy μ (f n) (G n)) (n : ℕ) :
    AEDominatedBy μ (W.apply f n) (W.apply G n) := by
  have hdom_all : ∀ᵐ ω ∂μ, ∀ i, f i ω ≤ G i ω := by
    exact ae_all_iff.mpr hdom
  filter_upwards [hdom_all] with ω hω
  dsimp [apply]
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left (hω i) (W.nonneg n i hi)

theorem apply_aeLowerBounded_of_antitone
    (W : ForwardConvexWeights) {μ : Measure Ω}
    {f : ℕ → Ω → ℝ} {δ : ℕ → ℝ}
    (hδ : Antitone δ)
    (hlower : ∀ n, AELowerBoundedBy μ (-(δ n)) (f n)) (n : ℕ) :
    AELowerBoundedBy μ (-(δ n)) (W.apply f n) := by
  have hlower_all : ∀ᵐ ω ∂μ, ∀ i, -(δ i) ≤ f i ω := by
    exact ae_all_iff.mpr hlower
  filter_upwards [hlower_all] with ω hω
  have hsum_const :
      (∑ i ∈ W.support n, W.weight n i * (-(δ n))) = -(δ n) := by
    rw [← Finset.sum_mul, W.sum_eq_one n, one_mul]
  calc
    -(δ n)
        = ∑ i ∈ W.support n, W.weight n i * (-(δ n)) := hsum_const.symm
    _ ≤ ∑ i ∈ W.support n, W.weight n i * f i ω := by
        apply Finset.sum_le_sum
        intro i hi
        have htail : n ≤ i := W.tail n i hi
        have hδi : δ i ≤ δ n := hδ htail
        have hlower_i : -(δ n) ≤ f i ω := by
          exact le_trans (neg_le_neg hδi) (hω i)
        exact mul_le_mul_of_nonneg_left hlower_i (W.nonneg n i hi)
    _ = W.apply f n ω := by
        simp [apply]

theorem apply_aeUpperBounded_one
    (W : ForwardConvexWeights) {μ : Measure Ω}
    {f : ℕ → Ω → ℝ}
    (hupper : ∀ n, ∀ᵐ ω ∂μ, f n ω ≤ 1) (n : ℕ) :
    ∀ᵐ ω ∂μ, W.apply f n ω ≤ 1 := by
  have hupper_all : ∀ᵐ ω ∂μ, ∀ i, f i ω ≤ 1 := by
    exact ae_all_iff.mpr hupper
  filter_upwards [hupper_all] with ω hω
  have hsum_const :
      (∑ i ∈ W.support n, W.weight n i * (1 : ℝ)) = 1 := by
    rw [← Finset.sum_mul, W.sum_eq_one n, one_mul]
  calc
    W.apply f n ω
        = ∑ i ∈ W.support n, W.weight n i * f i ω := by
        simp [apply]
    _ ≤ ∑ i ∈ W.support n, W.weight n i * (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hω i) (W.nonneg n i hi)
    _ = 1 := hsum_const

theorem apply_aestronglyMeasurable
    (W : ForwardConvexWeights) {μ : Measure Ω}
    {f : ℕ → Ω → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (n : ℕ) :
    AEStronglyMeasurable (W.apply f n) μ := by
  change AEStronglyMeasurable
    (fun ω => ∑ i ∈ W.support n, W.weight n i * f i ω) μ
  exact (W.support n).aestronglyMeasurable_fun_sum
    (fun i _hi => (hf i).const_mul (W.weight n i))

theorem apply_stronglyMeasurable
    (W : ForwardConvexWeights)
    {f : ℕ → Ω → ℝ}
    (hf : ∀ n, StronglyMeasurable (f n)) (n : ℕ) :
    StronglyMeasurable (W.apply f n) := by
  change StronglyMeasurable
    (fun ω => ∑ i ∈ W.support n, W.weight n i * f i ω)
  exact (W.support n).stronglyMeasurable_fun_sum
    (fun i _hi => (hf i).const_mul (W.weight n i))

theorem apply_ae_nonneg
    (W : ForwardConvexWeights) {μ : Measure Ω}
    {f : ℕ → Ω → ℝ}
    (hf : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ f n ω) (n : ℕ) :
    ∀ᵐ ω ∂μ, 0 ≤ W.apply f n ω := by
  have hf_all : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ f i ω := by
    exact ae_all_iff.mpr hf
  filter_upwards [hf_all] with ω hω
  change 0 ≤ ∑ i ∈ W.support n, W.weight n i * f i ω
  exact Finset.sum_nonneg fun i hi =>
    mul_nonneg (W.nonneg n i hi) (hω i)

end ForwardConvexWeights

/-- Finite convex weights supported in one fixed tail `{i | n ≤ i}`. -/
structure TailConvexWeights (n : ℕ) where
  support : Finset ℕ
  weight : ℕ → ℝ
  tail : ∀ i, i ∈ support → n ≤ i
  nonneg : ∀ i, i ∈ support → 0 ≤ weight i
  sum_eq_one : ∑ i ∈ support, weight i = 1

namespace ForwardConvexWeights

/-- Regard one row of forward-convex weights as fixed weights on that tail. -/
def tailRow (W : ForwardConvexWeights) (n : ℕ) : TailConvexWeights n where
  support := W.support n
  weight := W.weight n
  tail := W.tail n
  nonneg := W.nonneg n
  sum_eq_one := W.sum_eq_one n

end ForwardConvexWeights

namespace TailConvexWeights

/-- Apply fixed-tail convex weights to a sequence of claims. -/
def apply (w : TailConvexWeights n) (G : ℕ → Ω → ℝ) : Ω → ℝ :=
  fun ω => ∑ i ∈ w.support, w.weight i * G i ω

omit [MeasurableSpace Ω] in
theorem apply_add_const
    (w : TailConvexWeights n) (G : ℕ → Ω → ℝ) (c : ℝ) :
    w.apply (fun n ω => G n ω + c) =
      fun ω => w.apply G ω + c := by
  ext ω
  simp only [apply]
  calc
    (∑ i ∈ w.support, w.weight i * (G i ω + c)) =
        ∑ i ∈ w.support,
          (w.weight i * G i ω + w.weight i * c) := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
    _ = (∑ i ∈ w.support, w.weight i * G i ω) +
          ∑ i ∈ w.support, w.weight i * c := by
            rw [Finset.sum_add_distrib]
    _ = (∑ i ∈ w.support, w.weight i * G i ω) + c := by
          rw [← Finset.sum_mul, w.sum_eq_one, one_mul]

omit [MeasurableSpace Ω] in
theorem apply_sub_constFunction
    (w : TailConvexWeights n) (H : ℕ → Ω → ℝ) (u : Ω → ℝ) :
    w.apply (fun i ω => H i ω - u ω) =
      fun ω => w.apply H ω - u ω := by
  ext ω
  simp only [apply]
  calc
    (∑ i ∈ w.support, w.weight i * (H i ω - u ω)) =
        (∑ i ∈ w.support, w.weight i * H i ω) -
          ∑ i ∈ w.support, w.weight i * u ω := by
      simp [sub_eq_add_neg, mul_add, Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    _ = w.apply H ω - u ω := by
      rw [← Finset.sum_mul, w.sum_eq_one, one_mul]
      rfl

/--
The total coefficient of an index, extended by zero off the finite support.
This keeps later operations on unions of supports honest: values of `weight`
outside `support` are intentionally ignored.
-/
def coeff (w : TailConvexWeights n) (i : ℕ) : ℝ :=
  if i ∈ w.support then w.weight i else 0

omit [MeasurableSpace Ω] in
@[simp]
theorem coeff_of_mem (w : TailConvexWeights n) {i : ℕ} (hi : i ∈ w.support) :
    w.coeff i = w.weight i := by
  simp [coeff, hi]

omit [MeasurableSpace Ω] in
@[simp]
theorem coeff_of_not_mem (w : TailConvexWeights n) {i : ℕ} (hi : i ∉ w.support) :
    w.coeff i = 0 := by
  simp [coeff, hi]

omit [MeasurableSpace Ω] in
theorem coeff_nonneg (w : TailConvexWeights n) (i : ℕ) :
    0 ≤ w.coeff i := by
  by_cases hi : i ∈ w.support
  · simpa [coeff, hi] using w.nonneg i hi
  · simp [coeff, hi]

omit [MeasurableSpace Ω] in
theorem sum_coeff_eq_one (w : TailConvexWeights n) :
    ∑ i ∈ w.support, w.coeff i = 1 := by
  simpa [coeff] using w.sum_eq_one

omit [MeasurableSpace Ω] in
theorem sum_coeff_superset_eq_one
    (w : TailConvexWeights n) {s : Finset ℕ}
    (hsub : w.support ⊆ s) :
    ∑ i ∈ s, w.coeff i = 1 := by
  have hsum :
      ∑ i ∈ w.support, w.coeff i = ∑ i ∈ s, w.coeff i := by
    refine Finset.sum_subset hsub ?_
    intro i _his hiw
    exact coeff_of_not_mem w hiw
  simpa [sum_coeff_eq_one] using hsum.symm

omit [MeasurableSpace Ω] in
theorem apply_eq_sum_coeff_superset
    (w : TailConvexWeights n) {s : Finset ℕ}
    (hsub : w.support ⊆ s) (G : ℕ → Ω → ℝ) :
    (fun ω => ∑ i ∈ s, w.coeff i * G i ω) = w.apply G := by
  ext ω
  have hsum :
      ∑ i ∈ w.support, w.coeff i * G i ω =
        ∑ i ∈ s, w.coeff i * G i ω := by
    refine Finset.sum_subset hsub ?_
    intro i _his hiw
    simp [coeff_of_not_mem w hiw]
  calc
    ∑ i ∈ s, w.coeff i * G i ω
        = ∑ i ∈ w.support, w.coeff i * G i ω := hsum.symm
    _ = ∑ i ∈ w.support, w.weight i * G i ω := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [coeff_of_mem w hi]
    _ = w.apply G ω := rfl

/-- The degenerate convex weight selecting the first element of the tail. -/
def singleton (n : ℕ) : TailConvexWeights n where
  support := {n}
  weight := fun i => if i = n then 1 else 0
  tail := by
    intro i hi
    rw [Finset.mem_singleton] at hi
    exact le_of_eq hi.symm
  nonneg := by
    intro i _hi
    by_cases h : i = n <;> simp [h]
  sum_eq_one := by
    simp

omit [MeasurableSpace Ω] in
@[simp]
theorem singleton_apply (n : ℕ) (G : ℕ → Ω → ℝ) :
    (singleton n).apply G = G n := by
  ext ω
  simp [singleton, apply]

omit [MeasurableSpace Ω] in
/-- A tail supported after `m` is also supported after any earlier `n ≤ m`. -/
def mono {n m : ℕ} (hnm : n ≤ m) (w : TailConvexWeights m) :
    TailConvexWeights n where
  support := w.support
  weight := w.weight
  tail := fun i hi => le_trans hnm (w.tail i hi)
  nonneg := w.nonneg
  sum_eq_one := w.sum_eq_one

omit [MeasurableSpace Ω] in
@[simp]
theorem mono_apply {n m : ℕ} (hnm : n ≤ m)
    (w : TailConvexWeights m) (G : ℕ → Ω → ℝ) :
    (w.mono hnm).apply G = w.apply G := by
  rfl

omit [MeasurableSpace Ω] in
/-- The midpoint of two fixed-tail convex combinations. -/
noncomputable def average (w v : TailConvexWeights n) : TailConvexWeights n where
  support := w.support ∪ v.support
  weight := fun i => (w.coeff i + v.coeff i) / 2
  tail := by
    intro i hi
    rw [Finset.mem_union] at hi
    rcases hi with hi | hi
    · exact w.tail i hi
    · exact v.tail i hi
  nonneg := by
    intro i _hi
    nlinarith [w.coeff_nonneg i, v.coeff_nonneg i]
  sum_eq_one := by
    have hwsub : w.support ⊆ w.support ∪ v.support := by
      intro i hi
      exact Finset.mem_union.mpr (Or.inl hi)
    have hvsub : v.support ⊆ w.support ∪ v.support := by
      intro i hi
      exact Finset.mem_union.mpr (Or.inr hi)
    calc
      ∑ i ∈ w.support ∪ v.support, (w.coeff i + v.coeff i) / 2
          = (∑ i ∈ w.support ∪ v.support, (w.coeff i + v.coeff i)) / 2 := by
          rw [Finset.sum_div]
      _ = ((∑ i ∈ w.support ∪ v.support, w.coeff i) +
              ∑ i ∈ w.support ∪ v.support, v.coeff i) / 2 := by
          rw [Finset.sum_add_distrib]
      _ = (1 + 1) / 2 := by
          rw [w.sum_coeff_superset_eq_one hwsub, v.sum_coeff_superset_eq_one hvsub]
      _ = 1 := by norm_num

omit [MeasurableSpace Ω] in
@[simp]
theorem average_apply (w v : TailConvexWeights n) (G : ℕ → Ω → ℝ) :
    (w.average v).apply G =
      fun ω => (w.apply G ω + v.apply G ω) / 2 := by
  ext ω
  have hwsub : w.support ⊆ w.support ∪ v.support := by
    intro i hi
    exact Finset.mem_union.mpr (Or.inl hi)
  have hvsub : v.support ⊆ w.support ∪ v.support := by
    intro i hi
    exact Finset.mem_union.mpr (Or.inr hi)
  have hwapply := congrFun (w.apply_eq_sum_coeff_superset hwsub G).symm ω
  have hvapply := congrFun (v.apply_eq_sum_coeff_superset hvsub G).symm ω
  simp only [average, apply]
  calc
    ∑ i ∈ w.support ∪ v.support, (w.coeff i + v.coeff i) / 2 * G i ω
        = ∑ i ∈ w.support ∪ v.support,
            (w.coeff i * G i ω + v.coeff i * G i ω) / 2 := by
          apply Finset.sum_congr rfl
          intro i _hi
          ring
    _ = (∑ i ∈ w.support ∪ v.support,
            (w.coeff i * G i ω + v.coeff i * G i ω)) / 2 := by
          rw [Finset.sum_div]
    _ = ((∑ i ∈ w.support ∪ v.support, w.coeff i * G i ω) +
            ∑ i ∈ w.support ∪ v.support, v.coeff i * G i ω) / 2 := by
          rw [Finset.sum_add_distrib]
    _ = (w.apply G ω + v.apply G ω) / 2 := by
          rw [hwapply, hvapply]

theorem apply_stronglyMeasurable
    (w : TailConvexWeights n)
    {f : ℕ → Ω → ℝ}
    (hf : ∀ n, StronglyMeasurable (f n)) :
    StronglyMeasurable (w.apply f) := by
  change StronglyMeasurable
    (fun ω => ∑ i ∈ w.support, w.weight i * f i ω)
  exact w.support.stronglyMeasurable_fun_sum
    (fun i _hi => (hf i).const_mul (w.weight i))

theorem apply_ae_nonneg
    (w : TailConvexWeights n) {μ : Measure Ω}
    {f : ℕ → Ω → ℝ}
    (hf : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ f n ω) :
    ∀ᵐ ω ∂μ, 0 ≤ w.apply f ω := by
  have hf_all : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ f i ω := by
    exact ae_all_iff.mpr hf
  filter_upwards [hf_all] with ω hω
  dsimp [apply]
  exact Finset.sum_nonneg fun i hi =>
    mul_nonneg (w.nonneg i hi) (hω i)

theorem apply_ae_le
    (w : TailConvexWeights n) {μ : Measure Ω}
    {f : ℕ → Ω → ℝ} {M : ℝ}
    (hf : ∀ n, ∀ᵐ ω ∂μ, f n ω ≤ M) :
    ∀ᵐ ω ∂μ, w.apply f ω ≤ M := by
  have hf_all : ∀ᵐ ω ∂μ, ∀ i, f i ω ≤ M := by
    exact ae_all_iff.mpr hf
  filter_upwards [hf_all] with ω hω
  have hsum_const :
      (∑ i ∈ w.support, w.weight i * M) = M := by
    rw [← Finset.sum_mul, w.sum_eq_one, one_mul]
  calc
    w.apply f ω
        = ∑ i ∈ w.support, w.weight i * f i ω := by
        simp [apply]
    _ ≤ ∑ i ∈ w.support, w.weight i * M := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hω i) (w.nonneg i hi)
    _ = M := hsum_const

/-- Bundle one fixed-tail convex choice for each `n` into forward convex weights. -/
def toForward (w : ∀ n, TailConvexWeights n) : ForwardConvexWeights where
  support := fun n => (w n).support
  weight := fun n i => (w n).weight i
  tail := fun n i hi => (w n).tail i hi
  nonneg := fun n i hi => (w n).nonneg i hi
  sum_eq_one := fun n => (w n).sum_eq_one

omit [MeasurableSpace Ω] in
@[simp]
theorem toForward_apply (w : ∀ n, TailConvexWeights n) (G : ℕ → Ω → ℝ) :
    (toForward w).apply G = fun n => (w n).apply G := by
  ext n ω
  rfl

/--
Reindex fixed-tail weights along a strictly increasing subsequence and bundle
them as forward convex weights.  Since `n ≤ φ n`, a tail starting at `φ n` is
also valid for the `n`-th forward convex combination.
-/
def toForwardReindex (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (w : ∀ n, TailConvexWeights n) : ForwardConvexWeights where
  support := fun n => (w (φ n)).support
  weight := fun n i => (w (φ n)).weight i
  tail := by
    intro n i hi
    exact le_trans hφ.le_apply ((w (φ n)).tail i hi)
  nonneg := fun n i hi => (w (φ n)).nonneg i hi
  sum_eq_one := fun n => (w (φ n)).sum_eq_one

omit [MeasurableSpace Ω] in
@[simp]
theorem toForwardReindex_apply
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (w : ∀ n, TailConvexWeights n) (G : ℕ → Ω → ℝ) :
    (toForwardReindex φ hφ w).apply G =
      fun n => (w (φ n)).apply G := by
  ext n ω
  rfl

end TailConvexWeights

end FTAPTheorem42
