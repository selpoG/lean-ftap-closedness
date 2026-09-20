/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Basic.ConditionalExpectationL2
import FTAPTheorem42.Stochastic.Martingale.Basic.MartingaleAbsoluteEnvelope
import FTAPTheorem42.Stochastic.Martingale.Regularization.ConditionalExpectationFiltrationLimit
import FTAPTheorem42.Stochastic.Stopping.StoppingTimeForetelling
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Conditional-expectation envelopes at stopping times

Finite families of bounded stopping times can be sorted pathwise.  Their
order statistics are again stopping times, and conditional expectations at
the sorted times form a finite discrete martingale.  Doob's `L²` inequality
therefore controls a countable family of stopping-time conditional
expectations without requiring the stopping times to have countable range or
choosing a càdlàg version of the conditional-expectation martingale.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal MeasureTheory NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace StoppingTimeCondExpEnvelope

/-- The first `n + 1` stopping times, sorted pathwise. -/
noncomputable def sortedPrefixTime
    (σ : ℕ → Ω → ℝ≥0) (n : ℕ) (i : Fin (n + 1)) : Ω → ℝ≥0 :=
  fun ω ↦
    let f : Fin (n + 1) → ℝ≥0 := fun j ↦ σ j ω
    f (Tuple.sort f i)

omit [MeasurableSpace Ω] in
/-- The pathwise order statistics are chronological. -/
theorem sortedPrefixTime_mono
    (σ : ℕ → Ω → ℝ≥0) (n : ℕ) (ω : Ω) :
    Monotone fun i ↦ sortedPrefixTime σ n i ω := by
  exact Tuple.monotone_sort (fun j : Fin (n + 1) ↦ σ j ω)

omit [MeasurableSpace Ω] in
/-- Every member of the prefix occurs among its order statistics. -/
theorem exists_sortedPrefixTime_eq
    (σ : ℕ → Ω → ℝ≥0) (n k : ℕ) (hk : k ≤ n) (ω : Ω) :
    ∃ i : Fin (n + 1), sortedPrefixTime σ n i ω = σ k ω := by
  let j : Fin (n + 1) := ⟨k, Nat.lt_succ_iff.mpr hk⟩
  let f : Fin (n + 1) → ℝ≥0 := fun l ↦ σ l ω
  refine ⟨(Tuple.sort f).symm j, ?_⟩
  simp only [sortedPrefixTime, f, Equiv.apply_symm_apply, j]

/-- A pathwise order statistic of finite stopping times is a stopping time. -/
theorem sortedPrefixTime_isStoppingTime
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {σ : ℕ → Ω → ℝ≥0}
    (hσ : ∀ k, IsStoppingTime ℱ
      (fun ω ↦ (σ k ω : WithTop ℝ≥0)))
    (n : ℕ) (i : Fin (n + 1)) :
    IsStoppingTime ℱ
      (fun ω ↦ (sortedPrefixTime σ n i ω : WithTop ℝ≥0)) := by
  classical
  intro t
  let countLE : Ω → ℕ := fun ω ↦
    ∑ j : Fin (n + 1), if σ j ω ≤ t then 1 else 0
  have hcountMeas : Measurable[ℱ t] countLE := by
    apply Finset.measurable_sum Finset.univ
    intro j _
    apply Measurable.ite
    · simpa only [WithTop.coe_le_coe] using hσ j t
    · exact measurable_const
    · exact measurable_const
  have hevent :
      {ω | (sortedPrefixTime σ n i ω : WithTop ℝ≥0) ≤ t} =
        {ω | i.1 < countLE ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, WithTop.coe_le_coe]
    let f : Fin (n + 1) → ℝ≥0 := fun j ↦ σ j ω
    change (f ∘ Tuple.sort f) i ≤ t ↔ i.1 < countLE ω
    have hsorted := Tuple.monotone_sort f
    rw [← Tuple.lt_card_le_iff_apply_le_of_monotone
      (a := t) (j := i) hsorted]
    rw [Finset.card_filter]
    have hsum :
        (∑ j, if (f ∘ Tuple.sort f) j ≤ t then 1 else 0) =
          ∑ j, if f j ≤ t then 1 else 0 := by
      exact Equiv.sum_comp (Tuple.sort f)
        (fun j ↦ if f j ≤ t then 1 else 0)
    rw [hsum]
  rw [hevent]
  exact measurableSet_Ioi.preimage hcountMeas

/-- Conditional expectations with respect to two stopping-time sigma
algebras agree locally where the stopping times agree. -/
theorem condExp_ae_eq_restrict_of_stoppingTime_eq
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {σ τ : Ω → ℝ≥0}
    (hσ : IsStoppingTime ℱ (fun ω ↦ (σ ω : WithTop ℝ≥0)))
    (hτ : IsStoppingTime ℱ (fun ω ↦ (τ ω : WithTop ℝ≥0)))
    (J : Ω → ℝ) :
    μ[J | hσ.measurableSpace] =ᵐ[μ.restrict {ω | σ ω = τ ω}]
      μ[J | hτ.measurableSpace] := by
  have heqMeas : MeasurableSet[hσ.measurableSpace]
      {ω | σ ω = τ ω} := by
    simpa only [WithTop.coe_eq_coe] using
      hσ.measurableSet_eq_stopping_time hτ
  apply condExp_ae_eq_restrict_of_measurableSpace_eq_on
    hσ.measurableSpace_le hτ.measurableSpace_le heqMeas
  intro s
  rw [hσ.measurableSet, hτ.measurableSet]
  constructor
  · rintro ⟨hs, hsσ⟩
    refine ⟨hs, fun t ↦ ?_⟩
    have hevent :
        {ω | σ ω = τ ω} ∩ s ∩
            {ω | (τ ω : WithTop ℝ≥0) ≤ t} =
          {ω | σ ω = τ ω} ∩ s ∩
            {ω | (σ ω : WithTop ℝ≥0) ≤ t} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      grind
    rw [hevent]
    exact hsσ t
  · rintro ⟨hs, hsτ⟩
    refine ⟨hs, fun t ↦ ?_⟩
    have hevent :
        {ω | σ ω = τ ω} ∩ s ∩
            {ω | (σ ω : WithTop ℝ≥0) ≤ t} =
          {ω | σ ω = τ ω} ∩ s ∩
            {ω | (τ ω : WithTop ℝ≥0) ≤ t} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      grind
    rw [hevent]
    exact hsτ t

/-- Ambient almost-everywhere implication form of
`condExp_ae_eq_restrict_of_stoppingTime_eq`. -/
theorem condExp_ae_eq_of_stoppingTime_eq
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {σ τ : Ω → ℝ≥0}
    (hσ : IsStoppingTime ℱ (fun ω ↦ (σ ω : WithTop ℝ≥0)))
    (hτ : IsStoppingTime ℱ (fun ω ↦ (τ ω : WithTop ℝ≥0)))
    (J : Ω → ℝ) :
    ∀ᵐ ω ∂μ, σ ω = τ ω →
      μ[J | hσ.measurableSpace] ω = μ[J | hτ.measurableSpace] ω := by
  have heqMeas : MeasurableSet {ω | σ ω = τ ω} := by
    exact hσ.measurableSpace_le _ (by
      simpa only [WithTop.coe_eq_coe] using
        hσ.measurableSet_eq_stopping_time hτ)
  have hlocal := condExp_ae_eq_restrict_of_stoppingTime_eq
    (μ := μ) hσ hτ J
  rw [Filter.EventuallyEq, ae_restrict_iff' heqMeas] at hlocal
  exact hlocal

/-- Doob's `L²` estimate for the conditional expectations at a finite
prefix of arbitrary stopping times.  Pathwise sorting is used only inside
the proof; no global ordering of the stopping times is assumed. -/
theorem lintegral_condExp_prefixRunningMax_sq_le
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {σ : ℕ → Ω → ℝ≥0}
    (hσ : ∀ k, IsStoppingTime ℱ
      (fun ω ↦ (σ k ω : WithTop ℝ≥0)))
    {J : Ω → ℝ} (hJ : MemLp J (2 : ℝ≥0∞) μ) (n : ℕ) :
    (∫⁻ ω, ENNReal.ofReal
        ((finiteRunningMax
          (fun k ω ↦ |μ[J | (hσ k).measurableSpace] ω|) n ω) ^ 2) ∂μ) ≤
      4 * ∫⁻ ω, ENNReal.ofReal ((J ω) ^ 2) ∂μ := by
  let rank : ℕ → Fin (n + 1) := fun k ↦
    ⟨min k n, Nat.lt_succ_of_le (min_le_right k n)⟩
  have hrankMono : Monotone rank := by
    intro k l hkl
    exact min_le_min hkl le_rfl
  let θ : Fin (n + 1) → Ω → ℝ≥0 := fun i ↦
    sortedPrefixTime σ n i
  have hθ : ∀ i, IsStoppingTime ℱ
      (fun ω ↦ (θ i ω : WithTop ℝ≥0)) := fun i ↦
    sortedPrefixTime_isStoppingTime hσ n i
  let m : Filtration ℕ (inferInstance : MeasurableSpace Ω) :=
    { seq := fun k ↦ (hθ (rank k)).measurableSpace
      mono' := fun k l hkl ↦
        (hθ (rank k)).measurableSpace_mono (hθ (rank l))
          (fun ω ↦ WithTop.coe_le_coe.mpr
            (sortedPrefixTime_mono σ n ω (hrankMono hkl)))
      le' := fun k ↦ (hθ (rank k)).measurableSpace_le }
  let Y : ℕ → Ω → ℝ := fun k ↦ μ[J | m k]
  let Z : ℕ → Ω → ℝ := fun k ω ↦ |Y k ω|
  have hY : Martingale Y m μ := martingale_condExp J m μ
  have hZ : Submartingale Z m μ :=
    FTAPTheorem42.Martingale.abs_submartingale hY
  have hZNonneg : 0 ≤ Z := fun _ _ ↦ abs_nonneg _
  let G : ChronologicalGrid ℕ n :=
    { time := fun i ↦ i.1
      monotone_time := fun _ _ hij ↦ hij }
  have hterminal : MemLp
      (Z (G.time ⟨n, Nat.lt_succ_self n⟩))
        (2 : ℝ≥0∞) μ := by
    change MemLp |μ[J | m n]| (2 : ℝ≥0∞) μ
    exact (hJ.condExp (by norm_num)).abs
  have hDoob :=
    ChronologicalGrid.Submartingale.lintegral_sq_finiteRunningMax_sample_le_four_mul
      (G := G) hZ hZNonneg hterminal
  have hsampleEq : ∀ k, k ≤ n → G.natSample Z k = Z k := by
    intro k hk
    change Z (min k n) = Z k
    rw [min_eq_left hk]
  have hmaxEq : finiteRunningMax (G.natSample Z) n =
      finiteRunningMax Z n := by
    funext ω
    unfold finiteRunningMax
    apply Finset.sup'_congr Finset.nonempty_range_add_one rfl
    intro k hk
    exact congrFun (hsampleEq k
      (Nat.le_of_lt_succ (Finset.mem_range.1 hk))) ω
  rw [hmaxEq] at hDoob
  have hterminalBound :=
    CountableCondExpEnvelope.lintegral_condExp_sq_le
      (ℱ := m) hJ n
  have hsortedBound :
      (∫⁻ ω, ENNReal.ofReal ((finiteRunningMax Z n ω) ^ 2) ∂μ) ≤
        4 * ∫⁻ ω, ENNReal.ofReal ((J ω) ^ 2) ∂μ := by
    exact hDoob.trans (mul_le_mul_of_nonneg_left (by
      simpa only [G, Z, Y, sq_abs] using hterminalBound) (by positivity))
  have hcoord : ∀ k, k ≤ n →
      (fun ω ↦ |μ[J | (hσ k).measurableSpace] ω|) ≤ᵐ[μ]
        finiteRunningMax Z n := by
    intro k hk
    have heq : ∀ i : Fin (n + 1), ∀ᵐ ω ∂μ,
        σ k ω = θ i ω →
          μ[J | (hσ k).measurableSpace] ω =
            μ[J | (hθ i).measurableSpace] ω := by
      intro i
      exact condExp_ae_eq_of_stoppingTime_eq
        (μ := μ) (hσ k) (hθ i) J
    have heqAll : ∀ᵐ ω ∂μ, ∀ i : Fin (n + 1),
        σ k ω = θ i ω →
          μ[J | (hσ k).measurableSpace] ω =
            μ[J | (hθ i).measurableSpace] ω :=
      ae_all_iff.2 heq
    filter_upwards [heqAll] with ω hω
    obtain ⟨i, hi⟩ := exists_sortedPrefixTime_eq σ n k hk ω
    have hrank : rank i.1 = i := by
      ext
      simp [rank, Nat.le_of_lt_succ i.2]
    calc
      |μ[J | (hσ k).measurableSpace] ω| =
          |μ[J | (hθ i).measurableSpace] ω| := by
        rw [hω i hi.symm]
      _ = Z i.1 ω := by
        simp only [Z, Y, m, hrank]
      _ ≤ finiteRunningMax Z n ω :=
        Finset.le_sup' (fun l ↦ Z l ω)
          (Finset.mem_range.2 i.2)
  have hmaxDom :
      finiteRunningMax
          (fun k ω ↦ |μ[J | (hσ k).measurableSpace] ω|) n ≤ᵐ[μ]
        finiteRunningMax Z n := by
    have hcoordAll : ∀ᵐ ω ∂μ, ∀ k, k ≤ n →
        |μ[J | (hσ k).measurableSpace] ω| ≤
          finiteRunningMax Z n ω := by
      rw [ae_all_iff]
      intro k
      by_cases hk : k ≤ n
      · filter_upwards [hcoord k hk] with ω hω
        exact fun _ ↦ hω
      · exact Filter.Eventually.of_forall fun _ hkn ↦ (hk hkn).elim
    filter_upwards [hcoordAll] with ω hω
    unfold finiteRunningMax
    apply Finset.sup'_le
    intro k hk
    exact hω k (Nat.le_of_lt_succ (Finset.mem_range.1 hk))
  exact (lintegral_mono_ae (hmaxDom.mono fun ω hω ↦
    ENNReal.ofReal_le_ofReal ((sq_le_sq₀
      (finiteRunningMax_nonneg
        (fun k ω ↦ |μ[J | (hσ k).measurableSpace] ω|) n
        (fun _ _ ↦ abs_nonneg _) ω)
      (finiteRunningMax_nonneg Z n hZNonneg ω)).2 hω))).trans
    hsortedBound

omit [MeasurableSpace Ω] in
/-- The finite running maximum increases with its horizon. -/
theorem finiteRunningMax_mono_horizon (f : ℕ → Ω → ℝ) :
    Monotone (finiteRunningMax f) := by
  intro n l hnl ω
  obtain ⟨k, hk, hkEq⟩ := Finset.exists_mem_eq_sup'
    (s := Finset.range (n + 1)) Finset.nonempty_range_add_one
    (fun j ↦ f j ω)
  rw [show finiteRunningMax f n ω = f k ω by exact hkEq]
  exact Finset.le_sup' (fun j ↦ f j ω)
    (Finset.mem_range.2 ((Finset.mem_range.1 hk).trans_le
      (Nat.succ_le_succ hnl)))

/-- Squared envelope of conditional expectations at a countable family of
arbitrary stopping times. -/
noncomputable def condExpSqEnvelope
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (μ : Measure Ω) (σ : ℕ → Ω → ℝ≥0)
    (hσ : ∀ k, IsStoppingTime ℱ
      (fun ω ↦ (σ k ω : WithTop ℝ≥0)))
    (J : Ω → ℝ) : Ω → ℝ≥0∞ :=
  fun ω ↦ ⨆ n, ENNReal.ofReal
    ((finiteRunningMax
      (fun k ω ↦ |μ[J | (hσ k).measurableSpace] ω|) n ω) ^ 2)

/-- Every coordinate is bounded by the squared stopping-time envelope. -/
theorem ofReal_condExp_sq_le_condExpSqEnvelope
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} {σ : ℕ → Ω → ℝ≥0}
    (hσ : ∀ k, IsStoppingTime ℱ
      (fun ω ↦ (σ k ω : WithTop ℝ≥0)))
    (J : Ω → ℝ) (k : ℕ) (ω : Ω) :
    ENNReal.ofReal ((μ[J | (hσ k).measurableSpace] ω) ^ 2) ≤
      condExpSqEnvelope ℱ μ σ hσ J ω := by
  let f : ℕ → Ω → ℝ := fun l ω ↦
    |μ[J | (hσ l).measurableSpace] ω|
  have hvalue : f k ω ≤ finiteRunningMax f k ω :=
    Finset.le_sup' (fun l ↦ f l ω)
      (Finset.mem_range.2 (Nat.lt_succ_self k))
  have hsquare : (f k ω) ^ 2 ≤ (finiteRunningMax f k ω) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _)
      (finiteRunningMax_nonneg f k (fun _ _ ↦ abs_nonneg _) ω)).2 hvalue
  change ENNReal.ofReal ((μ[J | (hσ k).measurableSpace] ω) ^ 2) ≤
    ⨆ n, ENNReal.ofReal ((finiteRunningMax f n ω) ^ 2)
  simpa only [f, sq_abs] using
    (ENNReal.ofReal_le_ofReal hsquare).trans
      (le_iSup (fun n ↦ ENNReal.ofReal
        ((finiteRunningMax f n ω) ^ 2)) k)

/-- Doob's inequality on sorted finite prefixes, followed by monotone
convergence, controls a countable family of stopping-time conditional
expectations. -/
theorem lintegral_condExpSqEnvelope_le
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {σ : ℕ → Ω → ℝ≥0}
    (hσ : ∀ k, IsStoppingTime ℱ
      (fun ω ↦ (σ k ω : WithTop ℝ≥0)))
    {J : Ω → ℝ} (hJ : MemLp J (2 : ℝ≥0∞) μ) :
    (∫⁻ ω, condExpSqEnvelope ℱ μ σ hσ J ω ∂μ) ≤
      4 * ∫⁻ ω, ENNReal.ofReal ((J ω) ^ 2) ∂μ := by
  let f : ℕ → Ω → ℝ := fun k ω ↦
    |μ[J | (hσ k).measurableSpace] ω|
  let g : ℕ → Ω → ℝ≥0∞ := fun n ω ↦
    ENNReal.ofReal ((finiteRunningMax f n ω) ^ 2)
  have hgMeas : ∀ n, Measurable (g n) := by
    intro n
    apply Measurable.ennreal_ofReal
    apply Measurable.pow_const
    apply measurable_finiteRunningMax f n
    intro k _
    have hcond : StronglyMeasurable[(hσ k).measurableSpace]
        μ[J | (hσ k).measurableSpace] := stronglyMeasurable_condExp
    simpa only [Real.norm_eq_abs] using
      (hcond.mono (hσ k).measurableSpace_le).norm.measurable
  have hgMono : Monotone g := by
    intro n l hnl ω
    apply ENNReal.ofReal_le_ofReal
    exact (sq_le_sq₀
      (finiteRunningMax_nonneg f n (fun _ _ ↦ abs_nonneg _) ω)
      (finiteRunningMax_nonneg f l (fun _ _ ↦ abs_nonneg _) ω)).2
        (finiteRunningMax_mono_horizon f hnl ω)
  change (∫⁻ ω, ⨆ n, g n ω ∂μ) ≤ _
  rw [lintegral_iSup hgMeas hgMono]
  exact iSup_le fun n ↦
    lintegral_condExp_prefixRunningMax_sq_le hσ hJ n

/-- Diagonal enumeration of all stopping times in a countable family of
announcements. -/
def announcementTime
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {τ : ℕ → Ω → ℝ≥0}
    (a : ∀ n, StoppingTimeAnnouncement ℱ (τ n))
    (l : ℕ) : Ω → ℝ≥0 :=
  (a (Nat.unpair l).1).time (Nat.unpair l).2

/-- Every entry of the diagonal announcement enumeration is a stopping
time. -/
theorem announcementTime_isStoppingTime
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {τ : ℕ → Ω → ℝ≥0}
    (a : ∀ n, StoppingTimeAnnouncement ℱ (τ n)) (l : ℕ) :
    IsStoppingTime ℱ
      (fun ω ↦ (announcementTime a l ω : WithTop ℝ≥0)) := by
  exact (a (Nat.unpair l).1).isStoppingTime (Nat.unpair l).2

/-- Lévy upward convergence bounds every predictable-graph conditional
expectation by the common envelope over all announcing stopping times. -/
theorem condExp_graph_sq_le_envelope_ae
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {τ : ℕ → Ω → ℝ≥0}
    (a : ∀ n, StoppingTimeAnnouncement ℱ (τ n))
    {J : Ω → ℝ} :
    ∀ n, (fun ω ↦ ENNReal.ofReal
      ((μ[J | predictableGraphMeasurableSpace ℱ (τ n)] ω) ^ 2)) ≤ᵐ[μ]
        condExpSqEnvelope ℱ μ (announcementTime a)
          (announcementTime_isStoppingTime a) J := by
  intro n
  let m : ℕ → MeasurableSpace Ω := fun k ↦
    ((a n).isStoppingTime k).measurableSpace
  have hmMono : Monotone m := by
    intro i j hij
    exact ((a n).isStoppingTime i).measurableSpace_mono
      ((a n).isStoppingTime j) fun ω ↦
        WithTop.coe_le_coe.mpr ((a n).monotone ω hij)
  have hmSup : (⨆ k, m k) =
      predictableGraphMeasurableSpace ℱ (τ n) :=
    (predictableGraphMeasurableSpace_eq_iSup_measurableSpace
      (a n).isStoppingTime (a n).lt (a n).tendsto).symm
  let ℱm : Filtration ℕ (inferInstance : MeasurableSpace Ω) :=
    { seq := m
      mono' := hmMono
      le' := fun k ↦ ((a n).isStoppingTime k).measurableSpace_le }
  have htendCond := MeasureTheory.tendsto_ae_condExp
    (μ := μ) (ℱ := ℱm) J
  rw [show (⨆ k, ℱm k) =
      predictableGraphMeasurableSpace ℱ (τ n) by exact hmSup] at htendCond
  have henum : ∀ k,
      μ[J | m k] =ᵐ[μ]
        μ[J | (announcementTime_isStoppingTime a
          (Nat.pair n k)).measurableSpace] := by
    intro k
    have heq := condExp_ae_eq_of_stoppingTime_eq
      (μ := μ) ((a n).isStoppingTime k)
        (announcementTime_isStoppingTime a (Nat.pair n k)) J
    filter_upwards [heq] with ω hω
    apply hω
    rw [announcementTime, Nat.unpair_pair]
  filter_upwards [htendCond, ae_all_iff.2 henum]
    with ω htendω henumω
  have htendSq : Tendsto (fun k ↦ ENNReal.ofReal
      ((μ[J | m k] ω) ^ 2)) atTop
      (𝓝 (ENNReal.ofReal
        ((μ[J | predictableGraphMeasurableSpace ℱ (τ n)] ω) ^ 2))) := by
    apply ENNReal.tendsto_ofReal
    simpa only [pow_two] using htendω.mul htendω
  apply le_of_tendsto htendSq
  filter_upwards [] with k
  have hcoordinate := ofReal_condExp_sq_le_condExpSqEnvelope
    (μ := μ) (announcementTime_isStoppingTime a) J (Nat.pair n k) ω
  rw [henumω k]
  exact hcoordinate

end StoppingTimeCondExpEnvelope

end FTAPTheorem42
