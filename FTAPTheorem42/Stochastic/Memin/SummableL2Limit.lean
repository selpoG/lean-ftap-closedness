/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Memin.SummableComponentLimitData
import Mathlib.Analysis.Normed.Group.Completeness
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Topology.MetricSpace.PiNat

/-!
# `L²` limits from summable successive differences

Local square-integrable martingale controls turn terminal martingale
differences into `L²` distances between predictable integrands.  This module
performs the analytic part of that argument.  A summable series of successive
`L²` distances identifies the pointwise `limUnder`, proves that it belongs to
`L²`, and gives convergence in the `L²` seminorm.
-/

open Filter MeasureTheory Topology
open scoped BigOperators ENNReal NNReal PiCountable

namespace FTAPTheorem42.MeminL2

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}

/-- Summable successive `L²` distances identify the pointwise `limUnder` as
an `L²` function and force convergence to it in `L²`. -/
theorem memLp_two_limit_of_summable_steps
    (f : ℕ → α → ℝ)
    (hf : ∀ n, MemLp (f n) (2 : ℝ≥0∞) ν)
    (hSteps : (∑' k,
      eLpNorm (fun x => f (k + 1) x - f k x) (2 : ℝ≥0∞) ν) ≠ ∞) :
    let limit := fun x => limUnder atTop (fun n => f n x)
    MemLp limit (2 : ℝ≥0∞) ν ∧
      (∀ᵐ x ∂ν, Tendsto (fun n => f n x) atTop (𝓝 (limit x))) ∧
      Tendsto (fun n =>
        eLpNorm (fun x => f n x - limit x) (2 : ℝ≥0∞) ν)
          atTop (𝓝 0) := by
  let step : ℕ → α → ℝ := fun k x => f (k + 1) x - f k x
  have hStepMemLp : ∀ k, MemLp (step k) (2 : ℝ≥0∞) ν := by
    intro k
    exact (hf (k + 1)).sub (hf k)
  let F : ℕ → Lp ℝ (2 : ℝ≥0∞) ν := fun n =>
    (hf n).toLp (f n)
  let G : ℕ → Lp ℝ (2 : ℝ≥0∞) ν := fun k =>
    (hStepMemLp k).toLp (step k)
  have hGEnorm : (∑' k, ‖G k‖ₑ) ≠ ∞ := by
    simpa only [G, Lp.enorm_toLp, step] using hSteps
  have hGSummable : Summable G := Summable.of_enorm hGEnorm
  let Flimit : Lp ℝ (2 : ℝ≥0∞) ν := F 0 + ∑' k, G k
  have hG_eq : ∀ k, G k = F (k + 1) - F k := by
    intro k
    dsimp only [G, F, step]
    exact MemLp.toLp_sub (hf (k + 1)) (hf k)
  have hF_partial : ∀ n,
      F n = F 0 + ∑ k ∈ Finset.range n, G k := by
    intro n
    rw [show (∑ k ∈ Finset.range n, G k) = F n - F 0 by
      simpa only [hG_eq] using Finset.sum_range_sub F n]
    abel
  have hF_tendsto : Tendsto F atTop (𝓝 Flimit) := by
    have hSeries := hGSummable.tendsto_sum_tsum_nat
    have hAdd : Tendsto
        (fun n => F 0 + ∑ k ∈ Finset.range n, G k) atTop
        (𝓝 (F 0 + ∑' k, G k)) :=
      tendsto_const_nhds.add hSeries
    rw [show F = fun n => F 0 + ∑ k ∈ Finset.range n, G k by
      funext n
      exact hF_partial n]
    simpa only [Flimit] using hAdd
  let limit : α → ℝ := fun x => limUnder atTop (fun n => f n x)
  have hPointwise : ∀ᵐ x ∂ν,
      Tendsto (fun n => f n x) atTop (𝓝 (limit x)) := by
    have hSummableNorm : ∀ᵐ x ∂ν, Summable (fun k => ‖step k x‖) :=
      summable_norm_of_tsum_eLpNorm_ne_top (p := (2 : ℝ≥0∞))
        (by norm_num)
          (by simpa only [step] using hSteps)
    filter_upwards [hSummableNorm] with x hx
    have hDistSummable : Summable (fun k => dist (f k x) (f (k + 1) x)) := by
      simpa only [step, Real.norm_eq_abs, Real.dist_eq, abs_sub_comm] using hx
    exact (cauchySeq_of_summable_dist hDistSummable).tendsto_limUnder
  obtain ⟨cutoff, hCutoff, hSubsequence⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hF_tendsto).exists_seq_tendsto_ae
  have hCoe : ∀ᵐ x ∂ν, ∀ n, F n x = f n x := by
    exact ae_all_iff.mpr fun n => MemLp.coeFn_toLp (hf n)
  have hLimitAE : (⇑Flimit) =ᵐ[ν] limit := by
    filter_upwards [hSubsequence, hPointwise, hCoe] with x hLp hRaw hCoeAt
    have hLpRaw : Tendsto (fun n => f (cutoff n) x) atTop (𝓝 (Flimit x)) :=
      hLp.congr' (Filter.Eventually.of_forall fun n => hCoeAt (cutoff n))
    exact tendsto_nhds_unique hLpRaw (hRaw.comp hCutoff.tendsto_atTop)
  have hLimitMemLp : MemLp limit (2 : ℝ≥0∞) ν :=
    (Lp.memLp Flimit).ae_eq hLimitAE
  have hLimitToLp : hLimitMemLp.toLp limit = Flimit := by
    exact (MemLp.toLp_congr hLimitMemLp (Lp.memLp Flimit) hLimitAE.symm).trans
      (Lp.toLp_coeFn Flimit (Lp.memLp Flimit))
  have hRawLp : Tendsto (fun n => (hf n).toLp (f n)) atTop
      (𝓝 (hLimitMemLp.toLp limit)) := by
    simpa only [F, hLimitToLp] using hF_tendsto
  have hNorm :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf limit hLimitMemLp).mp hRawLp
  exact ⟨hLimitMemLp, hPointwise, hNorm⟩

/-- Every `L²`-Cauchy sequence has a strict subsequence whose successive
`L²` distances are summable; its pointwise `limUnder` is the corresponding
`L²` limit. -/
theorem exists_subsequence_memLp_two_limit_of_cauchy
    (f : ℕ → α → ℝ)
    (hf : ∀ n, MemLp (f n) (2 : ℝ≥0∞) ν)
    (hCauchy : CauchySeq (fun n => (hf n).toLp (f n))) :
    ∃ cutoff : ℕ → ℕ, StrictMono cutoff ∧
      let limit := fun x => limUnder atTop (fun n => f (cutoff n) x)
      MemLp limit (2 : ℝ≥0∞) ν ∧
        (∀ᵐ x ∂ν,
          Tendsto (fun n => f (cutoff n) x) atTop (𝓝 (limit x))) ∧
        Tendsto (fun n => eLpNorm (fun x =>
          f (cutoff n) x - limit x) (2 : ℝ≥0∞) ν) atTop (𝓝 0) := by
  let F : ℕ → Lp ℝ (2 : ℝ≥0∞) ν := fun n => (hf n).toLp (f n)
  obtain ⟨cutoff, hCutoff, hDistSummable⟩ :=
    Metric.exists_subseq_summable_dist_of_cauchySeq F hCauchy
  refine ⟨cutoff, hCutoff, ?_⟩
  apply memLp_two_limit_of_summable_steps
  · exact fun n => hf (cutoff n)
  rw [show (fun k => eLpNorm (fun x =>
      f (cutoff (k + 1)) x - f (cutoff k) x)
        (2 : ℝ≥0∞) ν) = fun k => ENNReal.ofReal
          (dist (F (cutoff (k + 1))) (F (cutoff k))) by
    funext k
    calc
      eLpNorm (fun x =>
          f (cutoff (k + 1)) x - f (cutoff k) x)
            (2 : ℝ≥0∞) ν =
          edist (F (cutoff (k + 1))) (F (cutoff k)) := by
            change eLpNorm
              (f (cutoff (k + 1)) - f (cutoff k))
                (2 : ℝ≥0∞) ν = _
            exact (Lp.edist_toLp_toLp
              (f (cutoff (k + 1))) (f (cutoff k))
              (hf (cutoff (k + 1))) (hf (cutoff k))).symm
      _ = ENNReal.ofReal
          (dist (F (cutoff (k + 1))) (F (cutoff k))) :=
        Lp.edist_dist _ _]
  exact hDistSummable.tsum_ofReal_ne_top

/-- An `L²`-Cauchy sequence which already has an almost-everywhere raw
limit converges to that same limit in `L²`.  This is the uniqueness bridge
used to identify stopped component limits with the Hilbert-space limits of
their terminal coordinates. -/
theorem memLp_two_of_cauchy_of_ae_tendsto
    (f : ℕ → α → ℝ)
    (hf : ∀ n, MemLp (f n) (2 : ℝ≥0∞) ν)
    (hCauchy : CauchySeq (fun n => (hf n).toLp (f n)))
    (g : α → ℝ)
    (hTendsto : ∀ᵐ x ∂ν, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    MemLp g (2 : ℝ≥0∞) ν ∧
      Tendsto (fun n => eLpNorm (fun x => f n x - g x)
        (2 : ℝ≥0∞) ν) atTop (𝓝 0) := by
  obtain ⟨cutoff, hCutoff, hLimitMemLp, hLimitAE, hLimitNorm⟩ :=
    exists_subsequence_memLp_two_limit_of_cauchy f hf hCauchy
  let limit : α → ℝ := fun x => limUnder atTop (fun n => f (cutoff n) x)
  have hLimitEq : limit =ᵐ[ν] g := by
    filter_upwards [hLimitAE, hTendsto] with x hSubsequence hFull
    exact tendsto_nhds_unique hSubsequence
      (hFull.comp hCutoff.tendsto_atTop)
  have hg : MemLp g (2 : ℝ≥0∞) ν := hLimitMemLp.ae_eq hLimitEq
  have hSubsequenceLp : Tendsto (fun n =>
      (hf (cutoff n)).toLp (f (cutoff n))) atTop
      (𝓝 (hLimitMemLp.toLp limit)) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n => f (cutoff n)) (fun n => hf (cutoff n))
        limit hLimitMemLp).mpr
    change Tendsto (fun n => eLpNorm (fun x =>
      f (cutoff n) x - limit x) (2 : ℝ≥0∞) ν) atTop (𝓝 0)
    simpa only [limit] using hLimitNorm
  have hLimitToLp : hLimitMemLp.toLp limit = hg.toLp g :=
    MemLp.toLp_congr hLimitMemLp hg hLimitEq
  have hSubsequenceLp' : Tendsto (fun n =>
      (hf (cutoff n)).toLp (f (cutoff n))) atTop
      (𝓝 (hg.toLp g)) := by
    rwa [hLimitToLp] at hSubsequenceLp
  have hFullLp : Tendsto (fun n => (hf n).toLp (f n)) atTop
      (𝓝 (hg.toLp g)) := by
    apply tendsto_nhds_of_cauchySeq_of_subseq hCauchy
      hCutoff.tendsto_atTop
    change Tendsto (fun n =>
      (hf (cutoff n)).toLp (f (cutoff n))) atTop (𝓝 (hg.toLp g))
    exact hSubsequenceLp'
  exact ⟨hg, (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).mp hFullLp⟩

/-- An `L²`-Cauchy sequence has one finite uniform bound on its extended
`L²` seminorms. -/
theorem exists_eLpNorm_two_bound_of_cauchy
    (f : ℕ → α → ℝ)
    (hf : ∀ n, MemLp (f n) (2 : ℝ≥0∞) ν)
    (hCauchy : CauchySeq (fun n => (hf n).toLp (f n))) :
    ∃ B : ℝ≥0, ∀ n, eLpNorm (f n) (2 : ℝ≥0∞) ν ≤ B := by
  obtain ⟨R, hR⟩ := hCauchy.isBounded_range.exists_norm_le
  let B : ℝ≥0 := ⟨max R 0, le_max_right _ _⟩
  refine ⟨B, fun n => ?_⟩
  rw [← Lp.enorm_toLp (hf n)]
  exact_mod_cast (hR ((hf n).toLp (f n)) ⟨n, rfl⟩).trans
    (le_max_left R 0)

/-- A countable family of `L²` controls admits one common strict subsequence.
For every control, the selected functions converge almost everywhere and in
`L²` to the same pointwise `limUnder`. -/
theorem exists_common_subsequence_memLp_two_limit_of_cauchy
    (control : ℕ → Measure α)
    (f : ℕ → α → ℝ)
    (hf : ∀ r n, MemLp (f n) (2 : ℝ≥0∞) (control r))
    (hCauchy : ∀ r, CauchySeq (fun n =>
      (hf r n).toLp (f n))) :
    ∃ cutoff : ℕ → ℕ, StrictMono cutoff ∧ ∀ r,
      let limit := fun x => limUnder atTop (fun n => f (cutoff n) x)
      MemLp limit (2 : ℝ≥0∞) (control r) ∧
        (∀ᵐ x ∂control r,
          Tendsto (fun n => f (cutoff n) x) atTop (𝓝 (limit x))) ∧
        Tendsto (fun n => eLpNorm (fun x =>
          f (cutoff n) x - limit x) (2 : ℝ≥0∞) (control r))
            atTop (𝓝 0) := by
  let U : ℕ → (∀ r, Lp ℝ (2 : ℝ≥0∞) (control r)) := fun n r =>
    (hf r n).toLp (f n)
  let : MetricSpace (∀ r, Lp ℝ (2 : ℝ≥0∞) (control r)) :=
    PiCountable.metricSpace
  have hUCauchy : CauchySeq U := by
    change Cauchy (Filter.map U atTop)
    rw [cauchy_pi_iff' (fun r => Lp ℝ (2 : ℝ≥0∞) (control r))]
    intro r
    change CauchySeq (fun n => U n r)
    simpa only [U] using hCauchy r
  obtain ⟨cutoff, hCutoff, hProductSummable⟩ :=
    Metric.exists_subseq_summable_dist_of_cauchySeq U hUCauchy
  refine ⟨cutoff, hCutoff, fun r => ?_⟩
  have hWeightPos : 0 < (2⁻¹ : ℝ) ^ Encodable.encode r := by positivity
  have hProductSmall : ∀ᶠ k in atTop,
      dist (U (cutoff (k + 1))) (U (cutoff k)) <
        (2⁻¹ : ℝ) ^ Encodable.encode r :=
    (tendsto_order.1 hProductSummable.tendsto_atTop_zero).2 _ hWeightPos
  have hCoordinateSummable : Summable (fun k =>
      dist (U (cutoff (k + 1)) r) (U (cutoff k) r)) :=
    hProductSummable.of_norm_bounded_eventually_nat <| by
      filter_upwards [hProductSmall] with k hk
      rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg]
      exact PiCountable.dist_le_dist_pi_of_dist_lt hk
  apply memLp_two_limit_of_summable_steps
  · exact fun n => hf r (cutoff n)
  rw [show (fun k => eLpNorm (fun x =>
      f (cutoff (k + 1)) x - f (cutoff k) x)
        (2 : ℝ≥0∞) (control r)) = fun k => ENNReal.ofReal
          (dist (U (cutoff (k + 1)) r) (U (cutoff k) r)) by
    funext k
    calc
      eLpNorm (fun x =>
          f (cutoff (k + 1)) x - f (cutoff k) x)
            (2 : ℝ≥0∞) (control r) =
          edist (U (cutoff (k + 1)) r) (U (cutoff k) r) := by
            change eLpNorm
              (f (cutoff (k + 1)) - f (cutoff k))
                (2 : ℝ≥0∞) (control r) = _
            exact (Lp.edist_toLp_toLp
              (f (cutoff (k + 1))) (f (cutoff k))
              (hf r (cutoff (k + 1))) (hf r (cutoff k))).symm
      _ = ENNReal.ofReal
          (dist (U (cutoff (k + 1)) r) (U (cutoff k) r)) :=
        Lp.edist_dist _ _]
  exact hCoordinateSummable.tsum_ofReal_ne_top

end FTAPTheorem42.MeminL2
