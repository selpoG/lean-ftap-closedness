/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Core.ForwardConvex
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import FTAPTheorem42.Core.Closedness
import FTAPTheorem42.Trading.Basic

/-! # Terminal improvements and maximality

Forward-convex combinations retain persistent positive gaps. This contradicts
maximality in the terminal-claim closure, also when the base is dominated only
up to an almost-everywhere vanishing lower error. Varying-event pasting retains
the common almost-everywhere limit. -/

namespace FTAPTheorem42

open Filter MeasureTheory Topology
open scoped BigOperators ENNReal MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Pointwise finite-convex clipping -/

omit [MeasurableSpace Ω] in
theorem ForwardConvexWeights.apply_min_le_min_apply
    (W : ForwardConvexWeights) {f : ℕ → Ω → ℝ} {ε : ℝ}
    (n : ℕ) (ω : Ω) :
    W.apply (fun i x => min (f i x) ε) n ω ≤
      min (W.apply f n ω) ε := by
  change (∑ i ∈ W.support n, W.weight n i * min (f i ω) ε) ≤
    min (∑ i ∈ W.support n, W.weight n i * f i ω) ε
  apply le_min
  · apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (min_le_left _ _)
      (W.nonneg n i hi)
  · calc
      ∑ i ∈ W.support n, W.weight n i * min (f i ω) ε ≤
          ∑ i ∈ W.support n, W.weight n i * ε := by
            apply Finset.sum_le_sum
            intro i hi
            exact mul_le_mul_of_nonneg_left (min_le_right _ _)
              (W.nonneg n i hi)
      _ = ε := by
        rw [← Finset.sum_mul, W.sum_eq_one n, one_mul]

/-! ### Positive capped mass cannot vanish -/

/--
If every nonnegative gap exceeds `ε` on a set of measure at least `δ`, then no
forward-convexification can converge a.e. to zero.  The events are allowed to
be only null-measurable; all inequalities on them are interpreted a.e.
-/
theorem not_tendstoAE_zero_forwardConvex_apply_of_gap_mass
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {gap : ℕ → Ω → ℝ} {s : ℕ → Set Ω} (W : ForwardConvexWeights)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hgap_meas : ∀ n, AEStronglyMeasurable (gap n) μ)
    (hgap_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ gap n ω)
    (_hs : ∀ n, NullMeasurableSet (s n) μ)
    (hs_mass : ∀ n, ENNReal.ofReal δ ≤ μ (s n))
    (hs_gap : ∀ n, ∀ᵐ ω ∂μ, ω ∈ s n → ε ≤ gap n ω)
    (hlim : TendstoAE μ (W.apply gap) (fun _ => 0)) :
    False := by
  let cap : ℕ → Ω → ℝ := fun n ω => min (gap n ω) ε
  let capEN : ℕ → Ω → ℝ≥0∞ :=
    fun n ω => ENNReal.ofReal (cap n ω)
  have hcap_meas : ∀ n, AEMeasurable (capEN n) μ := by
    intro n
    have hmin : AEMeasurable (cap n) μ :=
      (hgap_meas n).aemeasurable.min measurable_const.aemeasurable
    exact ENNReal.measurable_ofReal.comp_aemeasurable hmin
  have hcap_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ cap n ω := by
    intro n
    filter_upwards [hgap_nonneg n] with ω hω
    exact le_min hω hε.le
  have hcap_integral_lower : ∀ n,
      ENNReal.ofReal (ε * δ) ≤ ∫⁻ ω, capEN n ω ∂μ := by
    intro n
    have hset_lower : ENNReal.ofReal ε * μ (s n) ≤
        ∫⁻ ω in s n, capEN n ω ∂μ := by
      calc
        ENNReal.ofReal ε * μ (s n) =
            ∫⁻ _ω in s n, ENNReal.ofReal ε ∂μ := by
              rw [setLIntegral_const]
        _ ≤ ∫⁻ ω in s n, capEN n ω ∂μ := by
          apply setLIntegral_mono_ae (hcap_meas n).restrict
          filter_upwards [hs_gap n] with ω hω hωs
          simp only [capEN, cap]
          rw [min_eq_right (hω hωs)]
    have hset_to_all :
        (∫⁻ ω in s n, capEN n ω ∂μ) ≤ ∫⁻ ω, capEN n ω ∂μ :=
      setLIntegral_le_lintegral _ _
    have hεδ : ENNReal.ofReal (ε * δ) ≤ ENNReal.ofReal ε * μ (s n) := by
      rw [ENNReal.ofReal_mul hε.le]
      gcongr
      exact hs_mass n
    exact hεδ.trans (hset_lower.trans hset_to_all)
  have hconvex_cap_lower : ∀ n,
      ENNReal.ofReal (ε * δ) ≤
        ∫⁻ ω, ENNReal.ofReal (W.apply (fun i x => cap i x) n ω) ∂μ := by
    intro n
    have hcap_nonneg_all : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ cap i ω :=
      ae_all_iff.mpr hcap_nonneg
    have hsum_eq : ∀ᵐ ω ∂μ,
        ENNReal.ofReal (W.apply (fun i x => cap i x) n ω) =
          ∑ i ∈ W.support n,
            ENNReal.ofReal (W.weight n i) * capEN i ω := by
      filter_upwards [hcap_nonneg_all] with ω hω
      simp only [ForwardConvexWeights.apply, capEN]
      rw [ENNReal.ofReal_sum_of_nonneg]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [ENNReal.ofReal_mul (W.nonneg n i hi)]
      · intro i hi
        exact mul_nonneg (W.nonneg n i hi) (hω i)
    have hsum_integral :
        (∫⁻ ω, ENNReal.ofReal (W.apply (fun i x => cap i x) n ω) ∂μ) =
          ∑ i ∈ W.support n,
            ENNReal.ofReal (W.weight n i) * (∫⁻ ω, capEN i ω ∂μ) := by
      calc
        (∫⁻ ω, ENNReal.ofReal (W.apply (fun i x => cap i x) n ω) ∂μ) =
            ∫⁻ ω, ∑ i ∈ W.support n,
              ENNReal.ofReal (W.weight n i) * capEN i ω ∂μ :=
          lintegral_congr_ae hsum_eq
        _ = ∑ i ∈ W.support n,
            ∫⁻ ω, ENNReal.ofReal (W.weight n i) * capEN i ω ∂μ := by
          rw [lintegral_finsetSum']
          intro i hi
          exact (hcap_meas i).const_mul (ENNReal.ofReal (W.weight n i))
        _ = ∑ i ∈ W.support n,
            ENNReal.ofReal (W.weight n i) * (∫⁻ ω, capEN i ω ∂μ) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [lintegral_const_mul'' _ (hcap_meas i)]
    rw [hsum_integral]
    calc
      ENNReal.ofReal (ε * δ) =
          ∑ i ∈ W.support n,
            ENNReal.ofReal (W.weight n i) * ENNReal.ofReal (ε * δ) := by
              rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg]
              · simp [W.sum_eq_one]
              · intro i hi
                exact W.nonneg n i hi
      _ ≤ ∑ i ∈ W.support n,
            ENNReal.ofReal (W.weight n i) * (∫⁻ ω, capEN i ω ∂μ) := by
              apply Finset.sum_le_sum
              intro i hi
              gcongr
              exact hcap_integral_lower i
  have hcap_apply_le : ∀ n, ∀ᵐ ω ∂μ,
      ENNReal.ofReal (W.apply (fun i x => cap i x) n ω) ≤
        ENNReal.ofReal (min (W.apply gap n ω) ε) := by
    intro n
    have hnonneg_all : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ gap i ω :=
      ae_all_iff.mpr hgap_nonneg
    filter_upwards [hnonneg_all] with ω hω
    exact ENNReal.ofReal_mono
      (W.apply_min_le_min_apply n ω)
  have hlim_cap : ∀ᵐ ω ∂μ, Tendsto
      (fun n => ENNReal.ofReal (min (W.apply gap n ω) ε)) atTop (𝓝 0) := by
    filter_upwards [hlim] with ω hω
    have hmin : Tendsto
        (fun n => min (W.apply gap n ω) ε) atTop (𝓝 (min (0 : ℝ) ε)) :=
      hω.min tendsto_const_nhds
    have hzero : min (0 : ℝ) ε = 0 := min_eq_left hε.le
    change Tendsto (ENNReal.ofReal ∘ fun n => min (W.apply gap n ω) ε)
      atTop (𝓝 0)
    simpa only [hzero, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto (min (0 : ℝ) ε)).comp hmin
  have hlim_integral : Tendsto
      (fun n => ∫⁻ ω, ENNReal.ofReal (min (W.apply gap n ω) ε) ∂μ)
      atTop (𝓝 0) := by
    have h := tendsto_lintegral_of_dominated_convergence'
      (fun _ω => ENNReal.ofReal ε)
      (fun n => by
        have happly : AEMeasurable (W.apply gap n) μ :=
          (W.apply_aestronglyMeasurable hgap_meas n).aemeasurable
        exact ENNReal.measurable_ofReal.comp_aemeasurable
          (happly.min measurable_const.aemeasurable))
      (fun n => by
        filter_upwards [] with ω
        exact ENNReal.ofReal_mono (min_le_right _ _))
      (by
        rw [lintegral_const]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ Set.univ))
      hlim_cap
    simpa only [lintegral_zero] using h
  have hlower_apply : ∀ n,
      ENNReal.ofReal (ε * δ) ≤
        ∫⁻ ω, ENNReal.ofReal (min (W.apply gap n ω) ε) ∂μ := by
    intro n
    exact (hconvex_cap_lower n).trans
      (lintegral_mono_ae (hcap_apply_le n))
  have hεδ_pos : 0 < ENNReal.ofReal (ε * δ) :=
    ENNReal.ofReal_pos.mpr (mul_pos hε hδ)
  have hbad : ENNReal.ofReal (ε * δ) ≤ 0 :=
    ge_of_tendsto' hlim_integral (fun n => hlower_apply n)
  exact (not_le_of_gt hεδ_pos) hbad

namespace GainProcessModel

noncomputable section

open Classical in
theorem piecewise_tendstoAE_of_tendstoAE
    {μ : Measure Ω} {s : ℕ → Set Ω} {f g : ℕ → Ω → ℝ} {h : Ω → ℝ}
    (hf : TendstoAE μ f h) (hg : TendstoAE μ g h) :
    TendstoAE μ
      (fun n => (s n).piecewise (g n) (f n)) h := by
  classical
  filter_upwards [hf, hg] with ω hfw hgw
  rw [Metric.tendsto_nhds] at hfw hgw ⊢
  intro ε hε
  filter_upwards [hfw (ε / 2) (half_pos hε), hgw (ε / 2) (half_pos hε)]
    with n hfn hgn
  have hhalf : ε / 2 < ε := by linarith
  by_cases hn : ω ∈ s n
  · simp only [Set.piecewise, ite_eq_left hn]
    exact hgn.trans hhalf
  · simp only [Set.piecewise, ite_eq_right hn]
    exact hfn.trans hhalf

end
end GainProcessModel

/-! ### The abstract terminal-gain consumer -/

/--
If a sequence of claims in `K₁` has a persistent uniformly positive gap over a
base sequence converging a.e. to an a.e.-maximal point of the in-measure
sequential closure of `K₁`, then the forward-convex candidate for the improved
sequence yields a contradiction.

The forward-convex weights are selected internally from
`TerminalGainHasAEForwardConvexCandidate`.  In particular, membership of the
candidate limit in the sequential closure is proved here from convex
stability of `K₁`; it is not an additional assumption on the limit.
-/
theorem not_persistent_terminalGain_improvement_of_forwardConvexCandidate
    {Time : Type*} {A : GainProcessModel Ω Time}
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {h : Ω → ℝ} {f g : ℕ → Ω → ℝ} {s : ℕ → Set Ω}
    {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ)
    (hK1_meas :
      ∀ q, q ∈ A.K1OfGainProcessModel μ → AEStronglyMeasurable q μ)
    (hCandidate :
      TerminalGainHasAEForwardConvexCandidate μ
        (A.K1OfGainProcessModel μ))
    (hgK1 : ∀ n, g n ∈ A.K1OfGainProcessModel μ)
    (hmax :
      AEMaximalIn μ
        (InMeasureSequentialClosure μ (A.K1OfGainProcessModel μ)) h)
    (hf : TendstoAE μ f h)
    (hdom : ∀ n, AEDominatedBy μ (f n) (g n))
    (hgap_meas : ∀ n,
      AEStronglyMeasurable (fun ω => g n ω - f n ω) μ)
    (hgap_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ g n ω - f n ω)
    (hs : ∀ n, NullMeasurableSet (s n) μ)
    (hs_mass : ∀ n, ENNReal.ofReal δ ≤ μ (s n))
    (hs_gap : ∀ n, ∀ᵐ ω ∂μ, ω ∈ s n → ε ≤ g n ω - f n ω) :
    False := by
  rcases hCandidate g hgK1 with ⟨W, g_lim, hglim⟩
  have hK1_mem : ∀ n, W.apply g n ∈ A.K1OfGainProcessModel μ := by
    intro n
    exact A.K1_apply_forwardConvexWeights_mem μ W hgK1 n
  have hK1_apply_meas : ∀ n,
      AEStronglyMeasurable (W.apply g n) μ := by
    intro n
    apply W.apply_aestronglyMeasurable
    intro i
    exact hK1_meas (g i) (hgK1 i)
  have hglim_in_measure :
      MeasureTheory.TendstoInMeasure μ (W.apply g) atTop g_lim :=
    tendstoInMeasure_of_tendstoAE (μ := μ) hK1_apply_meas hglim
  have hglim_mem :
      g_lim ∈ InMeasureSequentialClosure μ
        (A.K1OfGainProcessModel μ) := by
    exact ⟨W.apply g, hK1_mem, hglim_in_measure⟩
  have hWf_lim : TendstoAE μ (W.apply f) h :=
    W.preservesTendstoAE μ hf
  have hWdom : ∀ n,
      AEDominatedBy μ (W.apply f n) (W.apply g n) := by
    intro n
    exact W.apply_dominated hdom n
  have hlim_dom : AEDominatedBy μ h g_lim :=
    AEDominatedBy.limit hWf_lim hglim hWdom
  have hlim_eq : g_lim =ᵐ[μ] h :=
    hmax.2 g_lim hglim_mem hlim_dom
  have hWgap_lim :
      TendstoAE μ
        (W.apply (fun n ω => g n ω - f n ω)) (fun _ => 0) := by
    have hWgap_lim' :
        TendstoAE μ
          (fun n ω => W.apply g n ω - W.apply f n ω)
          (fun ω => g_lim ω - h ω) := by
      filter_upwards [hglim, hWf_lim] with ω hgω hfω
      exact hgω.sub hfω
    rw [W.apply_sub g f]
    filter_upwards [hWgap_lim', hlim_eq] with ω hω heq
    simpa [heq] using hω
  exact not_tendstoAE_zero_forwardConvex_apply_of_gap_mass
    W hε hδ hgap_meas hgap_nonneg hs hs_mass hs_gap hWgap_lim

/-- A persistent positive improvement contradicts maximality even when the
unmodified base is dominated only up to an almost-everywhere vanishing lower
error.  The exact dominated base required by the existing consumer is
constructed internally. -/
theorem not_persistent_terminalGain_improvement_of_vanishing_lowerError
    {Time : Type*} {A : GainProcessModel Ω Time}
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {h : Ω → ℝ} {b g : ℕ → Ω → ℝ} {s : ℕ → Set Ω}
    {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ)
    (hK1_meas :
      ∀ q, q ∈ A.K1OfGainProcessModel μ → AEStronglyMeasurable q μ)
    (hCandidate :
      TerminalGainHasAEForwardConvexCandidate μ
        (A.K1OfGainProcessModel μ))
    (hgK1 : ∀ n, g n ∈ A.K1OfGainProcessModel μ)
    (hmax :
      AEMaximalIn μ
        (InMeasureSequentialClosure μ (A.K1OfGainProcessModel μ)) h)
    (hb_meas : ∀ n, AEStronglyMeasurable (b n) μ)
    (hb : TendstoAE μ b h)
    (hLowerError :
      TendstoAE μ
        (fun n ω => max (b n ω - g n ω) 0) (fun _ => 0))
    (hs : ∀ n, NullMeasurableSet (s n) μ)
    (hs_mass : ∀ n, ENNReal.ofReal δ ≤ μ (s n))
    (hs_gap : ∀ n, ∀ᵐ ω ∂μ, ω ∈ s n → ε ≤ g n ω - b n ω) :
    False := by
  let correction : ℕ → Ω → ℝ := fun n ω => max (b n ω - g n ω) 0
  let f : ℕ → Ω → ℝ := fun n ω => b n ω - correction n ω
  have hCorrectionMeas : ∀ n,
      AEStronglyMeasurable (correction n) μ := by
    intro n
    apply AEMeasurable.aestronglyMeasurable
    exact ((hb_meas n).sub (hK1_meas (g n) (hgK1 n))).aemeasurable.max
      aemeasurable_const
  have hf : TendstoAE μ f h := by
    filter_upwards [hb, hLowerError] with ω hbω hErrorω
    simpa only [f, correction, sub_zero] using hbω.sub hErrorω
  have hdom : ∀ n, AEDominatedBy μ (f n) (g n) := by
    intro n
    apply Filter.Eventually.of_forall
    intro ω
    dsimp only [f, correction]
    have hMax : b n ω - g n ω ≤ max (b n ω - g n ω) 0 :=
      le_max_left _ _
    linarith
  have hgap_meas : ∀ n,
      AEStronglyMeasurable (fun ω => g n ω - f n ω) μ := by
    intro n
    exact (hK1_meas (g n) (hgK1 n)).sub
      ((hb_meas n).sub (hCorrectionMeas n))
  have hgap_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ g n ω - f n ω := by
    intro n
    apply Filter.Eventually.of_forall
    intro ω
    dsimp only [f, correction]
    have hMax : b n ω - g n ω ≤ max (b n ω - g n ω) 0 :=
      le_max_left _ _
    linarith
  have hs_gap' : ∀ n, ∀ᵐ ω ∂μ, ω ∈ s n → ε ≤ g n ω - f n ω := by
    intro n
    filter_upwards [hs_gap n] with ω hGap hω
    dsimp only [f, correction]
    have hCorrection : 0 ≤ max (b n ω - g n ω) 0 := le_max_right _ _
    linarith [hGap hω]
  exact not_persistent_terminalGain_improvement_of_forwardConvexCandidate
    hε hδ hK1_meas hCandidate hgK1 hmax hf hdom hgap_meas
      hgap_nonneg hs hs_mass hs_gap'

end FTAPTheorem42
