/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Calculus.SemimartingaleStrategy
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Dominated local martingales

A strongly adapted local martingale dominated at all times by one integrable
random variable is a true martingale.  This is the localization-to-martingale
step used after the first rescaling in Lemma 4.7.
-/

open Filter MeasureTheory Set
open scoped NNReal Topology

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace LocalMartingale

variable {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [SigmaFiniteFiltration μ ℱ]
  {X : Process Ω}

private noncomputable def localizedProcess
    (hX : LocalMartingale X ℱ μ) (n : ℕ) : Process Ω :=
  MeasureTheory.stoppedProcess
    (fun t => {ω | (⊥ : WithTop ℝ≥0) < hX.localSeq n ω}.indicator (X t))
    (hX.localSeq n)

omit [SigmaFiniteFiltration μ ℱ] in
private theorem localizedProcess_martingale
    (hX : LocalMartingale X ℱ μ) (n : ℕ) :
    Martingale (localizedProcess hX n) ℱ μ :=
  hX.stoppedProcess_localSeq n

omit [SigmaFiniteFiltration μ ℱ] in
private theorem localizedProcess_tendsto_ae
    (hX : LocalMartingale X ℱ μ) (t : ℝ≥0) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => localizedProcess hX n t ω)
      atTop (𝓝 (X t ω)) := by
  filter_upwards [hX.isLocalizingSequence_localSeq.tendsto_top] with ω hω
  have heq : ∀ᶠ n in atTop, localizedProcess hX n t ω = X t ω := by
    have hgt : ∀ᶠ n in atTop,
        (t : WithTop ℝ≥0) < hX.localSeq n ω :=
      hω.eventually (Ioi_mem_nhds (WithTop.coe_lt_top t))
    filter_upwards [hgt] with n hn
    rw [localizedProcess, MeasureTheory.stoppedProcess_eq_of_le hn.le]
    have hnMem : ω ∈ {ω | (⊥ : WithTop ℝ≥0) < hX.localSeq n ω} :=
      lt_of_le_of_lt bot_le hn
    exact Set.indicator_of_mem hnMem _
  exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm heq)
    tendsto_const_nhds

omit [SigmaFiniteFiltration μ ℱ] in
private theorem localizedProcess_norm_le_ae
    (hX : LocalMartingale X ℱ μ)
    (Z : Ω → ℝ) (hdom : ∀ᵐ ω ∂μ, ∀ t, |X t ω| ≤ Z ω) :
    ∀ n t, ∀ᵐ ω ∂μ, ‖localizedProcess hX n t ω‖ ≤ Z ω := by
  intro n t
  filter_upwards [hdom] with ω hω
  have hZ : 0 ≤ Z ω := (abs_nonneg (X 0 ω)).trans (hω 0)
  rw [localizedProcess, MeasureTheory.stoppedProcess_indicator_comm]
  by_cases hp : (⊥ : WithTop ℝ≥0) < hX.localSeq n ω
  · have hpMem : ω ∈ {ω | (⊥ : WithTop ℝ≥0) < hX.localSeq n ω} := hp
    rw [Set.indicator_of_mem hpMem, Real.norm_eq_abs]
    exact hω _
  · have hpMem : ω ∉ {ω | (⊥ : WithTop ℝ≥0) < hX.localSeq n ω} := hp
    rw [Set.indicator_of_notMem hpMem, norm_zero]
    exact hZ

/-- An integrably dominated, strongly adapted local martingale is a true
martingale.  Domination holds outside one null set simultaneously for all
times. -/
theorem martingale_of_integrable_bound
    (hX : LocalMartingale X ℱ μ)
    (hAdapted : StronglyAdapted ℱ X)
    (Z : Ω → ℝ) (hZ : Integrable Z μ)
    (hdom : ∀ᵐ ω ∂μ, ∀ t, |X t ω| ≤ Z ω) :
    Martingale X ℱ μ := by
  have hXIntegrable : ∀ t, Integrable (X t) μ := by
    intro t
    apply hZ.mono' hAdapted.stronglyMeasurable.aestronglyMeasurable
    filter_upwards [hdom] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  refine ⟨hAdapted, ?_⟩
  intro i j hij
  apply EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le i)
    (hXIntegrable j)
  · intro s hs hμs
    exact (hXIntegrable i).integrableOn
  · intro s hs hμs
    have hs0 : MeasurableSet s := ℱ.le i s hs
    let F : ℕ → Ω → ℝ := fun n =>
      s.indicator (localizedProcess hX n i)
    let G : ℕ → Ω → ℝ := fun n =>
      s.indicator (localizedProcess hX n j)
    have hFMeas : ∀ n, AEStronglyMeasurable (F n) μ := by
      intro n
      exact ((localizedProcess_martingale hX n).stronglyMeasurable i).mono
        (ℱ.le i) |>.indicator hs0 |>.aestronglyMeasurable
    have hGMeas : ∀ n, AEStronglyMeasurable (G n) μ := by
      intro n
      exact ((localizedProcess_martingale hX n).stronglyMeasurable j).mono
        (ℱ.le j) |>.indicator hs0 |>.aestronglyMeasurable
    have hFBound : ∀ n, ∀ᵐ ω ∂μ, ‖F n ω‖ ≤ Z ω := by
      intro n
      filter_upwards [localizedProcess_norm_le_ae hX Z hdom n i,
        hdom] with ω hloc hω
      by_cases hωs : ω ∈ s
      · simpa [F, Set.indicator_of_mem hωs] using hloc
      · simp [F, Set.indicator_of_notMem hωs,
          (abs_nonneg (X 0 ω)).trans (hω 0)]
    have hGBound : ∀ n, ∀ᵐ ω ∂μ, ‖G n ω‖ ≤ Z ω := by
      intro n
      filter_upwards [localizedProcess_norm_le_ae hX Z hdom n j,
        hdom] with ω hloc hω
      by_cases hωs : ω ∈ s
      · simpa [G, Set.indicator_of_mem hωs] using hloc
      · simp [G, Set.indicator_of_notMem hωs,
          (abs_nonneg (X 0 ω)).trans (hω 0)]
    have hFLim : ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω)
        atTop (𝓝 (s.indicator (X i) ω)) := by
      filter_upwards [localizedProcess_tendsto_ae hX i] with ω hω
      by_cases hωs : ω ∈ s
      · simpa [F, Set.indicator_of_mem hωs] using hω
      · simp [F, Set.indicator_of_notMem hωs]
    have hGLim : ∀ᵐ ω ∂μ, Tendsto (fun n => G n ω)
        atTop (𝓝 (s.indicator (X j) ω)) := by
      filter_upwards [localizedProcess_tendsto_ae hX j] with ω hω
      by_cases hωs : ω ∈ s
      · simpa [G, Set.indicator_of_mem hωs] using hω
      · simp [G, Set.indicator_of_notMem hωs]
    have hFInt := tendsto_integral_of_dominated_convergence Z hFMeas hZ
      hFBound hFLim
    have hGInt := tendsto_integral_of_dominated_convergence Z hGMeas hZ
      hGBound hGLim
    have hEq : ∀ n, (∫ ω, F n ω ∂μ) = ∫ ω, G n ω ∂μ := by
      intro n
      simpa only [F, G, integral_indicator hs0] using
        (localizedProcess_martingale hX n).setIntegral_eq hij hs
    have hLimits := tendsto_nhds_unique hFInt
      (hGInt.congr' (Eventually.of_forall fun n => (hEq n).symm))
    simpa only [integral_indicator hs0] using hLimits
  · exact (hAdapted i).aestronglyMeasurable

end LocalMartingale

namespace SIntegrableStrategy

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- A strategy's local-martingale component is a true martingale as soon as
one integrable random variable dominates it simultaneously at every time. -/
theorem martingalePart_isMartingale_of_integrable_bound
    (H : SIntegrableStrategy D)
    (Z : Ω → ℝ) (hZ : Integrable Z μ)
    (hdom : ∀ᵐ ω ∂μ, ∀ t, |H.martingalePart t ω| ≤ Z ω) :
    Martingale H.martingalePart ℱ μ :=
  LocalMartingale.martingale_of_integrable_bound
    H.martingalePart_isLocalMartingale
    H.martingalePart_isStronglyAdapted Z hZ hdom

end SIntegrableStrategy

end FTAPTheorem42
