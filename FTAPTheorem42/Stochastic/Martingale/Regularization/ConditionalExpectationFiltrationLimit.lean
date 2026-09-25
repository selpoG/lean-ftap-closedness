/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import Mathlib.Probability.Martingale.Convergence
import FTAPTheorem42.Stochastic.Martingale.Basic.BoundedStoppingOptionalSampling
import FTAPTheorem42.Stochastic.Predictable.PredictableStoppingGraph
import FTAPTheorem42.Stochastic.Stopping.StoppingTimeForetelling

/-!
# Conditional expectations along increasing sigma algebras

Lévy's upward theorem identifies the limit of conditional expectations
along an increasing family with conditioning on the supremum sigma algebra.
This module records the form used at an announced predictable time.
-/

open Filter MeasureTheory Topology
open scoped MeasureTheory NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [m0 : MeasurableSpace Ω]

/-- If versions of `E[f | mₙ]` converge almost everywhere to `z`, then `z`
is a version of `E[f | ⨆ n, mₙ]`. -/
theorem condExp_iSup_ae_eq_of_tendsto
    {μ : Measure Ω} [IsFiniteMeasure μ] (m : ℕ → MeasurableSpace Ω)
    (hm_mono : Monotone m) (hm_le : ∀ n, m n ≤ m0)
    [∀ n, SigmaFinite (μ.trim (hm_le n))]
    (f z : Ω → ℝ) (g : ℕ → Ω → ℝ)
    (hcond : ∀ n, μ[f | m n] =ᵐ[μ] g n)
    (htend : ∀ᵐ ω ∂μ, Tendsto (fun n => g n ω) atTop (𝓝 (z ω))) :
    μ[f | ⨆ n, m n] =ᵐ[μ] z := by
  let ℱm : Filtration ℕ m0 :=
    { seq := m
      mono' := hm_mono
      le' := hm_le }
  have hlevy := MeasureTheory.tendsto_ae_condExp
    (μ := μ) (ℱ := ℱm) f
  have hcondAll : ∀ᵐ ω ∂μ, ∀ n, μ[f | m n] ω = g n ω :=
    ae_all_iff.2 hcond
  filter_upwards [hlevy, hcondAll, htend] with ω hlevyω hcondω htendω
  have hlevyω' : Tendsto (fun n => g n ω) atTop
      (𝓝 (μ[f | ⨆ n, m n] ω)) := by
    exact hlevyω.congr' (Filter.Eventually.of_forall fun n => hcondω n)
  exact tendsto_nhds_unique hlevyω' htendω

/-- Limit identification for stopped values gives conditional mean zero for
their difference from the announced left limit. -/
theorem condExp_sub_iSup_ae_eq_zero_of_tendsto
    {μ : Measure Ω} [IsFiniteMeasure μ] (m : ℕ → MeasurableSpace Ω)
    (hm_mono : Monotone m) (hm_le : ∀ n, m n ≤ m0)
    [∀ n, SigmaFinite (μ.trim (hm_le n))]
    (f z : Ω → ℝ) (g : ℕ → Ω → ℝ)
    (hf : Integrable f μ) (hz : Integrable z μ)
    (hzmeas : StronglyMeasurable[⨆ n, m n] z)
    (hcond : ∀ n, μ[f | m n] =ᵐ[μ] g n)
    (htend : ∀ᵐ ω ∂μ, Tendsto (fun n => g n ω) atTop (𝓝 (z ω))) :
    μ[(fun ω => f ω - z ω) | ⨆ n, m n] =ᵐ[μ] fun _ => 0 := by
  have hmSup : (⨆ n, m n) ≤ m0 := iSup_le hm_le
  let : SigmaFinite (μ.trim hmSup) := by
    infer_instance
  have hfz := condExp_iSup_ae_eq_of_tendsto
    m hm_mono hm_le f z g hcond htend
  have hzcond : μ[z | ⨆ n, m n] =ᵐ[μ] z :=
    Filter.Eventually.of_forall fun ω =>
      congrFun (condExp_of_stronglyMeasurable hmSup hzmeas hz) ω
  change μ[f - z | ⨆ n, m n] =ᵐ[μ] fun _ => 0
  calc
    μ[f - z | ⨆ n, m n] =ᵐ[μ]
        μ[f | ⨆ n, m n] - μ[z | ⨆ n, m n] :=
      condExp_sub hf hz (⨆ n, m n)
    _ =ᵐ[μ] z - z := hfz.sub hzcond
    _ = fun _ => 0 := by funext ω; simp

/-- Announced stopped values converging to the left limit give conditional
mean zero for the martingale left jump on the graph-pullback sigma algebra. -/
theorem condExp_sampledLeftJump_ae_eq_zero_of_announcedValues
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 m0}
    (M : Process Ω) (τ : Ω → ℝ≥0) (σ : ℕ → Ω → ℝ≥0)
    (m : ℕ → MeasurableSpace Ω)
    (hm_mono : Monotone m) (hm_le : ∀ n, m n ≤ m0)
    [∀ n, SigmaFinite (μ.trim (hm_le n))]
    (hmSup : (⨆ n, m n) = predictableGraphMeasurableSpace ℱ τ)
    (hMτ : Integrable (fun ω => M (τ ω) ω) μ)
    (hMleft : Integrable
      (fun ω => Function.leftLim (M · ω) (τ ω)) μ)
    (hMleftMeas : StronglyMeasurable[⨆ n, m n]
      (fun ω => Function.leftLim (M · ω) (τ ω)))
    (hcond : ∀ n,
      μ[(fun ω => M (τ ω) ω) | m n] =ᵐ[μ]
        fun ω => M (σ n ω) ω)
    (htend : ∀ᵐ ω ∂μ, Tendsto (fun n => M (σ n ω) ω) atTop
      (𝓝 (Function.leftLim (M · ω) (τ ω)))) :
    μ[(fun ω => processLeftJump M (τ ω) ω) |
      predictableGraphMeasurableSpace ℱ τ] =ᵐ[μ] fun _ => 0 := by
  have hzero := condExp_sub_iSup_ae_eq_zero_of_tendsto
    m hm_mono hm_le
    (fun ω => M (τ ω) ω)
    (fun ω => Function.leftLim (M · ω) (τ ω))
    (fun n ω => M (σ n ω) ω)
    hMτ hMleft hMleftMeas hcond htend
  rw [hmSup] at hzero
  simpa only [processLeftJump] using hzero

/-- For an increasing announcing sequence, the standard stopped-value
identities imply that the martingale left jump has conditional mean zero on
the predictable graph. -/
theorem condExp_sampledLeftJump_ae_eq_zero_of_announcement
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 m0}
    (M : Process Ω) (τ : Ω → ℝ≥0) (σ : ℕ → Ω → ℝ≥0)
    (hσ : ∀ n, IsStoppingTime ℱ
      (fun ω => (σ n ω : WithTop ℝ≥0)))
    (hσmono : ∀ ω, Monotone fun n => σ n ω)
    (hστ : ∀ n ω, σ n ω < τ ω)
    (hσtend : ∀ ω, Tendsto (fun n => σ n ω) atTop (𝓝 (τ ω)))
    (hMτ : Integrable (fun ω => M (τ ω) ω) μ)
    (hMleft : Integrable
      (fun ω => Function.leftLim (M · ω) (τ ω)) μ)
    (hMleftMeas : StronglyMeasurable[predictableGraphMeasurableSpace ℱ τ]
      (fun ω => Function.leftLim (M · ω) (τ ω)))
    (hcond : ∀ n,
      μ[(fun ω => M (τ ω) ω) | (hσ n).measurableSpace] =ᵐ[μ]
        fun ω => M (σ n ω) ω)
    (htend : ∀ᵐ ω ∂μ, Tendsto (fun n => M (σ n ω) ω) atTop
      (𝓝 (Function.leftLim (M · ω) (τ ω)))) :
    μ[(fun ω => processLeftJump M (τ ω) ω) |
      predictableGraphMeasurableSpace ℱ τ] =ᵐ[μ] fun _ => 0 := by
  let m : ℕ → MeasurableSpace Ω := fun n => (hσ n).measurableSpace
  have hm_mono : Monotone m := by
    intro i j hij
    exact (hσ i).measurableSpace_mono (hσ j) fun ω =>
      WithTop.coe_le_coe.mpr (hσmono ω hij)
  have hmSup : (⨆ n, m n) = predictableGraphMeasurableSpace ℱ τ :=
    (predictableGraphMeasurableSpace_eq_iSup_measurableSpace
      hσ hστ hσtend).symm
  have hMleftMeas' : StronglyMeasurable[⨆ n, m n]
      (fun ω => Function.leftLim (M · ω) (τ ω)) := by
    rw [hmSup]
    exact hMleftMeas
  exact condExp_sampledLeftJump_ae_eq_zero_of_announcedValues
    M τ σ m hm_mono (fun n => (hσ n).measurableSpace_le)
    hmSup hMτ hMleft hMleftMeas' hcond htend

/-- Values of a martingale along an arbitrary bounded announcing sequence
are uniformly integrable.  The countable-range restriction is unnecessary
once optional sampling is available for arbitrary bounded stopping times. -/
theorem Martingale.integrable_sampledLeftLim_of_stoppingTimeAnnouncement
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 m0} [SigmaFiniteFiltration μ ℱ]
    {M : Process Ω} (hM : Martingale M ℱ μ)
    {τ : Ω → ℝ≥0} (a : StoppingTimeAnnouncement ℱ τ)
    (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T)
    (hMRight : ∀ ω t,
      ContinuousWithinAt (M · ω) (Set.Ici t) t)
    (hMLeft : ProcessHasLeftLimits M) :
    Integrable (fun ω => Function.leftLim (M · ω) (τ ω)) μ := by
  have hσT : ∀ n ω, a.time n ω ≤ T := fun n ω =>
    (a.lt n ω).le.trans (hτT ω)
  have hσTerminal : ∀ n, (fun ω => M (a.time n ω) ω) =ᵐ[μ]
      μ[M (T + 1) | (a.isStoppingTime n).measurableSpace] := by
    intro n
    exact Martingale.sample_ae_eq_condExp_terminal_of_boundedStoppingTime
      hM (a.isStoppingTime n) (hσT n) hMRight
  have hUI : UniformIntegrable
      (fun n ω => M (a.time n ω) ω) 1 μ := by
    have hcondUI := (hM.integrable (T + 1)).uniformIntegrable_condExp
      (fun n => (a.isStoppingTime n).measurableSpace_le_of_le
        (fun ω => WithTop.coe_le_coe.mpr (hσT n ω)))
    exact hcondUI.ae_eq fun n => (hσTerminal n).symm
  apply UniformIntegrable.integrable_of_ae_tendsto (u := atTop) hUI
  exact Filter.Eventually.of_forall fun ω =>
    (hMLeft ω (τ ω)).comp (tendsto_nhdsWithin_iff.mpr
      ⟨a.tendsto ω, Filter.Eventually.of_forall fun n => a.lt n ω⟩)

/-- An arbitrary bounded announcing sequence supplies the predictable-graph
conditional mean-zero identity for a martingale left jump. -/
theorem Martingale.condExp_sampledLeftJump_ae_eq_zero_of_stoppingTimeAnnouncement
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 m0} [SigmaFiniteFiltration μ ℱ]
    {M : Process Ω} (hM : Martingale M ℱ μ)
    {τ : Ω → ℝ≥0} (a : StoppingTimeAnnouncement ℱ τ)
    (T : ℝ≥0)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτT : ∀ ω, τ ω ≤ T)
    (hMRight : ∀ ω t,
      ContinuousWithinAt (M · ω) (Set.Ici t) t)
    (hMLeft : ProcessHasLeftLimits M)
    (hMleftMeas : StronglyMeasurable[predictableGraphMeasurableSpace ℱ τ]
      (fun ω => Function.leftLim (M · ω) (τ ω))) :
    μ[(fun ω => processLeftJump M (τ ω) ω) |
      predictableGraphMeasurableSpace ℱ τ] =ᵐ[μ] fun _ => 0 := by
  have hcond : ∀ n,
      μ[(fun ω => M (τ ω) ω) |
          (a.isStoppingTime n).measurableSpace] =ᵐ[μ]
        fun ω => M (a.time n ω) ω := by
    intro n
    exact Martingale.condExp_sampled_ae_eq_of_boundedStoppingTimes
      hM (a.isStoppingTime n) hτ (fun ω => (a.lt n ω).le)
      hτT hMRight
  have hMτ : Integrable (fun ω => M (τ ω) ω) μ :=
    Martingale.integrable_sample_of_boundedStoppingTime
      hM hτ hτT hMRight
  have hMleft : Integrable
      (fun ω => Function.leftLim (M · ω) (τ ω)) μ :=
    Martingale.integrable_sampledLeftLim_of_stoppingTimeAnnouncement
      hM a T hτT hMRight hMLeft
  have htend : ∀ᵐ ω ∂μ,
      Tendsto (fun n => M (a.time n ω) ω) atTop
        (𝓝 (Function.leftLim (M · ω) (τ ω))) :=
    Filter.Eventually.of_forall fun ω =>
      (hMLeft ω (τ ω)).comp (tendsto_nhdsWithin_iff.mpr
        ⟨a.tendsto ω,
          Filter.Eventually.of_forall fun n => a.lt n ω⟩)
  exact FTAPTheorem42.condExp_sampledLeftJump_ae_eq_zero_of_announcement
    M τ a.time a.isStoppingTime a.monotone a.lt a.tendsto
    hMτ hMleft hMleftMeas hcond htend

end FTAPTheorem42
