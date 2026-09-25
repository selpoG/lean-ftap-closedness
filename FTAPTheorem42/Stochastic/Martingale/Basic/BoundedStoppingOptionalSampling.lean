/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Stopping.StoppingTimeRightApproximation
import FTAPTheorem42.Foundations.RightContinuousProgressive
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import FTAPTheorem42.Stochastic.Martingale.Basic.DoobL2Maximal

/-!
# Optional sampling at bounded finite stopping times

The countable-range optional-sampling theorem is passed to an arbitrary
bounded finite stopping time by rounding that time from the right.  The
rounded stopped values are conditional expectations of one deterministic
terminal value, hence uniformly integrable.  Vitali convergence replaces a
pathwise dominating envelope.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped MeasureTheory NNReal

variable {Ω : Type*} [m0 : MeasurableSpace Ω]

/-- Conditional expectation commutes with an almost-everywhere limit of a
uniformly integrable sequence.  This is the `L¹` replacement for a dominated
convergence argument with a pathwise envelope. -/
theorem condExp_ae_eq_of_uniformIntegrable_tendsto
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m0)
    [SigmaFinite (μ.trim (m := m) hm)]
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hfUI : UniformIntegrable f 1 μ)
    (hfg : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (c : Ω → ℝ) (_hcMeas : AEStronglyMeasurable[m] c μ)
    (hcond : ∀ n, μ[f n | m] =ᵐ[μ] c) :
    μ[g | m] =ᵐ[μ] c := by
  have hcInt : Integrable c μ := integrable_condExp.congr (hcond 0)
  have hgInt : Integrable g μ := hfUI.integrable_of_ae_tendsto hfg
  have hLp : Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
      hfUI.aestronglyMeasurable (memLp_one_iff_integrable.2 hgInt) hfUI.unifIntegrable hfg
  have hbound : ∀ n, eLpNorm (μ[g | m] - c) 1 μ ≤
      eLpNorm (f n - g) 1 μ := by
    intro n
    have hfnInt : Integrable (f n) μ :=
      (hfUI.memLp n).integrable le_rfl
    have hdiff : (μ[g | m] - c) =ᵐ[μ] μ[g - f n | m] := by
      filter_upwards [(condExp_sub hgInt hfnInt m), hcond n]
        with ω hsub hc
      change μ[g | m] ω - c ω = μ[g - f n | m] ω
      rw [← hc]
      exact hsub.symm
    rw [eLpNorm_congr_ae hdiff]
    calc
      eLpNorm μ[g - f n | m] 1 μ ≤ eLpNorm (g - f n) 1 μ :=
        eLpNorm_condExp_le_eLpNorm (g - f n) le_rfl
      _ = eLpNorm (f n - g) 1 μ := eLpNorm_sub_comm _ _ _ _
  have hzero : eLpNorm (μ[g | m] - c) 1 μ = 0 := by
    apply le_antisymm
    · exact ge_of_tendsto' hLp hbound
    · exact bot_le
  have hzeroAE : (μ[g | m] - c) =ᵐ[μ] 0 :=
    (eLpNorm_eq_zero_iff one_ne_zero).1 hzero
  filter_upwards [hzeroAE] with ω hω
  simpa only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] using hω

/-- Right-grid approximations of a bounded stopping time sample a uniformly
integrable family from a martingale.  Each approximation is the conditional
expectation of the same deterministic terminal value. -/
theorem Martingale.uniformIntegrable_sample_rightApproximation
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 m0} [SigmaFiniteFiltration μ ℱ]
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ μ)
    {τ : Ω → ℝ≥0} {T : ℝ≥0}
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτT : ∀ ω, τ ω ≤ T) :
    UniformIntegrable (fun r ω =>
      M (StoppingTimeRightApproximation.approx r τ ω) ω) 1 μ := by
  let ρ : ℕ → Ω → ℝ≥0 := fun r =>
    StoppingTimeRightApproximation.approx r τ
  have hρstop : ∀ r, IsStoppingTime ℱ
      (fun ω => (ρ r ω : WithTop ℝ≥0)) := fun r =>
    StoppingTimeRightApproximation.isStoppingTime hτ r
  have hρ_countable : ∀ r,
      (Set.range fun ω => (ρ r ω : WithTop ℝ≥0)).Countable := by
    intro r
    apply Set.Countable.mono ?_
      ((StoppingTimeRightApproximation.countable_range r τ).image
        (fun t : ℝ≥0 => (t : WithTop ℝ≥0)))
    rintro _ ⟨ω, rfl⟩
    exact ⟨StoppingTimeRightApproximation.approx r τ ω,
      ⟨ω, rfl⟩, by rfl⟩
  have hρT : ∀ r ω, ρ r ω ≤ T + 1 := fun r ω =>
    StoppingTimeRightApproximation.approx_le_add_one_of_le hτT r ω
  have hρTerminal : ∀ r, (fun ω => M (ρ r ω) ω) =ᵐ[μ]
      μ[M (T + 1) | (hρstop r).measurableSpace] := by
    intro r
    have hstoppedEq : MeasureTheory.stoppedValue M
        (fun ω => (ρ r ω : WithTop ℝ≥0)) = fun ω => M (ρ r ω) ω := by
      funext ω
      rw [MeasureTheory.stoppedValue,
        WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
    rw [← hstoppedEq]
    exact hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
      (hρstop r) (fun ω => WithTop.coe_le_coe.mpr (hρT r ω))
      (hρ_countable r)
  have hcondUI := (hM.integrable (T + 1)).uniformIntegrable_condExp
    (fun r => (hρstop r).measurableSpace_le_of_le
      (fun ω => WithTop.coe_le_coe.mpr (hρT r ω)))
  exact hcondUI.ae_eq fun r => (hρTerminal r).symm

/-- A right-continuous martingale sampled at a bounded finite stopping time
is integrable. -/
theorem Martingale.integrable_sample_of_boundedStoppingTime
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 m0} [SigmaFiniteFiltration μ ℱ]
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ μ)
    {τ : Ω → ℝ≥0} {T : ℝ≥0}
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτT : ∀ ω, τ ω ≤ T)
    (hMRight : ∀ ω t, ContinuousWithinAt (M · ω) (Set.Ici t) t) :
    Integrable (fun ω => M (τ ω) ω) μ := by
  have hUI := Martingale.uniformIntegrable_sample_rightApproximation
    hM hτ hτT
  exact UniformIntegrable.integrable_of_ae_tendsto (u := atTop) hUI
    (Filter.Eventually.of_forall fun ω =>
      StoppingTimeRightApproximation.tendsto_sample M hMRight τ ω)

/-- Optional sampling from a deterministic terminal time to an arbitrary
bounded finite stopping time.  Countable-range right approximations supply
the discrete optional-sampling identities; uniform integrability passes to
the right-continuous limit. -/
theorem Martingale.sample_ae_eq_condExp_terminal_of_boundedStoppingTime
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 m0} [SigmaFiniteFiltration μ ℱ]
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ μ)
    {τ : Ω → ℝ≥0} {T : ℝ≥0}
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτT : ∀ ω, τ ω ≤ T)
    (hMRight : ∀ ω t,
      ContinuousWithinAt (M · ω) (Set.Ici t) t) :
    (fun ω => M (τ ω) ω) =ᵐ[μ]
      μ[M (T + 1) | hτ.measurableSpace] := by
  let ρ : ℕ → Ω → ℝ≥0 := fun r =>
    StoppingTimeRightApproximation.approx r τ
  have hρstop : ∀ r, IsStoppingTime ℱ
      (fun ω => (ρ r ω : WithTop ℝ≥0)) := fun r =>
    StoppingTimeRightApproximation.isStoppingTime hτ r
  have hρCountable : ∀ r,
      (Set.range fun ω => (ρ r ω : WithTop ℝ≥0)).Countable := by
    intro r
    apply Set.Countable.mono ?_
      ((StoppingTimeRightApproximation.countable_range r τ).image
        (fun t : ℝ≥0 => (t : WithTop ℝ≥0)))
    rintro _ ⟨ω, rfl⟩
    exact ⟨ρ r ω, ⟨ω, rfl⟩, rfl⟩
  have hρT : ∀ r ω, ρ r ω ≤ T + 1 := fun r ω =>
    StoppingTimeRightApproximation.approx_le_add_one_of_le hτT r ω
  have hρTerminal : ∀ r, (fun ω => M (ρ r ω) ω) =ᵐ[μ]
      μ[M (T + 1) | (hρstop r).measurableSpace] := by
    intro r
    have hstoppedEq : MeasureTheory.stoppedValue M
        (fun ω => (ρ r ω : WithTop ℝ≥0)) =
          fun ω => M (ρ r ω) ω := by
      funext ω
      rw [MeasureTheory.stoppedValue,
        WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
    rw [← hstoppedEq]
    exact hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
      (hρstop r) (fun ω => WithTop.coe_le_coe.mpr (hρT r ω))
      (hρCountable r)
  have hτρ : ∀ r,
      (fun ω => (τ ω : WithTop ℝ≥0)) ≤
        fun ω => (ρ r ω : WithTop ℝ≥0) := fun r ω =>
    WithTop.coe_le_coe.mpr
      (StoppingTimeRightApproximation.le_approx r τ ω)
  have hcond : ∀ r,
      μ[(fun ω => M (ρ r ω) ω) | hτ.measurableSpace] =ᵐ[μ]
        μ[M (T + 1) | hτ.measurableSpace] := by
    intro r
    calc
      μ[(fun ω => M (ρ r ω) ω) | hτ.measurableSpace] =ᵐ[μ]
          μ[μ[M (T + 1) | (hρstop r).measurableSpace] |
            hτ.measurableSpace] := condExp_congr_ae (hρTerminal r)
      _ =ᵐ[μ] μ[M (T + 1) | hτ.measurableSpace] :=
        condExp_condExp_of_le
          (hτ.measurableSpace_mono (hρstop r) (hτρ r))
          ((hρstop r).measurableSpace_le_of_le
            (fun ω => WithTop.coe_le_coe.mpr (hρT r ω)))
  have hρUI : UniformIntegrable
      (fun r ω => M (ρ r ω) ω) 1 μ :=
    Martingale.uniformIntegrable_sample_rightApproximation hM hτ hτT
  have hρTend : ∀ᵐ ω ∂μ,
      Tendsto (fun r => M (ρ r ω) ω) atTop (𝓝 (M (τ ω) ω)) :=
    Filter.Eventually.of_forall fun ω =>
      StoppingTimeRightApproximation.tendsto_sample M hMRight τ ω
  have hterminalMeas : AEStronglyMeasurable[hτ.measurableSpace]
      μ[M (T + 1) | hτ.measurableSpace] μ :=
    stronglyMeasurable_condExp.aestronglyMeasurable
  have hlimit := condExp_ae_eq_of_uniformIntegrable_tendsto
    hτ.measurableSpace_le
    (fun r ω => M (ρ r ω) ω) (fun ω => M (τ ω) ω)
    hρUI hρTend μ[M (T + 1) | hτ.measurableSpace]
    hterminalMeas hcond
  have hsampleInt : Integrable (fun ω => M (τ ω) ω) μ :=
    Martingale.integrable_sample_of_boundedStoppingTime
      hM hτ hτT hMRight
  have hprogressive : IsStronglyProgressive ℱ M :=
    FTAPTheorem42.StronglyAdapted.isStronglyProgressive_of_rightContinuous
      hM.stronglyAdapted hMRight
  have hsampleMeas : StronglyMeasurable[hτ.measurableSpace]
      (fun ω => M (τ ω) ω) := by
    have hstoppedEq : MeasureTheory.stoppedValue M
        (fun ω => (τ ω : WithTop ℝ≥0)) =
          fun ω => M (τ ω) ω := by
      funext ω
      rw [MeasureTheory.stoppedValue,
        WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
    rw [← hstoppedEq]
    exact (MeasureTheory.measurable_stoppedValue hprogressive hτ).stronglyMeasurable
  have hself : μ[(fun ω => M (τ ω) ω) | hτ.measurableSpace] =
      fun ω => M (τ ω) ω :=
    condExp_of_stronglyMeasurable hτ.measurableSpace_le
      hsampleMeas hsampleInt
  rw [hself] at hlimit
  exact hlimit

/-- Optional sampling between arbitrary bounded finite stopping times. -/
theorem Martingale.condExp_sampled_ae_eq_of_boundedStoppingTimes
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 m0} [SigmaFiniteFiltration μ ℱ]
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ μ)
    {σ τ : Ω → ℝ≥0} {T : ℝ≥0}
    (hσ : IsStoppingTime ℱ (fun ω => (σ ω : WithTop ℝ≥0)))
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (hστ : ∀ ω, σ ω ≤ τ ω) (hτT : ∀ ω, τ ω ≤ T)
    (hMRight : ∀ ω t,
      ContinuousWithinAt (M · ω) (Set.Ici t) t) :
    μ[(fun ω => M (τ ω) ω) | hσ.measurableSpace] =ᵐ[μ]
      fun ω => M (σ ω) ω := by
  have hσT : ∀ ω, σ ω ≤ T := fun ω => (hστ ω).trans (hτT ω)
  have hτTerminal :=
    Martingale.sample_ae_eq_condExp_terminal_of_boundedStoppingTime
      hM hτ hτT hMRight
  have hσTerminal :=
    Martingale.sample_ae_eq_condExp_terminal_of_boundedStoppingTime
      hM hσ hσT hMRight
  calc
    μ[(fun ω => M (τ ω) ω) | hσ.measurableSpace] =ᵐ[μ]
        μ[μ[M (T + 1) | hτ.measurableSpace] |
          hσ.measurableSpace] := condExp_congr_ae hτTerminal
    _ =ᵐ[μ] μ[M (T + 1) | hσ.measurableSpace] :=
      condExp_condExp_of_le
        (hσ.measurableSpace_mono hτ fun ω =>
          WithTop.coe_le_coe.mpr (hστ ω))
        hτ.measurableSpace_le
    _ =ᵐ[μ] fun ω => M (σ ω) ω := hσTerminal.symm

/-- Optional sampling from a countable-range stopping time `σ` to an
arbitrary bounded finite stopping time `τ`.  Right continuity identifies the
limit of the countable-range right approximations of `τ`. -/
theorem Martingale.condExp_sampled_ae_eq_of_countableRange_lower
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [SigmaFiniteFiltration μ ℱ]
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ μ)
    {σ τ : Ω → ℝ≥0} {T : ℝ≥0}
    (hσ : IsStoppingTime ℱ (fun ω => (σ ω : WithTop ℝ≥0)))
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    (hσ_countable : (Set.range fun ω => (σ ω : WithTop ℝ≥0)).Countable)
    (hστ : ∀ ω, σ ω ≤ τ ω) (hτT : ∀ ω, τ ω ≤ T)
    (hMRight : ∀ ω t, ContinuousWithinAt (M · ω) (Set.Ici t) t) :
    μ[(fun ω => M (τ ω) ω) | hσ.measurableSpace] =ᵐ[μ]
      fun ω => M (σ ω) ω := by
  let ρ : ℕ → Ω → ℝ≥0 := fun r =>
    StoppingTimeRightApproximation.approx r τ
  have hρstop : ∀ r, IsStoppingTime ℱ
      (fun ω => (ρ r ω : WithTop ℝ≥0)) := fun r =>
    StoppingTimeRightApproximation.isStoppingTime hτ r
  have hρ_countable : ∀ r,
      (Set.range fun ω => (ρ r ω : WithTop ℝ≥0)).Countable := by
    intro r
    apply Set.Countable.mono ?_
      ((StoppingTimeRightApproximation.countable_range r τ).image
        (fun t : ℝ≥0 => (t : WithTop ℝ≥0)))
    rintro _ ⟨ω, rfl⟩
    exact ⟨StoppingTimeRightApproximation.approx r τ ω,
      ⟨ω, rfl⟩, by rfl⟩
  have hρT : ∀ r ω, ρ r ω ≤ T + 1 := fun r ω =>
    StoppingTimeRightApproximation.approx_le_add_one_of_le hτT r ω
  have hρUI : UniformIntegrable
      (fun r ω => M (ρ r ω) ω) 1 μ :=
    Martingale.uniformIntegrable_sample_rightApproximation hM hτ hτT
  have hcond : ∀ r,
      μ[(fun ω => M (ρ r ω) ω) | hσ.measurableSpace] =ᵐ[μ]
        fun ω => M (σ ω) ω := by
    intro r
    have hσρ : (fun ω => (σ ω : WithTop ℝ≥0)) ≤
        fun ω => (ρ r ω : WithTop ℝ≥0) := fun ω =>
      WithTop.coe_le_coe.mpr
        ((hστ ω).trans (StoppingTimeRightApproximation.le_approx r τ ω))
    have hopt :=
      hM.stoppedValue_ae_eq_condExp_of_le_of_countable_range
        (hρstop r) hσ hσρ
        (fun ω => WithTop.coe_le_coe.mpr (hρT r ω))
        (hρ_countable r) hσ_countable
    have hρEq : MeasureTheory.stoppedValue M
        (fun ω => (ρ r ω : WithTop ℝ≥0)) = fun ω => M (ρ r ω) ω := by
      funext ω
      rw [MeasureTheory.stoppedValue,
        WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
    have hσEq : MeasureTheory.stoppedValue M
        (fun ω => (σ ω : WithTop ℝ≥0)) = fun ω => M (σ ω) ω := by
      funext ω
      rw [MeasureTheory.stoppedValue,
        WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
    rw [hρEq, hσEq] at hopt
    exact hopt.symm
  have hMσMeas : AEStronglyMeasurable[hσ.measurableSpace]
      (fun ω => M (σ ω) ω) μ :=
    stronglyMeasurable_condExp.aestronglyMeasurable.congr (hcond 0)
  have hρTend : ∀ᵐ ω ∂μ,
      Tendsto (fun r => M (ρ r ω) ω) atTop (𝓝 (M (τ ω) ω)) :=
    Filter.Eventually.of_forall fun ω =>
      StoppingTimeRightApproximation.tendsto_sample M hMRight τ ω
  exact condExp_ae_eq_of_uniformIntegrable_tendsto
    hσ.measurableSpace_le
    (fun r ω => M (ρ r ω) ω) (fun ω => M (τ ω) ω)
    hρUI hρTend (fun ω => M (σ ω) ω) hMσMeas hcond

end FTAPTheorem42

namespace FTAPTheorem42

/-!
## Centered L2 contraction between bounded stopping times

Optional sampling identifies the value of a martingale at an earlier
bounded stopping time with the conditional expectation of its value at a
later one.  Centering at time zero commutes with this identity.  Consequently
the sampled centered martingale contracts in `L2`.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

omit [IsProbabilityMeasure mu] in
/-- A true martingale remains a true martingale after subtracting its
time-zero value at every time. -/
theorem Martingale.centered
    {M : Process Omega} (hM : Martingale M F mu) :
    Martingale (fun t omega => M t omega - M 0 omega) F mu := by
  have hInitial : Martingale (fun _ => M 0) F mu :=
    martingale_const_fun F mu (hM.stronglyAdapted 0) (hM.integrable 0)
  exact hM.sub hInitial

/-- Sampling a centered right-continuous martingale at an earlier bounded
stopping time contracts its `L2` norm. -/
theorem Martingale.centered_sample_memLp_two_and_eLpNorm_le
    {M : Process Omega} (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    {sigma tau : Omega -> NNReal} {T : NNReal}
    (hSigma : IsStoppingTime F (fun omega => (sigma omega : WithTop NNReal)))
    (hTau : IsStoppingTime F (fun omega => (tau omega : WithTop NNReal)))
    (hSigmaTau : forall omega, sigma omega <= tau omega)
    (hTauT : forall omega, tau omega <= T)
    (hTauMem : MemLp
      (fun omega => M (tau omega) omega - M 0 omega)
      (2 : ENNReal) mu) :
    MemLp (fun omega => M (sigma omega) omega - M 0 omega)
        (2 : ENNReal) mu /\
      eLpNorm (fun omega => M (sigma omega) omega - M 0 omega)
          (2 : ENNReal) mu <=
        eLpNorm (fun omega => M (tau omega) omega - M 0 omega)
          (2 : ENNReal) mu := by
  let X : Process Omega := fun t omega => M t omega - M 0 omega
  have hX : Martingale X F mu := by
    simpa only [X] using FTAPTheorem42.Martingale.centered hM
  have hXRight : forall omega t,
      ContinuousWithinAt (X · omega) (Ici t) t := by
    intro omega t
    exact (hMRight omega t).sub continuousWithinAt_const
  have hOptional :=
    FTAPTheorem42.Martingale.condExp_sampled_ae_eq_of_boundedStoppingTimes
      hX hSigma hTau hSigmaTau hTauT hXRight
  have hTauMemX : MemLp (fun omega => X (tau omega) omega)
      (2 : ENNReal) mu := by
    simpa only [X] using hTauMem
  have hCondMem : MemLp
      (mu[(fun omega => X (tau omega) omega) | hSigma.measurableSpace])
      (2 : ENNReal) mu := by
    exact hTauMemX.condExp (by norm_num)
  have hSigmaMem : MemLp (fun omega => X (sigma omega) omega)
      (2 : ENNReal) mu :=
    (memLp_congr_ae hOptional).mp hCondMem
  refine ⟨by simpa only [X] using hSigmaMem, ?_⟩
  calc
    eLpNorm (fun omega => M (sigma omega) omega - M 0 omega)
        (2 : ENNReal) mu =
      eLpNorm
        (mu[(fun omega => X (tau omega) omega) |
          hSigma.measurableSpace])
        (2 : ENNReal) mu := by
          apply eLpNorm_congr_ae
          simpa only [X] using hOptional.symm
    _ <= eLpNorm (fun omega => X (tau omega) omega)
        (2 : ENNReal) mu :=
      eLpNorm_condExp_le_eLpNorm _ (by norm_num)
    _ = eLpNorm (fun omega => M (tau omega) omega - M 0 omega)
        (2 : ENNReal) mu := by rfl

end FTAPTheorem42
