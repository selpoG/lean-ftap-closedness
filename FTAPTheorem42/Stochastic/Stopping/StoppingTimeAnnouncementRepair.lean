/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Stopping.StoppingTimeForetelling
import FTAPTheorem42.Foundations.UsualConditions

/-!
# Repairing almost-everywhere stopping-time announcements

Under the usual conditions, every subset of an exceptional null set is
already known at time zero.  This module uses that fact to replace an
almost-everywhere valid countable-range announcing sequence by one satisfying
monotonicity, strictness, and convergence pointwise on the whole sample
space.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal Topology

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace StoppingTimeForetelling

/-- Under the usual conditions, an almost-everywhere foretelling sequence
can be repaired on its exceptional null set.  On that null set the canonical
deterministic approximation is applied pointwise to the target; completeness
at time zero makes the arbitrary repair stopping-time measurable. -/
noncomputable def of_ae
    {μ : Measure Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (hUsual : Filtration.UsualConditions μ ℱ)
    {τ : Ω → WithTop ℝ≥0}
    (σ : ℕ → Ω → WithTop ℝ≥0)
    (hσ : ∀ n, IsStoppingTime ℱ (σ n))
    (hvalid : ∀ᵐ ω ∂μ,
      Monotone (fun n => σ n ω) ∧
        (∀ n, σ n ω ≤ τ ω) ∧
        (∀ n, τ ω ≠ 0 → σ n ω < τ ω) ∧
        Tendsto (fun n => σ n ω) atTop (𝓝 (τ ω))) :
    StoppingTimeForetelling ℱ τ := by
  classical
  let good : Set Ω := {ω |
    Monotone (fun n => σ n ω) ∧
      (∀ n, σ n ω ≤ τ ω) ∧
      (∀ n, τ ω ≠ 0 → σ n ω < τ ω) ∧
      Tendsto (fun n => σ n ω) atTop (𝓝 (τ ω))}
  have hbad : μ goodᶜ = 0 := by
    rw [← mem_ae_iff]
    exact hvalid
  let repaired : ℕ → Ω → WithTop ℝ≥0 := fun n ω =>
    if ω ∈ good then σ n ω else constApprox n (τ ω)
  have hRepairedStopping : ∀ n, IsStoppingTime ℱ (repaired n) := by
    intro n t
    have heq : {ω | repaired n ω ≤ (t : WithTop ℝ≥0)} =
        (good ∩ {ω | σ n ω ≤ (t : WithTop ℝ≥0)}) ∪
          (goodᶜ ∩ {ω | constApprox n (τ ω) ≤ (t : WithTop ℝ≥0)}) := by
      ext ω
      by_cases hω : ω ∈ good <;> simp [repaired, hω]
    rw [heq]
    have hbadZero : MeasurableSet[ℱ 0] goodᶜ :=
      hUsual.measurableSet_of_null bot_le hbad
    have hgoodZero : MeasurableSet[ℱ 0] good := by
      simpa only [compl_compl] using hbadZero.compl
    apply ((ℱ.mono bot_le _ hgoodZero).inter (hσ n t)).union
    apply hUsual.measurableSet_of_null bot_le
    exact measure_mono_null inter_subset_left hbad
  refine
    { time := repaired
      isStoppingTime := hRepairedStopping
      monotone := ?_
      le := ?_
      lt_of_ne_zero := ?_
      tendsto := ?_ }
  · intro ω
    by_cases hω : ω ∈ good
    · simpa only [repaired, ite_eq_left hω] using hω.1
    · simpa only [repaired, ite_eq_right hω] using constApprox_mono (τ ω)
  · intro n ω
    by_cases hω : ω ∈ good
    · simpa only [repaired, ite_eq_left hω] using hω.2.1 n
    · simpa only [repaired, ite_eq_right hω] using constApprox_le n (τ ω)
  · intro n ω hτ
    by_cases hω : ω ∈ good
    · simpa only [repaired, ite_eq_left hω] using hω.2.2.1 n hτ
    · simpa only [repaired, ite_eq_right hω] using
        constApprox_lt_of_ne_zero n hτ
  · intro ω
    by_cases hω : ω ∈ good
    · simpa only [repaired, ite_eq_left hω] using hω.2.2.2
    · simpa only [repaired, ite_eq_right hω] using tendsto_constApprox (τ ω)

/-- Foretelling is invariant under almost-everywhere equality of its target
under the usual conditions.  The announcing sequence is repaired on the
single exceptional null set. -/
noncomputable def congr_ae
    {μ : Measure Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (hUsual : Filtration.UsualConditions μ ℱ)
    {σ τ : Ω → WithTop ℝ≥0}
    (a : StoppingTimeForetelling ℱ σ) (hστ : σ =ᵐ[μ] τ) :
    StoppingTimeForetelling ℱ τ := by
  apply of_ae hUsual a.time a.isStoppingTime
  filter_upwards [hστ] with ω hω
  refine ⟨a.monotone ω, ?_, ?_, ?_⟩
  · intro n
    exact (a.le n ω).trans_eq hω
  · intro n hτ
    rw [← hω]
    apply a.lt_of_ne_zero n ω
    simpa only [hω] using hτ
  · simpa only [hω] using a.tendsto ω

end StoppingTimeForetelling

end FTAPTheorem42
