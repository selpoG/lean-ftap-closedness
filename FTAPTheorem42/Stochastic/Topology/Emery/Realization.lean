/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Topology.Emery.Completion
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.MartingaleIntegralCadlag

/-!
# Realized gains in the elementary Emery completion

An element of the realized completion is represented by a predictable
elementary sequence together with a strongly adapted càdlàg gain process.
The gain is required to be the compact-uniform-in-measure limit on each
finite integer horizon.  No terminal value, raw integrand, or semimartingale
decomposition is part of this carrier.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace PredictableElementaryEmery

variable {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- The running gain of a predictable elementary strategy. -/
noncomputable def elementaryGain
    (S : Process Ω) (H : PredictableElementaryStrategy ℱ) : Process Ω :=
  ElementaryStrategy.gain S H.toElementary

theorem tendstoInMeasure_of_nonneg_le
    {μ : Measure Ω} {f g : ℕ → Ω → ℝ}
    (hfg : ∀ n ω, 0 ≤ f n ω ∧ f n ω ≤ g n ω)
    (hg : TendstoInMeasure μ g atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure μ f atTop (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_enorm] at hg ⊢
  intro ε hε hεtop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds (hg ε hε hεtop)
  · exact fun _ => zero_le
  · intro n
    apply measure_mono
    intro ω hω
    have hf0 := (hfg n ω).1
    have hfg' := (hfg n ω).2
    have hg0 : 0 ≤ g n ω := hf0.trans hfg'
    change ε ≤ ‖f n ω - 0‖ₑ at hω
    change ε ≤ ‖g n ω - 0‖ₑ
    rw [sub_zero, Real.enorm_eq_ofReal hf0] at hω
    rw [sub_zero, Real.enorm_eq_ofReal hg0]
    exact hω.trans (ENNReal.ofReal_le_ofReal hfg')

theorem tendstoInMeasure_of_nonneg_le_add
    {μ : Measure Ω} {f g h : ℕ → Ω → ℝ}
    (hf : ∀ n ω, 0 ≤ f n ω)
    (hfg : ∀ n ω, f n ω ≤ g n ω + h n ω)
    (hgMeasure : TendstoInMeasure μ g atTop (fun _ => (0 : ℝ)))
    (hhMeasure : TendstoInMeasure μ h atTop (fun _ => (0 : ℝ))) :
    TendstoInMeasure μ f atTop (fun _ => (0 : ℝ)) := by
  apply tendstoInMeasure_of_nonneg_le
    (fun n ω => ⟨hf n ω, hfg n ω⟩)
  have hSum := tendstoInMeasure_add hgMeasure hhMeasure
  simpa only [Pi.zero_apply, add_zero] using hSum

/-- A representative sequence and its right-continuous gain limit. -/
structure RealizedStrategy
    (μ : Measure Ω) (S : Process Ω) where
  representative : ℕ → PredictableElementaryStrategy ℱ
  /-- A deterministic coefficient-sum bound for each elementary row. -/
  representativeBound : ℕ → ℝ≥0
  representative_coefficientAbsSum_le : ∀ n ω,
    (representative n).coefficientAbsSum ω ≤ representativeBound n
  gain : Process Ω
  gain_stronglyAdapted : StronglyAdapted ℱ gain
  gain_rightContinuous : ∀ ω t,
    ContinuousWithinAt (gain · ω) (Set.Ici t) t
  gain_hasLeftLimits : ProcessHasLeftLimits gain
  gain_convergence : ∀ r : ℕ,
    TendstoInMeasure μ
      (fun n => FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (fun t ω => elementaryGain S (representative n) t ω - gain t ω)
        ((r + 1 : ℕ) : ℝ≥0))
      atTop (fun _ => 0)
  isCauchy : PredictableElementaryEmery.IsCauchy μ S representative

/-- The constant elementary sequence is a canonical realized carrier.

This constructor is deliberately limited to a sequence which already has a
pathwise càdlàg elementary gain.  It supplies no terminal value or raw
integrand data beyond the representative sequence itself. -/
noncomputable def RealizedStrategy.constant
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : Process Ω) (hS : IsStronglyProgressive ℱ S)
    (hSRight : ∀ ω t,
      ContinuousWithinAt (S · ω) (Set.Ici t) t)
    (hSLeft : ProcessHasLeftLimits S)
    (H : PredictableElementaryStrategy ℱ)
    (C : ℝ≥0)
    (hC : ∀ ω, H.coefficientAbsSum ω ≤ C) :
    RealizedStrategy (ℱ := ℱ) μ S where
  representative := fun _ => H
  representativeBound := fun _ => C
  representative_coefficientAbsSum_le := by
    intro n ω
    exact hC ω
  gain := elementaryGain S H
  gain_stronglyAdapted :=
    PredictableElementaryStrategy.stronglyAdapted_gain S hS H
  gain_rightContinuous := by
    intro ω t
    exact PredictableElementaryStrategy.rightContinuous_gain S hSRight H ω t
  gain_hasLeftLimits := by
    exact ElementaryStrategy.gain_hasLeftLimits S hSLeft H.toElementary
  gain_convergence := by
    intro r
    have hDiff :
        (fun t ω => elementaryGain S H t ω - elementaryGain S H t ω) =
          (fun _ _ => (0 : ℝ)) := by
      funext t ω
      exact sub_self _
    rw [hDiff]
    convert tendstoInMeasure_const μ (fun _ : Ω => (0 : ℝ)) using 1
    funext n ω
    exact cappedFiniteHorizonAbsoluteEnvelope_zero
      ((r + 1 : ℕ) : ℝ≥0) ω
  isCauchy := PredictableElementaryEmery.constant_isCauchy S hS H

end PredictableElementaryEmery

end FTAPTheorem42
