/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Basic.CountableRangeStoppedMartingale
import FTAPTheorem42.Stochastic.Martingale.Basic.CompatibleLocalMartingaleGluing
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableStrategyAlgebra
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableCumulativeVariationBridge
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableFiniteVariationIntegral
import FTAPTheorem42.Stochastic.Predictable.PredictableHahnVariationMass
import FTAPTheorem42.Stochastic.Integral.Calculus.SemimartingaleStrategy
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableFiniteVariationBridge
import FTAPTheorem42.Stochastic.Martingale.Basic.RightContinuousStoppedMartingale

/-!
# Synchronizing right-continuous local martingales

The pointwise minimum of two arbitrary localizing sequences synchronizes two
right-continuous local martingales.  The bottom-time indicators appearing in
mathlib's `Locally` definition are retained throughout.  Unlike the earlier
countable-range consumer, no range assumption is imposed on either sequence.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Re-stopping one localized right-continuous martingale at a second
stopping time gives the localization at the pointwise minimum. -/
theorem martingale_indicator_stopped_min_of_rightContinuous
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [SigmaFiniteFiltration μ ℱ]
    {X : Process Ω} {τ σ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime ℱ σ)
    (hXStopped : Martingale
      (MeasureTheory.stoppedProcess
        (fun i => {ω | (⊥ : WithTop ℝ≥0) < τ ω}.indicator (X i)) τ) ℱ μ)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t) :
    Martingale
      (MeasureTheory.stoppedProcess
        (fun i => {ω | (⊥ : WithTop ℝ≥0) < min (τ ω) (σ ω)}.indicator (X i))
        (fun ω => min (τ ω) (σ ω))) ℱ μ := by
  let sτ : Set Ω := {ω | (⊥ : WithTop ℝ≥0) < τ ω}
  let sσ : Set Ω := {ω | (⊥ : WithTop ℝ≥0) < σ ω}
  let sρ : Set Ω := sτ ∩ sσ
  let ρ : Ω → WithTop ℝ≥0 := fun ω => min (τ ω) (σ ω)
  have hsσ : MeasurableSet[ℱ ⊥] sσ := by
    have hEq : sσ = ({ω | σ ω ≤ (0 : ℝ≥0)} : Set Ω)ᶜ := by
      ext ω
      simp only [sσ, Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
      rfl
    rw [hEq]
    exact (hσ.measurableSet_le 0).compl
  have hRestricted : Martingale
      (fun i ω => sσ.indicator
        (MeasureTheory.stoppedProcess
          (fun k => sτ.indicator (X k)) τ i) ω) ℱ μ := by
    simpa only [sτ, sσ] using
      hXStopped.indicator_of_measurableSet_bot hsσ
  have hIndicatorRight : ∀ ω t, ContinuousWithinAt
      ((fun i ω => sτ.indicator (X i) ω) · ω) (Set.Ici t) t :=
    RightContinuousStoppedMartingale.indicator_rightContinuous X sτ hXRight
  have hStoppedRight : ∀ ω t, ContinuousWithinAt
      (MeasureTheory.stoppedProcess
        (fun i ω => sτ.indicator (X i) ω) τ · ω) (Set.Ici t) t :=
    RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
      (fun i ω => sτ.indicator (X i) ω) hIndicatorRight
  have hRestrictedRight : ∀ ω t, ContinuousWithinAt
      ((fun i ω => sσ.indicator
        (MeasureTheory.stoppedProcess
          (fun k => sτ.indicator (X k)) τ i) ω) · ω) (Set.Ici t) t :=
    RightContinuousStoppedMartingale.indicator_rightContinuous
      (MeasureTheory.stoppedProcess
        (fun i ω => sτ.indicator (X i) ω) τ) sσ hStoppedRight
  have hCrossStopped : Martingale
      (MeasureTheory.stoppedProcess
        (fun i ω => sσ.indicator
          (MeasureTheory.stoppedProcess
            (fun k => sτ.indicator (X k)) τ i) ω) σ) ℱ μ :=
    RightContinuousStoppedMartingale.Martingale.stoppedProcess_of_rightContinuous
      hRestricted hσ hRestrictedRight
  have hsρ : {ω | (⊥ : WithTop ℝ≥0) < ρ ω} = sρ := by
    ext ω
    simp only [ρ, sρ, sτ, sσ, Set.mem_ofPred_eq, Set.mem_inter_iff,
      lt_min_iff]
  have hNested :
      MeasureTheory.stoppedProcess
          (fun i ω => sσ.indicator
            (MeasureTheory.stoppedProcess
              (fun k => sτ.indicator (X k)) τ i) ω) σ =
        (fun i ω => sρ.indicator
          (MeasureTheory.stoppedProcess X ρ i) ω) := by
    rw [MeasureTheory.stoppedProcess_indicator_comm']
    rw [MeasureTheory.stoppedProcess_stoppedProcess']
    rw [MeasureTheory.stoppedProcess_indicator_comm']
    ext i ω
    by_cases hτω : ω ∈ sτ <;> by_cases hσω : ω ∈ sσ <;>
      simp [sρ, ρ, hτω, hσω, min_comm]
  rw [hNested] at hCrossStopped
  have hTarget :
      MeasureTheory.stoppedProcess
          (fun i => {ω | (⊥ : WithTop ℝ≥0) < ρ ω}.indicator (X i)) ρ =
        (fun i ω => sρ.indicator
          (MeasureTheory.stoppedProcess X ρ i) ω) := by
    rw [hsρ, MeasureTheory.stoppedProcess_indicator_comm']
  rw [hTarget]
  exact hCrossStopped

/-- The pointwise minima of arbitrary localizing sequences form a common
localizing sequence for two right-continuous local martingales. -/
noncomputable def commonLocalizingSequence_of_rightContinuous
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [SigmaFiniteFiltration μ ℱ]
    {X Y : Process Ω}
    (hX : LocalMartingale X ℱ μ) (hY : LocalMartingale Y ℱ μ)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (hYRight : ∀ ω t,
      ContinuousWithinAt (Y · ω) (Set.Ici t) t) :
    CommonLocalizingSequence (ℱ := ℱ) μ X Y := by
  let τ := Classical.choose hX
  have hτSpec := Classical.choose_spec hX
  let σ := Classical.choose hY
  have hσSpec := Classical.choose_spec hY
  let hτ := hτSpec.1
  let hXStopped := hτSpec.2
  let hσ := hσSpec.1
  let hYStopped := hσSpec.2
  let ρ : ℕ → Ω → WithTop ℝ≥0 := fun n ω => min (τ n ω) (σ n ω)
  refine ⟨ρ, hτ.min hσ, fun n => ?_, fun n => ?_⟩
  · have hXCommon := martingale_indicator_stopped_min_of_rightContinuous
      (hσ.isStoppingTime n) (hXStopped n) hXRight
    simpa only [ρ] using hXCommon
  · have hYCommonRaw := martingale_indicator_stopped_min_of_rightContinuous
      (hτ.isStoppingTime n) (hYStopped n) hYRight
    simpa only [ρ, min_comm] using hYCommonRaw

/-- Two arbitrary localizing sequences can be synchronized by their
pointwise minimum when both local martingales have right-continuous paths. -/
theorem LocalMartingale.add_of_rightContinuous
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    [SigmaFiniteFiltration μ ℱ]
    {X Y : Process Ω}
    (hX : LocalMartingale X ℱ μ) (hY : LocalMartingale Y ℱ μ)
    (hXRight : ∀ ω t,
      ContinuousWithinAt (X · ω) (Set.Ici t) t)
    (hYRight : ∀ ω t,
      ContinuousWithinAt (Y · ω) (Set.Ici t) t) :
    LocalMartingale (fun t ω => X t ω + Y t ω) ℱ μ := by
  exact LocalMartingale.add_of_commonLocalizingSequence
    (commonLocalizingSequence_of_rightContinuous
      hX hY hXRight hYRight)

namespace SIntegrableStrategy

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsFiniteMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- Componentwise addition of realized strategies whose martingale parts are
right-continuous.  Arbitrary localizing sequences are synchronized by
`LocalMartingale.add_of_rightContinuous`. -/
noncomputable def add_of_rightContinuous
    (H K : SIntegrableStrategy D) :
    SIntegrableStrategy D where
  integrand := fun t ω => H.integrand t ω + K.integrand t ω
  stochasticIntegral := fun t ω =>
    H.stochasticIntegral t ω + K.stochasticIntegral t ω
  martingalePart := fun t ω => H.martingalePart t ω + K.martingalePart t ω
  finiteVariationPart := fun t ω =>
    H.finiteVariationPart t ω + K.finiteVariationPart t ω
  finiteVariationMeasure :=
    H.finiteVariationMeasure + K.finiteVariationMeasure
  integrand_isPredictable :=
    H.integrand_isPredictable.add K.integrand_isPredictable
  stochasticIntegral_isStronglyAdapted := fun t =>
    (H.stochasticIntegral_isStronglyAdapted t).add
      (K.stochasticIntegral_isStronglyAdapted t)
  stochasticIntegral_isRightContinuous := fun ω t =>
    (H.stochasticIntegral_isRightContinuous ω t).add
      (K.stochasticIntegral_isRightContinuous ω t)
  martingalePart_isLocalMartingale :=
    LocalMartingale.add_of_rightContinuous
      H.martingalePart_isLocalMartingale K.martingalePart_isLocalMartingale
      H.martingalePart_isRightContinuous K.martingalePart_isRightContinuous
  martingalePart_isStronglyAdapted := fun t =>
    (H.martingalePart_isStronglyAdapted t).add
      (K.martingalePart_isStronglyAdapted t)
  martingalePart_isRightContinuous := fun ω t =>
    (H.martingalePart_isRightContinuous ω t).add
      (K.martingalePart_isRightContinuous ω t)
  finiteVariationPart_isPredictable :=
    H.finiteVariationPart_isPredictable.add K.finiteVariationPart_isPredictable
  finiteVariationPart_isRightContinuous := fun ω t =>
    (H.finiteVariationPart_isRightContinuous ω t).add
      (K.finiteVariationPart_isRightContinuous ω t)
  finiteVariationPart_isBoundedVariation := fun ω =>
    boundedVariationOn_add
      (H.finiteVariationPart_isBoundedVariation ω)
      (K.finiteVariationPart_isBoundedVariation ω)
  integral_decomposition := by
    filter_upwards [H.integral_decomposition, K.integral_decomposition]
      with ω hH hK
    intro t
    rw [hH t, hK t]
    ring
  source_decomposition := H.source_decomposition

end SIntegrableStrategy

end FTAPTheorem42
