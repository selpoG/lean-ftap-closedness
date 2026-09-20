/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.Variation
import FTAPTheorem42.Stochastic.Integral.Calculus.SemimartingaleStrategy
import Mathlib.Probability.Martingale.OptionalStopping

/-!
# Linear calculus for realized stochastic-integrable strategies

This module proves the negation part of the general strategy calculus and the
addition part under an explicit common localizing sequence.  It does not
construct a stochastic integral or assume stochastic-integral closedness.
Synchronizing two arbitrary localizing sequences remains a separate
continuous-time boundary.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Local-martingale algebra -/

theorem LocalMartingale.neg
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} {X : Process Ω}
    (hX : LocalMartingale X ℱ μ) :
    LocalMartingale (fun t ω => -X t ω) ℱ μ := by
  rcases hX with ⟨τ, hτ, hStopped⟩
  refine ⟨τ, hτ, fun n => ?_⟩
  have hEq :
      MeasureTheory.stoppedProcess
          (fun i => {ω | ⊥ < τ n ω}.indicator (fun ω => -X i ω)) (τ n) =
        -MeasureTheory.stoppedProcess
          (fun i => {ω | ⊥ < τ n ω}.indicator (X i)) (τ n) := by
    ext i ω
    simp only [Pi.neg_apply, MeasureTheory.stoppedProcess]
    by_cases hω : ω ∈ {ω : Ω | ⊥ < τ n ω}
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
      simp
  rw [hEq]
  exact (hStopped n).neg

theorem LocalMartingale.smul
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} {X : Process Ω} (c : ℝ)
    (hX : LocalMartingale X ℱ μ) :
    LocalMartingale (fun t ω => c * X t ω) ℱ μ := by
  rcases hX with ⟨τ, hτ, hStopped⟩
  refine ⟨τ, hτ, fun n => ?_⟩
  have hSmul := (hStopped n).smul c
  convert hSmul using 1
  ext i ω
  simp only [MeasureTheory.stoppedProcess, Pi.smul_apply, smul_eq_mul]
  by_cases hω : ω ∈ {ω : Ω | ⊥ < τ n ω}
  · simp only [Set.indicator_of_mem hω]
  · simp only [Set.indicator_of_notMem hω]
    simp

/-! ## Addition under a supplied common localization -/

structure CommonLocalizingSequence
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (μ : Measure Ω) (X Y : Process Ω) where
  sequence : ℕ → Ω → WithTop ℝ≥0
  isLocalizing : ProbabilityTheory.IsLocalizingSequence ℱ sequence μ
  stopped_X : ∀ n, MeasureTheory.Martingale
    (MeasureTheory.stoppedProcess
      (fun i => {ω | ⊥ < sequence n ω}.indicator (X i)) (sequence n)) ℱ μ
  stopped_Y : ∀ n, MeasureTheory.Martingale
    (MeasureTheory.stoppedProcess
      (fun i => {ω | ⊥ < sequence n ω}.indicator (Y i)) (sequence n)) ℱ μ

theorem LocalMartingale.add_of_commonLocalizingSequence
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} {X Y : Process Ω}
    (h : CommonLocalizingSequence (ℱ := ℱ) μ X Y) :
    LocalMartingale (fun t ω => X t ω + Y t ω) ℱ μ := by
  refine ⟨h.sequence, h.isLocalizing, fun n => ?_⟩
  have hsum := (h.stopped_X n).add (h.stopped_Y n)
  convert hsum using 1
  ext i ω
  simp only [MeasureTheory.stoppedProcess, Pi.add_apply]
  by_cases hω : ω ∈ {ω : Ω | ⊥ < h.sequence n ω}
  · simp only [Set.indicator_of_mem hω]
  · simp only [Set.indicator_of_notMem hω]
    simp

/-! ## Component-wise strategy negation -/

namespace SIntegrableStrategy

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω}
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

noncomputable def neg (H : SIntegrableStrategy D) : SIntegrableStrategy D where
  integrand := fun t ω => -H.integrand t ω
  stochasticIntegral := fun t ω => -H.stochasticIntegral t ω
  martingalePart := fun t ω => -H.martingalePart t ω
  finiteVariationPart := fun t ω => -H.finiteVariationPart t ω
  finiteVariationMeasure := -H.finiteVariationMeasure
  integrand_isPredictable := H.integrand_isPredictable.neg
  stochasticIntegral_isStronglyAdapted := fun t =>
    (H.stochasticIntegral_isStronglyAdapted t).neg
  stochasticIntegral_isRightContinuous := fun ω t =>
    (H.stochasticIntegral_isRightContinuous ω t).neg
  martingalePart_isLocalMartingale := H.martingalePart_isLocalMartingale.neg
  martingalePart_isStronglyAdapted := fun t =>
    (H.martingalePart_isStronglyAdapted t).neg
  martingalePart_isRightContinuous := fun ω t =>
    (H.martingalePart_isRightContinuous ω t).neg
  finiteVariationPart_isPredictable := H.finiteVariationPart_isPredictable.neg
  finiteVariationPart_isRightContinuous := fun ω t =>
    (H.finiteVariationPart_isRightContinuous ω t).neg
  finiteVariationPart_isBoundedVariation := fun ω =>
    boundedVariationOn_neg (H.finiteVariationPart_isBoundedVariation ω)
  integral_decomposition := by
    filter_upwards [H.integral_decomposition] with ω hω
    intro t
    rw [hω t]
    ring
  source_decomposition := H.source_decomposition

noncomputable def smul (c : ℝ) (H : SIntegrableStrategy D) :
    SIntegrableStrategy D where
  integrand := c • H.integrand
  stochasticIntegral := c • H.stochasticIntegral
  martingalePart := c • H.martingalePart
  finiteVariationPart := c • H.finiteVariationPart
  finiteVariationMeasure := c • H.finiteVariationMeasure
  integrand_isPredictable := H.integrand_isPredictable.const_smul c
  stochasticIntegral_isStronglyAdapted := fun t =>
    (H.stochasticIntegral_isStronglyAdapted t).const_smul c
  stochasticIntegral_isRightContinuous := fun ω t => by
    change ContinuousWithinAt
      (fun u => c * H.stochasticIntegral u ω) (Set.Ici t) t
    exact (continuousWithinAt_const :
      ContinuousWithinAt (fun _ : ℝ≥0 => c) (Set.Ici t) t).mul
        (H.stochasticIntegral_isRightContinuous ω t)
  martingalePart_isLocalMartingale := LocalMartingale.smul c
    H.martingalePart_isLocalMartingale
  martingalePart_isStronglyAdapted := fun t =>
    (H.martingalePart_isStronglyAdapted t).const_smul c
  martingalePart_isRightContinuous := fun ω t => by
    change ContinuousWithinAt
      (fun u => c * H.martingalePart u ω) (Set.Ici t) t
    exact (continuousWithinAt_const :
      ContinuousWithinAt (fun _ : ℝ≥0 => c) (Set.Ici t) t).mul
        (H.martingalePart_isRightContinuous ω t)
  finiteVariationPart_isPredictable := H.finiteVariationPart_isPredictable.const_smul c
  finiteVariationPart_isRightContinuous := fun ω t => by
    change ContinuousWithinAt
      (fun u => c * H.finiteVariationPart u ω) (Set.Ici t) t
    exact (continuousWithinAt_const :
      ContinuousWithinAt (fun _ : ℝ≥0 => c) (Set.Ici t) t).mul
        (H.finiteVariationPart_isRightContinuous ω t)
  finiteVariationPart_isBoundedVariation := fun ω => by
    change BoundedVariationOn
      (fun t => c * H.finiteVariationPart t ω) Set.univ
    change eVariationOn (fun t => c * H.finiteVariationPart t ω) Set.univ ≠ ∞
    have hScaled :
        (‖c‖₊ : ℝ≥0∞) *
            eVariationOn (fun t => H.finiteVariationPart t ω) Set.univ ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top
        (H.finiteVariationPart_isBoundedVariation ω)
    refine ne_top_of_le_ne_top hScaled ?_
    rw [eVariationOn]
    apply iSup_le
    rintro ⟨n, u, hu, us⟩
    calc
      (∑ i ∈ Finset.range n,
          edist (c * H.finiteVariationPart (u (i + 1)) ω)
            (c * H.finiteVariationPart (u i) ω)) =
          ∑ i ∈ Finset.range n,
            ‖c‖₊ * edist (H.finiteVariationPart (u (i + 1)) ω)
              (H.finiteVariationPart (u i) ω) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← smul_eq_mul, ← smul_eq_mul, edist_smul₀]
        simp only [ENNReal.smul_def, smul_eq_mul]
      _ = ‖c‖₊ * ∑ i ∈ Finset.range n,
          edist (H.finiteVariationPart (u (i + 1)) ω)
            (H.finiteVariationPart (u i) ω) := by
        rw [Finset.mul_sum]
      _ ≤ ‖c‖₊ * eVariationOn
          (fun t => H.finiteVariationPart t ω) Set.univ := by
        simpa [mul_comm] using
          (mul_le_mul_left
            (eVariationOn.sum_le
              (f := fun t => H.finiteVariationPart t ω)
              (s := Set.univ) hu us)
            (‖c‖₊ : ℝ≥0∞))
  integral_decomposition := by
    filter_upwards [H.integral_decomposition] with ω hω
    intro t
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hω t]
    ring
  source_decomposition := H.source_decomposition

end SIntegrableStrategy

end FTAPTheorem42
