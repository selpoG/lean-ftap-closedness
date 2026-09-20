/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Calculus.SemimartingaleStrategy
import FTAPTheorem42.Foundations.Paths

/-!
# Left jumps of real-valued processes

This module records the pathwise left-jump algebra needed by the canonical
decomposition in Lemma 4.7.  Process decompositions are used on their common
full-measure set, so the resulting jump identity holds simultaneously at all
times rather than only almost everywhere at each fixed time.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal ProbabilityTheory BigOperators

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A bounded-variation component has left limits on every sample path. -/
theorem SIntegrableStrategy.finiteVariationPart_hasLeftLimits
    {S : Process Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω}
    {D : SpecialSemimartingaleDecomposition S ℱ μ}
    (H : SIntegrableStrategy D) :
    ProcessHasLeftLimits H.finiteVariationPart := by
  intro ω t
  exact (H.finiteVariationPart_isBoundedVariation ω).tendsto_leftLim t

/-- The realized integral decomposition supplies its left-jump decomposition
as soon as the local-martingale component has left limits. -/
theorem SIntegrableStrategy.processLeftJump_eq_components
    {S : Process Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω}
    {D : SpecialSemimartingaleDecomposition S ℱ μ}
    (H : SIntegrableStrategy D)
    (hM : ProcessHasLeftLimits H.martingalePart) :
    ∀ᵐ ω ∂μ, ∀ t,
      processLeftJump H.stochasticIntegral t ω =
        processLeftJump H.martingalePart t ω +
          processLeftJump H.finiteVariationPart t ω :=
  H.integral_decomposition.processLeftJump_eq_add hM
    H.finiteVariationPart_hasLeftLimits

/-- An all-time envelope for the realized gain controls all of its left
jumps.  Indistinguishability supplies the left-limit property on the same
full-measure set as the component decomposition. -/
theorem SIntegrableStrategy.abs_processLeftJump_stochasticIntegral_le
    {S : Process Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω}
    {D : SpecialSemimartingaleDecomposition S ℱ μ}
    (H : SIntegrableStrategy D)
    (hM : ProcessHasLeftLimits H.martingalePart)
    (ξ : Ω → ℝ)
    (hbound : ∀ᵐ ω ∂μ, ∀ t, |H.stochasticIntegral t ω| ≤ ξ ω) :
    ∀ᵐ ω ∂μ, ∀ t,
      |processLeftJump H.stochasticIntegral t ω| ≤ 2 * ξ ω := by
  filter_upwards [H.integral_decomposition, hbound] with ω hDecomp hBound
  have hPath : (fun t => H.stochasticIntegral t ω) =
      fun t => H.martingalePart t ω + H.finiteVariationPart t ω :=
    funext hDecomp
  intro t
  have hIntegralLeft : Tendsto (fun s => H.stochasticIntegral s ω)
      (𝓝[<] t)
      (𝓝 (Function.leftLim (fun s => H.stochasticIntegral s ω) t)) := by
    simpa only [hPath] using
      ((hM.add H.finiteVariationPart_hasLeftLimits) ω t)
  exact abs_processLeftJump_le_two_mul_of_bound
    H.stochasticIntegral hBound t hIntegralLeft

/-- A finite-horizon envelope for the realized gain controls all of its left
jumps before that horizon. -/
theorem SIntegrableStrategy.abs_processLeftJump_stochasticIntegral_le_upTo
    {S : Process Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω}
    {D : SpecialSemimartingaleDecomposition S ℱ μ}
    (H : SIntegrableStrategy D)
    (hM : ProcessHasLeftLimits H.martingalePart)
    (ξ : Ω → ℝ) (T : ℝ≥0)
    (hbound : ∀ᵐ ω ∂μ, ∀ t, t ≤ T →
      |H.stochasticIntegral t ω| ≤ ξ ω) :
    ∀ᵐ ω ∂μ, ∀ t, t ≤ T →
      |processLeftJump H.stochasticIntegral t ω| ≤ 2 * ξ ω := by
  filter_upwards [H.integral_decomposition, hbound] with ω hDecomp hBound
  have hPath : (fun t => H.stochasticIntegral t ω) =
      fun t => H.martingalePart t ω + H.finiteVariationPart t ω :=
    funext hDecomp
  intro t ht
  have hIntegralLeft : Tendsto (fun s => H.stochasticIntegral s ω)
      (𝓝[<] t)
      (𝓝 (Function.leftLim (fun s => H.stochasticIntegral s ω) t)) := by
    simpa only [hPath] using
      ((hM.add H.finiteVariationPart_hasLeftLimits) ω t)
  exact abs_processLeftJump_le_two_mul_of_bound_upTo
    H.stochasticIntegral hBound ht hIntegralLeft

end FTAPTheorem42
