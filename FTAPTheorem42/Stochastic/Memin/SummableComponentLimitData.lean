/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Trading.TerminalImprovement
import FTAPTheorem42.Stochastic.FiniteVariation.BoundedVariationLimit
import FTAPTheorem42.Stochastic.DS.Lemma411.MaximalApproximation
import FTAPTheorem42.Stochastic.Martingale.Basic.BoundedStoppingOptionalSampling
import FTAPTheorem42.Stochastic.DS.Lemma47.AnnouncedFirstLocalization
import FTAPTheorem42.Stochastic.Martingale.Basic.CompatibleLocalMartingaleGluing
import FTAPTheorem42.Stochastic.Martingale.Basic.UniformL2MartingaleLimit
import FTAPTheorem42.Stochastic.DS.Lemma410.StrategyConvexification
import FTAPTheorem42.Stochastic.DS.Lemma411.VariationWitness
import FTAPTheorem42.Stochastic.Memin.FiniteVariationBridge
import FTAPTheorem42.Stochastic.Memin.LocalS1Normalization
import FTAPTheorem42.Stochastic.Process.NullSetProcessRegularization
import FTAPTheorem42.Stochastic.Process.UniformLimits
import FTAPTheorem42.Foundations.CommonHilbertConvexification
import FTAPTheorem42.Stochastic.DS.Lemma410.StoppedPrefixMartingale
import FTAPTheorem42.Stochastic.Martingale.Basic.ConditionalExpectationL2
import FTAPTheorem42.Stochastic.Martingale.Basic.MartingaleAbsoluteEnvelope
import FTAPTheorem42.Stochastic.DS.Lemma48.NormalizedTail
import FTAPTheorem42.Foundations.MaximalProbability
import FTAPTheorem42.Stochastic.DS.Lemma49.StoppedTailMartingale
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrablePathwiseRestrictionCalculus
import FTAPTheorem42.Foundations.CadlagEnvelope
import FTAPTheorem42.Stochastic.DS.Lemma47.DownsideStopping
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableActualConvexCombination
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableActualScalarCalculus
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableRealizationModel
import FTAPTheorem42.Trading.Basic
import FTAPTheorem42.Stochastic.Memin.FiniteVariationLimit

/-!
# Actual summable component-limit data for the Mémín step

The raw Lemma 4.11 endpoint selects common convex weights, a strict
subsequence, and simultaneous component limits.  This module uses the
carrier-level convex-combination closure to package that very same
subsequence as actual stochastic-integral strategies.  The resulting data
bundle contains the summability and convergence facts needed by the Mémín
range-identification step; it does not assume that either limit is already a
stochastic integral.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

open SIntegrablePredictableMultiplierLinearL2Calculus

/-- The actual strategy subsequence and its already-proved component limits.
No range realization of either limit is included in this structure. -/
structure MeminSummableComponentLimitData
    {S : Process Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ]
    {D : SpecialSemimartingaleDecomposition S ℱ μ}
    (R : SIntegrableRealizationModel D) where
  approximant : ℕ → ActualSIntegrableStrategy R
  martingaleLimit : Process Ω
  finiteVariationLimit : Process Ω
  martingaleLimit_stronglyAdapted : StronglyAdapted ℱ martingaleLimit
  martingaleLimit_localMartingale : LocalMartingale martingaleLimit ℱ μ
  finiteVariationLimit_isStronglyPredictable :
    IsStronglyPredictable ℱ finiteVariationLimit
  martingaleLimit_rightContinuous :
    ∀ ω t, ContinuousWithinAt (martingaleLimit · ω) (Set.Ici t) t
  finiteVariationLimit_rightContinuous :
    ∀ ω t, ContinuousWithinAt (finiteVariationLimit · ω) (Set.Ici t) t
  finiteVariationLimit_boundedVariation :
    ∀ ω, BoundedVariationOn (finiteVariationLimit · ω) Set.univ
  finiteVariationLimit_zero : finiteVariationLimit 0 =ᵐ[μ] 0
  gainEnvelope : Ω → ℝ
  gainEnvelope_memLp : MemLp gainEnvelope (2 : ℝ≥0∞) μ
  approximant_martingaleLeft :
    ∀ k, ProcessHasLeftLimits (approximant k).val.martingalePart
  approximant_martingaleZero :
    ∀ k, (approximant k).val.martingalePart 0 =ᵐ[μ] 0
  approximant_finiteVariationZero :
    ∀ k, (approximant k).val.finiteVariationPart 0 =ᵐ[μ] 0
  approximant_gainBound : ∀ k, ∀ᵐ ω ∂μ, ∀ t,
    |(approximant k).val.stochasticIntegral t ω| ≤ gainEnvelope ω
  variationSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
    lemma411DifferenceTotalVariation
        (approximant (k + 1)).val (approximant k).val ω)
  martingaleEnvelopeSummable : ∀ T, ∀ᵐ ω ∂μ, Summable (fun k =>
    meminMartingaleDifferenceEnvelope
      (ActualSIntegrableStrategy.rawSequence approximant) T k ω)
  martingaleTendsto : ∀ᵐ ω ∂μ, ∀ t,
    Tendsto (fun k => (approximant k).val.martingalePart t ω)
      atTop (𝓝 (martingaleLimit t ω))
  finiteVariationTendsto : ∀ᵐ ω ∂μ, ∀ t,
    Tendsto (fun k => (approximant k).val.finiteVariationPart t ω)
      atTop (𝓝 (finiteVariationLimit t ω))
  gainTendsto : ∀ᵐ ω ∂μ, ∀ t,
    Tendsto (fun k => (approximant k).val.stochasticIntegral t ω)
      atTop (𝓝 (martingaleLimit t ω + finiteVariationLimit t ω))
  martingaleTendstoUniformly : ∀ᵐ ω ∂μ,
    TendstoUniformly
      (fun k t => (approximant k).val.martingalePart t ω)
      (fun t => martingaleLimit t ω) atTop
  finiteVariationTendstoUniformly : ∀ᵐ ω ∂μ,
    TendstoUniformly
      (fun k t => (approximant k).val.finiteVariationPart t ω)
      (fun t => finiteVariationLimit t ω) atTop
  finiteVariationVariationTendsto : ∀ᵐ ω ∂μ,
    Tendsto (fun k => eVariationOn
      (fun t => finiteVariationLimit t ω -
        (approximant k).val.finiteVariationPart t ω) Set.univ)
      atTop (𝓝 0)

namespace MeminSummableComponentLimitData

open SIntegrablePredictableMultiplierLinearL2Calculus

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}
  {R : SIntegrableRealizationModel D}
  {G : ActualLocallySIntegrableStrategy R}

/-- The finite-variation Stieltjes limit theorem instantiated on the actual
subsequence stored in the component-limit data. -/
theorem finiteVariation_stopped_signedMeasure_eq
    (data : MeminSummableComponentLimitData R)
    (C : SIntegrableFiniteVariationStieltjesCalculus D R G) :
    ∀ r, ∀ᵐ ω ∂μ,
      (FiniteVariationPath.signedMeasure
        ((G.val.deterministicallyStopped ((r + 1 : ℕ) : ℝ≥0) (by positivity)
          ).finiteVariationPart_isBoundedVariation ω)).totalVariation.withDensityᵥ
            (fun t =>
              FiniteVariationPath.variationDirection
                  ((G.val.deterministicallyStopped
                    ((r + 1 : ℕ) : ℝ≥0) (by positivity)
                    ).finiteVariationPart_isBoundedVariation ω) t *
                meminLimitIntegrand
                  (ActualSIntegrableStrategy.rawSequence data.approximant)
                    t ω) =
        FiniteVariationPath.signedMeasure
          (FiniteVariationStoppedPath.boundedVariationOn_stopAt
            (data.finiteVariationLimit_boundedVariation ω)
              ((r + 1 : ℕ) : ℝ≥0)) :=
  C.meminLimitIntegrand_stopped_signedMeasure_eq_limit
    data.approximant data.finiteVariationLimit data.variationSummable
      data.martingaleEnvelopeSummable data.finiteVariationTendsto
        data.finiteVariationLimit_boundedVariation
          data.finiteVariationLimit_rightContinuous

variable [ℱ.IsRightContinuous]

end MeminSummableComponentLimitData

end FTAPTheorem42
