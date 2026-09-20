/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Construction.DirectSchedule
import FTAPTheorem42.Stochastic.Topology.Emery.GainSemimartingale

/-! # A special raw candidate for a bounded original-price elementary gain

The gain is bounded and is itself a good integrator. Its special decomposition
supplies raw component data only; the original-source integral graph is
proved separately using the original source's completed schedule.
-/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open Filter MeasureTheory
open scoped NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

noncomputable def elementaryGainSource
    (source : BoundedSemimartingaleSource S F μ)
    (K : PredictableElementaryStrategy F) (B : NNReal)
    (hB : ∀ ω, K.coefficientAbsSum ω ≤ B) :
    BoundedSemimartingaleSource (ElementaryStrategy.gain S K.toElementary) F μ := by
  have hS := StronglyAdapted.isStronglyProgressive_of_rightContinuous
    source.stronglyAdapted source.rightContinuous
  refine {
    usualConditions := source.usualConditions
    stronglyAdapted := PredictableElementaryStrategy.stronglyAdapted_gain S hS K
    rightContinuous := PredictableElementaryStrategy.rightContinuous_gain S source.rightContinuous K
    hasLeftLimits := ElementaryStrategy.gain_hasLeftLimits S source.hasLeftLimits K.toElementary
    bound := 2 * B * max source.bound 0
    uniformBound := ?_
    isSemimartingale := PredictableElementaryEmery.RealizedStrategy.gain_isSemimartingale
      S hS source.rightContinuous source.hasLeftLimits source.isSemimartingale
      (PredictableElementaryEmery.RealizedStrategy.constant
        S hS source.rightContinuous source.hasLeftLimits K B hB) }
  filter_upwards [source.uniformBound] with ω hω
  intro t
  have h := K.norm_gain_le_coefficientAbsSum_mul S t ω (max source.bound 0)
    (fun s _ => by simpa only [Real.norm_eq_abs] using (hω s).trans (le_max_left _ _))
  simp only [Real.norm_eq_abs] at h
  exact h.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hB ω) (by norm_num))
      (le_max_right _ _))

/-- The selected gain decomposition is stored under the original source
decomposition. This raw object alone asserts no stochastic integral relation. -/
noncomputable def elementaryRawCandidate
    (source : BoundedSemimartingaleSource S F μ)
    (K : PredictableElementaryStrategy F) (B : NNReal)
    (hB : ∀ ω, K.coefficientAbsSum ω ≤ B) :
    LocallySIntegrableStrategy (sourceData source).regularizedDecomposition := by
  let L := unitSource (elementaryGainSource source K B hB)
  have hGain : L.stochasticIntegral = ElementaryStrategy.gain S K.toElementary := by
    funext t ω
    change ElementaryStrategy.gain S K.toElementary t ω -
      ElementaryStrategy.gain S K.toElementary 0 ω = _
    simp [ElementaryStrategy.gain, ElementaryInterval.gain]
  exact {
    integrand := K.integrand
    stochasticIntegral := ElementaryStrategy.gain S K.toElementary
    martingalePart := L.martingalePart
    finiteVariationPart := L.finiteVariationPart
    integrand_isPredictable := K.integrand_isStronglyPredictable
    stochasticIntegral_isStronglyAdapted := hGain ▸ L.stochasticIntegral_isStronglyAdapted
    stochasticIntegral_isRightContinuous := hGain ▸ L.stochasticIntegral_isRightContinuous
    martingalePart_isLocalMartingale := L.martingalePart_isLocalMartingale
    martingalePart_isStronglyAdapted := L.martingalePart_isStronglyAdapted
    martingalePart_isRightContinuous := L.martingalePart_isRightContinuous
    finiteVariationPart_isPredictable := L.finiteVariationPart_isPredictable
    finiteVariationPart_isRightContinuous := L.finiteVariationPart_isRightContinuous
    finiteVariationPart_isLocallyBoundedVariation := L.finiteVariationPart_isLocallyBoundedVariation
    integral_decomposition := by
      filter_upwards [L.integral_decomposition] with ω hω
      intro t
      exact (congrFun (congrFun hGain t) ω).symm.trans (hω t)
    source_decomposition := (unitSource source).source_decomposition }

end FTAPTheorem42.BoundedSourceIntegralMarket

namespace FTAPTheorem42.BoundedSourceIntegralMarket

/-!
## The intrinsic integral market of an original bounded source

The source decomposition and localization schedule are produced by existing
theorems. Only the proved schedule and intrinsic market definitions remain here.
The integrator is the original price, with unit gain `S - S₀`.
-/

open Filter MeasureTheory
open scoped NNReal ENNReal Topology ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

variable [SigmaFiniteFiltration μ F]

/-- The original bounded price supplies a constant L² envelope. -/
noncomputable def schedule (source : BoundedSemimartingaleSource S F μ) :
    LocalCompletedM2A.LocalCompletedM2ASchedule (unitSource source) := directSchedule source

end FTAPTheorem42.BoundedSourceIntegralMarket

namespace FTAPTheorem42.BoundedSourceIntegralMarket

/-! ## Original-source elementary graphs from the direct completed schedule

The raw candidate and completed coordinates are constructed independently
and identified in the original source graph. Bounded predictable
graph inclusion places the whole gain in the general truncation graph.
-/

open MeasureTheory
open scoped NNReal ProbabilityTheory

open LocalCompletedM2A

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

/-- The bounded gain supplies a raw special candidate, and the original
source's completed coordinates supply its actual integral semantics. -/
noncomputable def elementaryActualLocal
    (source : BoundedSemimartingaleSource S F μ)
    (K : PredictableElementaryStrategy F) (B : NNReal)
    (hB : ∀ ω, K.coefficientAbsSum ω ≤ B) :
    ActualLocallySIntegrableStrategy (realizationModel (unitSource source)) where
  val := elementaryRawCandidate source K B hB
  deterministicallyStopped_isRealized := fun T hT =>
    deterministicallyStoppedGraphWitness_isRealized
      (directElementaryCommonSchedule source K B hB).schedule
      (directElementaryCommonSchedule source K B hB).coefficient
      (directElementaryCommonSchedule source K B hB).coefficient_eq
      (elementaryRawCandidate source K B hB) rfl
      (directElementaryCommonSchedule source K B hB).stoppedGain_eq T hT

end FTAPTheorem42.BoundedSourceIntegralMarket
