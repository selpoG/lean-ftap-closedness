/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Construction.OriginalGainRealization
import FTAPTheorem42.Stochastic.Market.Transfer.FiniteRealizedGain
import FTAPTheorem42.Stochastic.Process.ProcessLeftJump

/-! # Finite process-level gains and the internal stopping calculus -/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal
open LocalCompletedM2A PredictableElementaryEmery

variable {Ω : Type*} [MeasurableSpace Ω]
  {S P : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ Q : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
  [SigmaFiniteFiltration μ F] [SigmaFiniteFiltration Q F]
  {source : BoundedSemimartingaleSource S F μ}

/-- The auxiliary tag carries no assertion about integral representation. -/
def OriginalSpecialGain.componentTag (Y : OriginalSpecialGain source Q) :
    SpecialSemimartingaleDecomposition Y.original.gain F Q where
  martingalePart := Y.decomposition.N
  finiteVariationPart := Y.decomposition.A
  martingalePart_isLocalMartingale := Y.decomposition.localMartingale
  finiteVariationPart_isPredictable := Y.predictable
  finiteVariationPart_isLocallyBoundedVariation := Y.decomposition.variationA
  decomposition := Y.decomposition.decomposition

/-- Copy finite regular components into the internal numerical record. -/
noncomputable def FiniteOriginalSpecialGain.componentRecord
    (Y : FiniteOriginalSpecialGain source Q)
    (D : SpecialSemimartingaleDecomposition P F Q) : SIntegrableStrategy D where
  integrand := 0
  stochasticIntegral := Y.original.gain
  martingalePart := Y.decomposition.N
  finiteVariationPart := Y.decomposition.A
  finiteVariationMeasure := 0
  integrand_isPredictable := stronglyMeasurable_zero
  stochasticIntegral_isStronglyAdapted := Y.original.adapted
  stochasticIntegral_isRightContinuous := Y.original.rightContinuous
  martingalePart_isLocalMartingale := Y.decomposition.localMartingale
  martingalePart_isStronglyAdapted := Y.decomposition.adaptedN
  martingalePart_isRightContinuous := Y.decomposition.rightN
  finiteVariationPart_isPredictable := Y.predictable
  finiteVariationPart_isRightContinuous := Y.decomposition.rightA
  finiteVariationPart_isBoundedVariation := Y.boundedVariation
  integral_decomposition := Y.decomposition.decomposition
  source_decomposition := D.decomposition

omit [SigmaFiniteFiltration μ F] in
/-- The process-level graph supplies the actual finite realization separately
from the numerical record. -/
theorem FiniteOriginalSpecialGain.hasFiniteRealizedGain
    (Y : FiniteOriginalSpecialGain source Q) (hQμ : Q ≪ μ) (hμQ : μ ≪ Q) :
    HasFiniteRealizedGain Q F S Y.original.gain := by
  obtain ⟨R, hR⟩ := Y.original.exists_realized source hQμ hμQ
  exact ⟨R, Eventually.of_forall (fun _ t => congrFun (congrFun hR.symm t) _),
    Y.eventuallyConstant⟩

/-- A realized component record admits regular centered coordinates. Only a
common null set is changed in the gain or the martingale component. -/
theorem exists_originalSpecialGain_of_record
    (source : BoundedSemimartingaleSource S F μ) (hQμ : Q ≪ μ) (hμQ : μ ≪ Q)
    {D : SpecialSemimartingaleDecomposition P F Q} (V : SIntegrableStrategy D)
    (hR : ∃ R : RealizedStrategy (ℱ := F) Q S,
      ProcessIndistinguishable Q V.stochasticIntegral R.gain)
    (hML : ProcessHasLeftLimits V.martingalePart) (hM0 : V.martingalePart 0 =ᵐ[Q] 0) :
    ∃ Y : OriginalSpecialGain source Q,
      ProcessIndistinguishable Q V.stochasticIntegral Y.original.gain ∧
      ProcessIndistinguishable Q V.martingalePart Y.decomposition.N := by
  obtain ⟨R, hR⟩ := hR
  let dec : SpecialSemimartingaleDecomposition R.gain F Q := {
    martingalePart := V.martingalePart
    finiteVariationPart := V.finiteVariationPart
    martingalePart_isLocalMartingale := V.martingalePart_isLocalMartingale
    finiteVariationPart_isPredictable := V.finiteVariationPart_isPredictable
    finiteVariationPart_isLocallyBoundedVariation := fun ω =>
      (V.finiteVariationPart_isBoundedVariation ω).locallyBoundedVariationOn
    decomposition := hR.symm.trans V.integral_decomposition }
  let G := dec.zeroInitialUnitSource R.gain_stronglyAdapted R.gain_rightContinuous
    (R.gain_initial_eq_zero S source.rightContinuous)
    V.martingalePart_isStronglyAdapted V.martingalePart_isRightContinuous
    V.finiteVariationPart_isRightContinuous
  let E : J1Decomposition R.gain F Q := {
    N := G.martingalePart
    A := G.finiteVariationPart
    decomposition := G.integral_decomposition
    localMartingale := G.martingalePart_isLocalMartingale
    adaptedN := G.martingalePart_isStronglyAdapted
    rightN := G.martingalePart_isRightContinuous
    leftN := hML.sub (.timeConstant _)
    zeroN := by funext ω; exact sub_self _
    adaptedA := G.finiteVariationPart_isPredictable.stronglyAdapted
    rightA := G.finiteVariationPart_isRightContinuous
    leftA := V.finiteVariationPart_hasLeftLimits.sub (.timeConstant _)
    variationA := G.finiteVariationPart_isLocallyBoundedVariation
    zeroA := by funext ω; exact sub_self _ }
  let Y : OriginalSpecialGain source Q := {
    original := OriginalGain.ofRealized source R hQμ hμQ
    decomposition := E
    predictable := G.finiteVariationPart_isPredictable }
  refine ⟨Y, hR, ?_⟩
  filter_upwards [hM0] with ω hω
  intro t
  change V.martingalePart t ω = V.martingalePart t ω - V.martingalePart 0 ω
  rw [hω, Pi.zero_apply, sub_zero]

end FTAPTheorem42.BoundedSourceIntegralMarket
