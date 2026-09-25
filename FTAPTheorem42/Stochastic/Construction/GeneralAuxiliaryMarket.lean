/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Interface.IntegralClosure
import FTAPTheorem42.Stochastic.Integral.General.L2GainActualRealization
import FTAPTheorem42.Stochastic.DS.Lemma411.LocalHahnStoppedSemantics

/-! # Returning auxiliary actual integrals to the original terminal market

The auxiliary source may vary with the gain and lives under an equivalent
measure. Only the realized gain, rather than its special decomposition, is
transported to the original price and measure.
-/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

open LocalCompletedM2A PredictableElementaryEmery

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ Q : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
  [SigmaFiniteFiltration μ F] [SigmaFiniteFiltration Q F]
  {U : Process Ω} {D : SpecialSemimartingaleDecomposition U F Q}

/-- Every actual transform of an L2-enveloped auxiliary realized gain has
an original-price general integral graph. -/
theorem exists_original_generalGraph_of_auxiliary_actual
    (source : BoundedSemimartingaleSource S F μ)
    (hQμ : Q ≪ μ) (hμQ : μ ≪ Q) (hUsual : Filtration.UsualConditions Q F)
    (R : RealizedStrategy (ℱ := F) Q S)
    (G : LocallySIntegrableStrategy D) (hGain : G.stochasticIntegral = R.gain)
    (hM0 : G.martingalePart 0 = 0) (hML : ProcessHasLeftLimits G.martingalePart)
    (ξ : Ω → Real) (hξ : MemLp ξ 2 Q)
    (hBound : ∀ᵐ ω ∂Q, ∀ t, |G.stochasticIntegral t ω| ≤ ξ ω)
    (V : ActualSIntegrableStrategy (realizationModel G)) :
    ∃ K : Process Ω, IsTruncatedIntegralGraph (unitSource source) K
      V.val.stochasticIntegral := by
  have hS := StronglyAdapted.isStronglyProgressive_of_rightContinuous
    source.stronglyAdapted source.rightContinuous
  obtain ⟨W, hW⟩ := exists_realization_of_actual_over_L2Gain hS source.rightContinuous
    R G hGain hUsual hM0 hML ξ hξ hBound V
  let Z := W.transferMeasure hQμ hμQ S hS
  obtain ⟨K, ⟨w⟩⟩ := exists_realized_truncatedGraph source Z
  exact ⟨K, ⟨{ w with gain_indistinguishable :=
    w.gain_indistinguishable.trans (hμQ.ae_le hW) }⟩⟩

/-- A finite-horizon auxiliary actual strategy returns its own terminal
value, with the same admissibility level, to the original market. -/
theorem auxiliary_actual_horizon_mem_original_terminalClaims
    (source : BoundedSemimartingaleSource S F μ)
    (hQμ : Q ≪ μ) (hμQ : μ ≪ Q) (hUsual : Filtration.UsualConditions Q F)
    (R : RealizedStrategy (ℱ := F) Q S)
    (G : LocallySIntegrableStrategy D) (hGain : G.stochasticIntegral = R.gain)
    (hM0 : G.martingalePart 0 = 0) (hML : ProcessHasLeftLimits G.martingalePart)
    (ξ : Ω → Real) (hξ : MemLp ξ 2 Q)
    (hBound : ∀ᵐ ω ∂Q, ∀ t, |G.stochasticIntegral t ω| ≤ ξ ω)
    (V : ActualSIntegrableStrategy (realizationModel G)) (T : NNReal)
    {a : Real} (ha : 0 < a)
    (hLower : ∀ t, AELowerBoundedBy Q (-a) (V.val.stochasticIntegral t))
    (hTerminal : ∀ᵐ ω ∂Q, ∀ t, T ≤ t →
      V.val.stochasticIntegral t ω = V.val.stochasticIntegral T ω) :
    V.val.stochasticIntegral T ∈ truncatedTerminalClaimsBy (unitSource source) a := by
  obtain ⟨K, hK⟩ := exists_original_generalGraph_of_auxiliary_actual source hQμ hμQ
    hUsual R G hGain hM0 hML ξ hξ hBound V
  refine ⟨ha, K, V.val.stochasticIntegral, hK, fun t => hμQ.ae_le (hLower t), ?_⟩
  filter_upwards [hμQ.ae_le hTerminal] with ω hω
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop T] with t ht
  exact (hω t ht).symm

end FTAPTheorem42.BoundedSourceIntegralMarket

namespace FTAPTheorem42.BoundedSourceIntegralMarket

/-! ## Controlled intrinsic Hahn gains in the original general market

One source schedule generates the unit actual graph and its finite-stop
Hahn restriction. Its martingale estimate and original-price graph concern
that same gain. Auxiliary sources may vary between applications.
-/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

open LocalCompletedM2A PredictableElementaryEmery

variable {Ω : Type*} [MeasurableSpace Ω]
  {S U : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ Q : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
  [SigmaFiniteFiltration μ F] [SigmaFiniteFiltration Q F]
  {D : SpecialSemimartingaleDecomposition U F Q}

/-- Construct the finite-stop Hahn gain, prove its component estimates and
return its general integral graph to the original price and probability.
The input bound concerns the auxiliary source martingale; it is uniform in
the Hahn set and the elementary tests. -/
theorem original_hahn_transform_component_bounds
    (source : BoundedSemimartingaleSource S F μ)
    (hQμ : Q ≪ μ) (hμQ : μ ≪ Q) (hUsual : Filtration.UsualConditions Q F)
    (R : RealizedStrategy (ℱ := F) Q S)
    (G : LocallySIntegrableStrategy D) (hGain : G.stochasticIntegral = R.gain)
    (hUnit : G.integrand = PredictableProcess.unit)
    (hZero : G.stochasticIntegral 0 =ᵐ[Q] 0)
    (hM0 : G.martingalePart 0 = 0) (hML : ProcessHasLeftLimits G.martingalePart)
    (ξ : Ω → Real) (hξ : MemLp ξ 2 Q)
    (hEnvelope : ∀ᵐ ω ∂Q, ∀ t, |G.stochasticIntegral t ω| ≤ ξ ω)
    (T : NNReal) (hT : 0 < T) (b : Real)
    (hBound : ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
      (∫ ω, elementaryEmeryTestError G.martingalePart 0 J T ω ∂Q) ≤ b) :
    letI := hUsual.rightContinuous
    let A := actualUnitSource (directScheduleOfL2Gain G hUsual hM0 hML ξ hξ hEnvelope) hUnit hZero
    let V := actualHahnOfDeterministicStop hML A T hT
    (∃ K : Process Ω, IsTruncatedIntegralGraph (unitSource source) K V.val.stochasticIntegral) ∧
    (∀ᵐ ω ∂Q, ∀ a c : NNReal, a ≤ c →
      0 ≤ V.val.finiteVariationPart c ω - V.val.finiteVariationPart a ω ∧
      G.finiteVariationPart (min c T) ω - G.finiteVariationPart (min a T) ω ≤
        V.val.finiteVariationPart c ω - V.val.finiteVariationPart a ω) ∧
    (∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
      (∫ ω, elementaryEmeryTestError V.val.martingalePart 0 J T ω ∂Q) ≤ b) ∧
    (∫ ω, FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
      V.val.martingalePart T ω ∂Q) ≤ b := by
  let _ := hUsual.rightContinuous
  let A := actualUnitSource (directScheduleOfL2Gain G hUsual hM0 hML ξ hξ hEnvelope) hUnit hZero
  let V := actualHahnOfDeterministicStop hML A T hT
  have hA : ∀ t ω, |A.val.integrand t ω| ≤ 1 := by
    intro t ω
    change |G.integrand t ω| ≤ 1
    rw [hUnit]
    norm_num [PredictableProcess.unit]
  refine ⟨exists_original_generalGraph_of_auxiliary_actual source hQμ hμQ hUsual
    R G hGain hM0 hML ξ hξ hEnvelope V, ?_⟩
  exact actualHahnOfDeterministicStop_component_bounds hML A hA T hT b hBound

end FTAPTheorem42.BoundedSourceIntegralMarket
