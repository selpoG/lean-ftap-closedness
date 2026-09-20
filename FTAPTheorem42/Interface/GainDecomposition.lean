/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Construction.OriginalGainRealization
import FTAPTheorem42.Stochastic.Topology.Emery.GainSemimartingale
import FTAPTheorem42.Stochastic.Decomposition.Source.GlobalSquareIntegrableSpecialDecomposition

/-! # Special decomposition under an L² gain envelope -/

namespace FTAPTheorem42.BoundedSourceIntegralMarket
open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal BigOperators
open LocalCompletedM2A PredictableElementaryEmery
variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ Q : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
  [SigmaFiniteFiltration μ F] [SigmaFiniteFiltration Q F]

omit [SigmaFiniteFiltration μ F] in
/-- An L²-bounded original gain has regular, centered special components. -/
theorem originalGain_specialDecomposition
    (source : BoundedSemimartingaleSource S F μ) (hQμ : Q ≪ μ) (hμQ : μ ≪ Q)
    (Y : OriginalGain source) (q : Ω → Real) (hq : MemLp q 2 Q)
    (hBound : ∀ᵐ ω ∂Q, ∀ t, |Y.gain t ω| ≤ ‖q ω‖) :
    ∃ E : J1Decomposition Y.gain F Q, IsStronglyPredictable F E.A := by
  let sourceQ := source.ofMutuallyAbsolutelyContinuous hμQ hQμ
  obtain ⟨R, hR⟩ := Y.exists_realized source hQμ hμQ
  have hS := StronglyAdapted.isStronglyProgressive_of_rightContinuous
    source.stronglyAdapted source.rightContinuous
  have hSemi : IsSemimartingale Y.gain F Q := by
    rw [← hR]
    exact R.gain_isSemimartingale S hS source.rightContinuous
      source.hasLeftLimits sourceQ.isSemimartingale
  obtain ⟨D⟩ :=
    HorizonFactorialGrid.exists_squareIntegrableSemimartingaleGlobalSpecialDecompositionData
      q hq sourceQ.usualConditions hSemi Y.adapted Y.rightContinuous Y.leftLimits hBound
  let G := D.toSpecialSemimartingaleDecomposition.zeroInitialUnitSource
    Y.adapted Y.rightContinuous (hQμ.ae_le Y.zero)
    D.M_isStronglyAdapted D.M_rightContinuous D.A_rightContinuous
  let E : J1Decomposition Y.gain F Q := {
    N := G.martingalePart
    A := G.finiteVariationPart
    decomposition := G.integral_decomposition
    localMartingale := G.martingalePart_isLocalMartingale
    adaptedN := G.martingalePart_isStronglyAdapted
    rightN := G.martingalePart_isRightContinuous
    leftN := D.M_leftLimits.sub (.timeConstant _)
    zeroN := by funext ω; exact sub_self _
    adaptedA := G.finiteVariationPart_isPredictable.stronglyAdapted
    rightA := G.finiteVariationPart_isRightContinuous
    leftA := D.A_leftLimits.sub (.timeConstant _)
    variationA := G.finiteVariationPart_isLocallyBoundedVariation
    zeroA := by funext ω; exact sub_self _ }
  exact ⟨E, G.finiteVariationPart_isPredictable⟩

end FTAPTheorem42.BoundedSourceIntegralMarket
