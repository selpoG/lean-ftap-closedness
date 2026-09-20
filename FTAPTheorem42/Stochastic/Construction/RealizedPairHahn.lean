/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.Emery.TerminalSwitching

import FTAPTheorem42.Stochastic.Construction.GeneralAuxiliaryMarket
import FTAPTheorem42.Stochastic.Market.Source.RealizedSpecialSource

/-! # Hahn gains retaining a prescribed realized special decomposition -/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

open LocalCompletedM2A PredictableElementaryEmery

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ Q : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
  [SigmaFiniteFiltration μ F] [SigmaFiniteFiltration Q F]

/-- The normalized components of a realized gain supply the auxiliary unit
source. The generated Hahn gain keeps these components for its variation
comparison and returns to the original general graph. -/
theorem original_realized_hahn_component_bounds
    (source : BoundedSemimartingaleSource S F μ)
    (hQμ : Q ≪ μ) (hμQ : μ ≪ Q) (hUsual : Filtration.UsualConditions Q F)
    (R : RealizedStrategy (ℱ := F) Q S) (D : J1Decomposition R.gain F Q)
    (hAP : IsStronglyPredictable F D.A)
    (ξ : Ω → Real) (hξ : MemLp ξ 2 Q)
    (hEnvelope : ∀ᵐ ω ∂Q, ∀ t, |R.gain t ω| ≤ ξ ω)
    (T : NNReal) (hT : 0 < T) (b : Real)
    (hBound : ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
      (∫ ω, elementaryEmeryTestError D.N 0 J T ω ∂Q) ≤ b) :
    letI := hUsual.rightContinuous
    let G := R.componentSource source.rightContinuous D hAP
    let hGL := R.componentSource_martingalePart_hasLeftLimits source.rightContinuous D hAP
    ∃ A : ActualLocallySIntegrableStrategy (realizationModel G), A.val = G ∧
      let V := actualHahnOfDeterministicStop hGL A T hT
      (∃ K : Process Ω, IsTruncatedIntegralGraph (unitSource source) K V.val.stochasticIntegral) ∧
      (∀ᵐ ω ∂Q, ∀ a c : NNReal, a ≤ c →
        0 ≤ V.val.finiteVariationPart c ω - V.val.finiteVariationPart a ω ∧
        D.A (min c T) ω - D.A (min a T) ω ≤
          V.val.finiteVariationPart c ω - V.val.finiteVariationPart a ω) ∧
      (∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
        (∫ ω, elementaryEmeryTestError V.val.martingalePart 0 J T ω ∂Q) ≤ b) ∧
      (∫ ω, FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        V.val.martingalePart T ω ∂Q) ≤ b := by
  let _ := hUsual.rightContinuous
  let G := R.componentSource source.rightContinuous D hAP
  have hM0 : G.martingalePart 0 = 0 := by
    rw [RealizedStrategy.componentSource_martingalePart, D.zeroN]
  have hGL := R.componentSource_martingalePart_hasLeftLimits source.rightContinuous D hAP
  have hUnit : G.integrand = PredictableProcess.unit := rfl
  have hZero : G.stochasticIntegral 0 =ᵐ[Q] 0 := R.gain_initial_eq_zero S source.rightContinuous
  let A := actualUnitSource (directScheduleOfL2Gain G hUsual hM0 hGL ξ hξ hEnvelope) hUnit hZero
  refine ⟨A, rfl, ?_⟩
  have h := original_hahn_transform_component_bounds source hQμ hμQ hUsual
    R G rfl hUnit hZero hM0 hGL ξ hξ hEnvelope T hT b
    (by simpa only [G, RealizedStrategy.componentSource_martingalePart] using hBound)
  simpa only [G, RealizedStrategy.componentSource_finiteVariationPart] using h

/-! ## Original-price Hahn gains for differences of prescribed components -/

/-- A concrete Hahn gain for this ordered pair, with its original-market
graph, variation improvement and uniform martingale bounds. -/
def OriginalPairHahnControl
    (source : BoundedSemimartingaleSource S F μ)
    (hUsual : Filtration.UsualConditions Q F)
    (R V : RealizedStrategy (ℱ := F) Q S)
    (D : J1Decomposition R.gain F Q) (E : J1Decomposition V.gain F Q)
    (hDP : IsStronglyPredictable F D.A) (hEP : IsStronglyPredictable F E.A)
    (T : NNReal) (hT : 0 < T) (b : Real) : Prop :=
    letI := hUsual.rightContinuous
    let hS := StronglyAdapted.isStronglyProgressive_of_rightContinuous
      source.stronglyAdapted source.rightContinuous
    let W := R.sub hS V
    let B := R.subDecomposition hS V D E
    let hBP : IsStronglyPredictable F B.A := hDP.add hEP.neg
    let G := W.componentSource source.rightContinuous B hBP
    let hGL := W.componentSource_martingalePart_hasLeftLimits source.rightContinuous B hBP
    ∃ L : ActualLocallySIntegrableStrategy (realizationModel G), L.val = G ∧
      let X := actualHahnOfDeterministicStop hGL L T hT
      (∃ K : Process Ω, IsTruncatedIntegralGraph (unitSource source) K X.val.stochasticIntegral) ∧
      (∀ᵐ ω ∂Q, ∀ a c : NNReal, a ≤ c →
        0 ≤ X.val.finiteVariationPart c ω - X.val.finiteVariationPart a ω ∧
        (D.A - E.A) (min c T) ω - (D.A - E.A) (min a T) ω ≤
          X.val.finiteVariationPart c ω - X.val.finiteVariationPart a ω) ∧
      (∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
        (∫ ω, elementaryEmeryTestError X.val.martingalePart 0 J T ω ∂Q) ≤ b) ∧
      (∫ ω, FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        X.val.martingalePart T ω ∂Q) ≤ b ∧
      (∫ ω, FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope
        (D.N - E.N) T ω ∂Q) ≤ b

/-- The pairwise martingale test error supplies a controlled Hahn gain in
the original general graph. The variation comparison uses the exact same
difference of the supplied components. -/
theorem original_pair_hahn_component_bounds
    (source : BoundedSemimartingaleSource S F μ)
    (hQμ : Q ≪ μ) (hμQ : μ ≪ Q) (hUsual : Filtration.UsualConditions Q F)
    (R V : RealizedStrategy (ℱ := F) Q S)
    (D : J1Decomposition R.gain F Q) (E : J1Decomposition V.gain F Q)
    (hDP : IsStronglyPredictable F D.A) (hEP : IsStronglyPredictable F E.A)
    (ξ : Ω → Real) (hξ : MemLp ξ 2 Q)
    (hR : ∀ᵐ ω ∂Q, ∀ t, |R.gain t ω| ≤ ξ ω)
    (hV : ∀ᵐ ω ∂Q, ∀ t, |V.gain t ω| ≤ ξ ω)
    (T : NNReal) (hT : 0 < T) (b : Real)
    (hBound : ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
      (∫ ω, elementaryEmeryTestError D.N E.N J T ω ∂Q) ≤ b) :
    OriginalPairHahnControl source hUsual R V D E hDP hEP T hT b := by
  unfold OriginalPairHahnControl
  let _ := hUsual.rightContinuous
  let hS := StronglyAdapted.isStronglyProgressive_of_rightContinuous
    source.stronglyAdapted source.rightContinuous
  let W := R.sub hS V
  let B := R.subDecomposition hS V D E
  have hBP : IsStronglyPredictable F B.A := hDP.add hEP.neg
  have hEnvelope : ∀ᵐ ω ∂Q, ∀ t, |W.gain t ω| ≤ ((2 : Real) • ξ) ω := by
    filter_upwards [hR, hV] with ω hr hv
    intro t
    rw [RealizedStrategy.sub_gain]
    change |R.gain t ω - V.gain t ω| ≤ 2 * ξ ω
    calc
      _ ≤ |R.gain t ω| + |V.gain t ω| := abs_sub _ _
      _ ≤ ξ ω + ξ ω := add_le_add (hr t) (hv t)
      _ = _ := (two_mul _).symm
  have hBTest : ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
      (∫ ω, elementaryEmeryTestError B.N 0 J T ω ∂Q) ≤ b := by
    intro J
    rw [RealizedStrategy.subDecomposition_N, elementaryEmeryTestError_sub_zero]
    exact hBound J
  have h := original_realized_hahn_component_bounds source hQμ hμQ hUsual W B hBP
    ((2 : Real) • ξ) (hξ.const_smul 2) hEnvelope T hT b hBTest
  obtain ⟨L, hL, hGraph, hInc, hTest, hCap⟩ := h
  refine ⟨L, hL, hGraph, ?_, hTest, hCap, ?_⟩
  · simpa only [B, RealizedStrategy.subDecomposition_A] using hInc
  · have hZero : D.N 0 =ᵐ[Q] E.N 0 := by rw [D.zeroN, E.zeroN]
    have hEq := elementaryEmeryTestError_horizonUnit (F := F) hZero T
    change _ =ᵐ[Q]
      FactorialChronologicalGrid.cappedFiniteHorizonAbsoluteEnvelope (D.N - E.N) T at hEq
    rw [← integral_congr_ae hEq]
    exact hBound _

end FTAPTheorem42.BoundedSourceIntegralMarket
