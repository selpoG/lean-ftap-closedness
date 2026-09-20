/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Construction.FiniteGainRecords
import FTAPTheorem42.Stochastic.Integral.Local.Calculus.DirectStopping

/-! # Finite stopping of an original-price special gain -/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal
open PredictableElementaryEmery

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ Q : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
  [SigmaFiniteFiltration μ F] [SigmaFiniteFiltration Q F]

/-- Stop a gain and the same two components at one finite horizon. -/
theorem originalSpecialGain_finiteStop
    (source : BoundedSemimartingaleSource S F μ)
    (hQμ : Q ≪ μ) (hμQ : μ ≪ Q)
    (Y : OriginalSpecialGain source Q) (T : NNReal) (hT : 0 < T) :
    ∃ U : FiniteOriginalSpecialGain source Q,
      U.original.gain = (fun t ω => Y.original.gain (min t T) ω) ∧
      U.decomposition.N = (fun t ω => Y.decomposition.N (min t T) ω) ∧
      U.decomposition.A = (fun t ω => Y.decomposition.A (min t T) ω) := by
  obtain ⟨R, hR⟩ := Y.original.exists_realized source hQμ hμQ
  let E : J1Decomposition R.gain F Q :=
    { Y.decomposition with decomposition := by rw [hR]; exact Y.decomposition.decomposition }
  have hEP : IsStronglyPredictable F E.A := Y.predictable
  let G := R.componentSource source.rightContinuous E hEP
  let V := G.deterministicallyStopped T hT
  have hM : V.martingalePart = (fun t ω => E.N (min t T) ω) := by
    change (fun t ω => G.martingalePart (min t T) ω) = _
    rw [RealizedStrategy.componentSource_martingalePart]
  have hA : V.finiteVariationPart = (fun t ω => E.A (min t T) ω) := by
    change (fun t ω => G.finiteVariationPart (min t T) ω) = _
    rw [RealizedStrategy.componentSource_finiteVariationPart]
  have hS := StronglyAdapted.isStronglyProgressive_of_rightContinuous
    source.stronglyAdapted source.rightContinuous
  let R' := R.deterministicallyStop S hS source.rightContinuous T
  let O := OriginalGain.ofRealized source R' hQμ hμQ
  have hX : O.gain = V.stochasticIntegral := by
    funext t ω
    exact R.deterministicallyStop_gain_apply S hS source.rightContinuous T t ω
  let E' : J1Decomposition O.gain F Q := {
    N := V.martingalePart
    A := V.finiteVariationPart
    decomposition := by rw [hX]; exact V.integral_decomposition
    localMartingale := V.martingalePart_isLocalMartingale
    adaptedN := V.martingalePart_isStronglyAdapted
    rightN := V.martingalePart_isRightContinuous
    leftN := by
      rw [hM]
      exact E.leftN.deterministicallyStopped T
    zeroN := by
      rw [hM]
      funext ω
      change E.N (min 0 T) ω = 0
      rw [min_eq_left (show (0 : NNReal) ≤ T from bot_le), E.zeroN]
      rfl
    adaptedA := V.finiteVariationPart_isPredictable.stronglyAdapted
    rightA := V.finiteVariationPart_isRightContinuous
    leftA := by rw [hA]; exact E.leftA.deterministicallyStopped T
    variationA := fun ω => (V.finiteVariationPart_isBoundedVariation ω).locallyBoundedVariationOn
    zeroA := by
      rw [hA]
      funext ω
      change E.A (min 0 T) ω = 0
      rw [min_eq_left (show (0 : NNReal) ≤ T from bot_le), E.zeroA]
      rfl }
  let U : FiniteOriginalSpecialGain source Q := {
    original := O
    decomposition := E'
    predictable := V.finiteVariationPart_isPredictable
    boundedVariation := V.finiteVariationPart_isBoundedVariation
    eventuallyConstant := ⟨T, by
      filter_upwards [] with ω
      intro t ht
      rw [hX]
      change R.gain (min t T) ω = R.gain (min T T) ω
      rw [min_eq_right ht, min_self]⟩ }
  refine ⟨U, ?_, hM, hA⟩
  rw [hX]
  change (fun t ω => R.gain (min t T) ω) = _
  rw [hR]

end FTAPTheorem42.BoundedSourceIntegralMarket
