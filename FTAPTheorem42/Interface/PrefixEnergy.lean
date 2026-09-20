/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Construction.OriginalGainRealization
import FTAPTheorem42.Stochastic.DS.Lemma410.LocalPrefixL2

/-! # The finite passage-prefix energy estimate -/

namespace FTAPTheorem42.BoundedSourceIntegralMarket
open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal BigOperators
open LocalCompletedM2A PredictableElementaryEmery
variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ Q : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
  [SigmaFiniteFiltration μ F] [SigmaFiniteFiltration Q F]

omit [SigmaFiniteFiltration μ F] in
/-- Stopped components are true L² martingales with a common envelope bound. -/
theorem originalGain_prefix_energy
    (source : BoundedSemimartingaleSource S F μ) (hQμ : Q ≪ μ) (hμQ : μ ≪ Q)
    (hUsual : Filtration.UsualConditions Q F) (Y : OriginalSpecialGain source Q)
    (q : Ω → Real) (hq : MemLp q 2 Q)
    (hBound : ∀ᵐ ω ∂Q, ∀ t, |Y.original.gain t ω| ≤ q ω)
    (c : Real) (hc : 0 ≤ c) (T : NNReal) (hT : 0 < T) :
    let P := absolutePassagePrefix Y.decomposition.N c T
    Martingale P F Q ∧ MemLp (P T) 2 Q ∧
      eLpNorm (P T) 2 Q ≤ ENNReal.ofReal c + 6 * eLpNorm q 2 Q := by
  let : F.IsRightContinuous := hUsual.rightContinuous
  obtain ⟨R, hR⟩ := Y.original.exists_realized source hQμ hμQ
  let E : J1Decomposition R.gain F Q := { Y.decomposition with
    decomposition := by rw [hR]; exact Y.decomposition.decomposition }
  let G := R.componentSource source.rightContinuous E Y.predictable
  have hM : G.martingalePart = Y.decomposition.N :=
    R.componentSource_martingalePart source.rightContinuous E Y.predictable
  have hGain : G.stochasticIntegral = Y.original.gain := hR
  have hZero : G.martingalePart 0 =ᵐ[Q] 0 := by
    rw [hM, Y.decomposition.zeroN]
  have hBound' : ∀ᵐ ω ∂Q, ∀ t, |G.stochasticIntegral t ω| ≤ q ω := by
    rwa [hGain]
  have hResult := LocallySIntegrableStrategy.absolutePassagePrefix_martingale_l2
    G hUsual (by rw [hM]; exact Y.decomposition.leftN) hZero q hq hBound' c hc T hT
  simpa only [hM] using hResult

omit [IsProbabilityMeasure Q] [SigmaFiniteFiltration μ F] [SigmaFiniteFiltration Q F] in
/-- Path regularity and the zero initial value of the same finite prefix. -/
theorem originalGain_prefix_regular
    (source : BoundedSemimartingaleSource S F μ) (Y : OriginalSpecialGain source Q)
    (c : Real) (T : NNReal) :
    (∀ ω t, ContinuousWithinAt (absolutePassagePrefix Y.decomposition.N c T · ω) (Ici t) t) ∧
    absolutePassagePrefix Y.decomposition.N c T 0 =ᵐ[Q] 0 := by
  refine ⟨RightContinuousStoppedMartingale.stoppedProcess_rightContinuous _
    Y.decomposition.rightN, ?_⟩
  filter_upwards [] with ω
  change stoppedProcess Y.decomposition.N _ 0 ω = 0
  rw [stoppedProcess_eq_of_le bot_le, Y.decomposition.zeroN]
  rfl

end FTAPTheorem42.BoundedSourceIntegralMarket
