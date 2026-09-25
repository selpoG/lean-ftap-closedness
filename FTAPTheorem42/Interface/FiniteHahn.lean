/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Interface.GainData
import FTAPTheorem42.Interface.HahnData
import FTAPTheorem42.Stochastic.Construction.OriginalGainRealization
import FTAPTheorem42.Stochastic.Construction.OriginalHahnImprovement

/-! # Finite Hahn improvements for two specified original gains -/

namespace FTAPTheorem42.BoundedSourceIntegralMarket
open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal
open LocalCompletedM2A PredictableElementaryEmery
variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ Q : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
  [SigmaFiniteFiltration μ F] [SigmaFiniteFiltration Q F]

/-- A finite test estimate controls both orientations of the Hahn trade.
No Cauchy sequence or maximality hypothesis enters this construction. -/
theorem originalGain_finiteHahn
    (source : BoundedSemimartingaleSource S F μ) (hQμ : Q ≪ μ) (hμQ : μ ≪ Q)
    (hUsual : Filtration.UsualConditions Q F) (Y Z : OriginalSpecialGain source Q)
    (q : Ω → Real) (hq : MemLp q 2 Q)
    (hY : ∀ᵐ ω ∂Q, ∀ t, |Y.original.gain t ω| ≤ q ω)
    (hZ : ∀ᵐ ω ∂Q, ∀ t, |Z.original.gain t ω| ≤ q ω)
    (hYL : ∀ᵐ ω ∂Q, ∀ t, (-1 : Real) ≤ Y.original.gain t ω)
    (hZL : ∀ᵐ ω ∂Q, ∀ t, (-1 : Real) ≤ Z.original.gain t ω)
    (T : NNReal) (hT : 0 < T) (b δ : Real) (hδ : 0 ≤ δ)
    (hForward : ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
      (∫ ω, elementaryEmeryTestError Y.decomposition.N Z.decomposition.N J T ω ∂Q) ≤ b)
    (hReverse : ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
      (∫ ω, elementaryEmeryTestError Z.decomposition.N Y.decomposition.N J T ω ∂Q) ≤ b) :
    OriginalPairHahnOrientedImprovement source Y.original.gain Z.original.gain
      Y.decomposition Z.decomposition T b δ := by
  obtain ⟨R, hR⟩ := Y.original.exists_realized source hQμ hμQ
  obtain ⟨V, hV⟩ := Z.original.exists_realized source hQμ hμQ
  let D : J1Decomposition R.gain F Q := { Y.decomposition with
    decomposition := by rw [hR]; exact Y.decomposition.decomposition }
  let E : J1Decomposition V.gain F Q := { Z.decomposition with
    decomposition := by rw [hV]; exact Z.decomposition.decomposition }
  have hRB : ∀ᵐ ω ∂Q, ∀ t, |R.gain t ω| ≤ q ω := by rwa [hR]
  have hVB : ∀ᵐ ω ∂Q, ∀ t, |V.gain t ω| ≤ q ω := by rwa [hV]
  have hRL : ∀ᵐ ω ∂Q, ∀ t, (-1 : Real) ≤ R.gain t ω := by rwa [hR]
  have hVL : ∀ᵐ ω ∂Q, ∀ t, (-1 : Real) ≤ V.gain t ω := by rwa [hV]
  have hF := original_pair_hahn_component_bounds source hQμ hμQ hUsual R V D E
    Y.predictable Z.predictable q hq hRB hVB T hT b hForward
  have hB := original_pair_hahn_component_bounds source hQμ hμQ hUsual V R E D
    Z.predictable Y.predictable q hq hVB hRB T hT b hReverse
  have hFC := original_pair_hahn_finiteTerminal source hQμ hμQ hUsual R V D E
    Y.predictable Z.predictable hRL hVL T hT b hF hδ
  have hBC := original_pair_hahn_finiteTerminal source hQμ hμQ hUsual V R E D
    Z.predictable Y.predictable hVL hRL T hT b hB hδ
  have h := original_pair_hahn_orientedImprovement source hUsual R V D E
    Y.predictable Z.predictable T hT b δ hFC hBC
  have h' : ∃ P : OriginalHahnImprovement source Q V.gain
      (Y.decomposition.N - Z.decomposition.N) (Y.decomposition.A - Z.decomposition.A) T b δ,
    ∃ P' : OriginalHahnImprovement source Q R.gain
      (Z.decomposition.N - Y.decomposition.N) (Z.decomposition.A - Y.decomposition.A) T b δ,
      ∀ α : Real,
        α < Q.real {ω | α < finiteHorizonPathVariation (Y.decomposition.A - Z.decomposition.A)
          (fun ω a c ha hc => by
            simpa only [Pi.sub_apply, sub_eq_add_neg] using
              boundedVariationOn_add (Y.decomposition.variationA ω a c ha hc)
                (boundedVariationOn_neg (Z.decomposition.variationA ω a c ha hc))) T ω} →
        α / 2 < Q.real {ω | α / 2 < P.finiteVariation T ω} ∨
          α / 2 < Q.real {ω | α / 2 < P'.finiteVariation T ω} := h
  rw [hR, hV] at h'
  exact h'

end FTAPTheorem42.BoundedSourceIntegralMarket
