/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Construction.FiniteGainRecords
import FTAPTheorem42.Stochastic.DS.Lemma48.FiniteRealizedTail
import FTAPTheorem42.Stochastic.DS.Lemma48.TailHorizon
import FTAPTheorem42.Foundations.Passage

/-! # Finite normalization in the original-price market

The result constructs one normalized gain at a prescribed positive scale.
It assumes a maximal bound on the input family, not NFLVR, and makes no
claim that convex tail passage probabilities tend to zero.
-/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal BigOperators
open PredictableElementaryEmery SIntegrableProcessStoppingCalculus

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ Q : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
  [SigmaFiniteFiltration μ F] [SigmaFiniteFiltration Q F]

/-- A large finite convex-tail event produces a unit-admissible gain with
unit L² envelope norm and an amplified martingale event. All cutoffs precede
the convex weights. -/
theorem originalGain_finiteTail_normalization
    (source : BoundedSemimartingaleSource S F μ)
    (hQμ : Q ≪ μ) (hμQ : μ ≪ Q) (hUsual : Filtration.UsualConditions Q F)
    (H : Nat → FiniteOriginalSpecialGain source Q)
    (q : Ω → Real) (hq : MemLp q 2 Q)
    (hLower : ∀ i, ∀ᵐ ω ∂Q, ∀ t, (-1 : Real) ≤ (H i).original.gain t ω)
    (hBound : ∀ i, ∀ᵐ ω ∂Q, ∀ t, |(H i).original.gain t ω| ≤ ‖q ω‖)
    (hMaximal : ∀ η : Real, 0 < η → ∃ R : Real, 0 ≤ R ∧ ∀ i,
      Q {ω | ENNReal.ofReal R < ⨆ t : NNReal,
        ENNReal.ofReal |(H i).decomposition.N t ω|} ≤ ENNReal.ofReal η) :
    ∀ ε : Real, 0 < ε → ∃ N : Real, 0 ≤ N ∧
      ∀ δ : Real, 0 < δ → δ ≤ ε / 4 → ∃ c₀ : Real, 0 ≤ c₀ ∧
        ∀ (w : TailConvexWeights 0) (c : Real), c₀ ≤ c →
          ε < Q.real (convexTailPassageEvent (fun i => (H i).decomposition.N) w c ε) →
          ∃ Y : OriginalSpecialGain source Q, Y.Normalized ∧
            ε / 2 < Q.real {ω |
              ENNReal.ofReal (((1 + N) * δ)⁻¹ * (ε / 2)) <
                ⨆ t : NNReal, ENNReal.ofReal |Y.decomposition.N t ω|} := by
  let _ := hUsual.rightContinuous
  let D := (H 0).toOriginalSpecialGain.componentTag
  let V := fun i => (H i).componentRecord D
  let C := SIntegrableStrategy.processStoppingCalculus D
  have hS := StronglyAdapted.isStronglyProgressive_of_rightContinuous
    source.stronglyAdapted source.rightContinuous
  have hV i : HasFiniteRealizedGain Q F S (V i).stochasticIntegral :=
    (H i).hasFiniteRealizedGain hQμ hμQ
  intro ε hε
  obtain ⟨N, hN, hGainCap⟩ := exists_lemma48CommonGainCap_measureReal_le
    V q hq (ε / 4) (by positivity) hBound
  have haN : 0 < (1 : Real) + N := by linarith
  refine ⟨N, hN, ?_⟩
  intro δ hδ hδ_le
  obtain ⟨c₀, hc₀, hThreshold⟩ := exists_lemma48PassageThreshold_with_normalizedGainEnvelope
    V q hq δ N 1 hδ haN hMaximal
  refine ⟨c₀, hc₀, fun w c hc hHigh => ?_⟩
  let weight := w.coeff
  let n := w.rangeSize
  have hWeight := w.coeff_nonneg_on_rangeSize
  have hSum := w.sum_coeff_rangeSize_eq_one
  obtain ⟨hActive, hG, hNorm⟩ := hThreshold weight n c hc hWeight hSum
  let R := C.lemma48NormalizedTailConvexStrategy V weight n c N δ ε 1
  have hReal := C.lemma48NormalizedTailConvexStrategy_hasFiniteRealizedGain
    hS source.rightContinuous V hV weight n c N δ ε 1
  have hML := C.lemma48NormalizedTailConvexStrategy_martingalePart_hasLeftLimits
    V weight n c N δ ε 1 (fun i => (H i).decomposition.leftN)
  have hM0 := C.lemma48NormalizedTailConvexStrategy_martingalePart_zero V weight n c N δ ε 1
  obtain ⟨Y, hYX, hYM⟩ := exists_originalSpecialGain_of_record source hQμ hμQ R
    (by obtain ⟨R, hR, _⟩ := hReal; exact ⟨R, hR⟩) hML hM0
  have hLow := C.lemma48NormalizedTailConvexStrategy_admissible
    V weight n c N δ ε 1 hδ haN hWeight hLower
  have hEnvelope := C.lemma48NormalizedTailConvexStrategy_gain_le_envelope
    V weight n c N δ ε 1 q (mul_pos haN hδ) hWeight hBound
  have hNormalized : Y.Normalized := by
    refine ⟨?_, lemma48NormalizedTailGainEnvelope V weight n c q N δ 1, hG, ?_, hNorm⟩
    · filter_upwards [hLow, hYX] with ω hω hEq
      intro t
      rw [← hEq t]
      exact hω t
    · filter_upwards [hEnvelope, hYX] with ω hω hEq
      intro t
      rw [← hEq t]
      exact hω t
  have hRaw : ε < Q.real (C.lemma48TailMartingalePassageFiniteEvent V weight n c ε) := by
    have hM : (C.lemma48TailConvexStrategy V weight n c).martingalePart =
        w.applyVector (fun i => absolutePassageTail (H i).decomposition.N c) := by
      rw [direct_tail_martingale_eq]
      funext t ω
      rw [TailConvexWeights.applyVector_process_apply]
      exact congrFun (w.apply_eq_sum_coeff_superset w.support_subset_rangeSize _) ω
    change ε < Q.real {ω | absoluteStrictHittingAfter
      (C.lemma48TailConvexStrategy V weight n c).martingalePart ε ω ≠ ⊤}
    rw [hM]
    exact hHigh
  have hRetained := C.measureReal_lemma48NormalizedMartingaleHighEvent_gt
    V weight n c N δ ε 1 ε (ε / 4) δ (mul_pos haN hδ) hε hRaw hGainCap hActive
  have hHighR : ε / 2 < Q.real {ω |
      ENNReal.ofReal (((1 + N) * δ)⁻¹ * (ε / 2)) <
        ⨆ t : NNReal, ENNReal.ofReal |R.martingalePart t ω|} :=
    (by linarith : ε / 2 ≤ ε - ε / 4 - δ).trans_lt hRetained
  refine ⟨Y, hNormalized, ?_⟩
  have hEvents : {ω | ENNReal.ofReal (((1 + N) * δ)⁻¹ * (ε / 2)) <
        ⨆ t : NNReal, ENNReal.ofReal |R.martingalePart t ω|} =ᵐ[Q]
      {ω | ENNReal.ofReal (((1 + N) * δ)⁻¹ * (ε / 2)) <
        ⨆ t : NNReal, ENNReal.ofReal |Y.decomposition.N t ω|} := by
    filter_upwards [hYM] with ω hω
    simp only [hω]
  rwa [measureReal_congr hEvents] at hHighR

end FTAPTheorem42.BoundedSourceIntegralMarket
