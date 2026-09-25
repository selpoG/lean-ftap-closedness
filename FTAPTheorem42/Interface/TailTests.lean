/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Interface.TailNormalization
import FTAPTheorem42.Stochastic.DS.Lemma49.ElementaryTest

/-! # Finite convex-tail test estimates

The energy and jump estimates leave the tail-passage probability explicit.
Its decay is established by the main Lemma 4.8 argument.
-/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal BigOperators
open SIntegrableProcessStoppingCalculus

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ Q : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
  [SigmaFiniteFiltration Q F]

/-- The same cutoff controls every finite convex weight, horizon and test;
the remaining passage probability is not absorbed into an assumption. -/
theorem originalGain_finiteTail_test_estimate
    (source : BoundedSemimartingaleSource S F μ)
    (hUsual : Filtration.UsualConditions Q F)
    (H : Nat → FiniteOriginalSpecialGain source Q)
    (q : Ω → Real) (hq : MemLp q 2 Q)
    (hBound : ∀ i, ∀ᵐ ω ∂Q, ∀ t, |(H i).original.gain t ω| ≤ ‖q ω‖)
    (hMaximal : ∀ η : Real, 0 < η → ∃ R : Real, 0 ≤ R ∧ ∀ i,
      Q {ω | ENNReal.ofReal R < ⨆ t : NNReal,
        ENNReal.ofReal |(H i).decomposition.N t ω|} ≤ ENNReal.ofReal η) :
    ∀ η : Real, 0 < η → ∃ c₀ : Real, 0 ≤ c₀ ∧
      ∀ (w : TailConvexWeights 0) (c : Real), c₀ ≤ c →
        ∀ T : NNReal, 0 < T → ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
          (∫ ω, elementaryEmeryTestError
            (w.applyVector (fun i => absolutePassageTail (H i).decomposition.N c)) 0 J T ω ∂Q) ≤
              4 * η + Q.real (convexTailPassageEvent (fun i => (H i).decomposition.N) w c η) := by
  let _ := hUsual.rightContinuous
  let D := (H 0).toOriginalSpecialGain.componentTag
  let V := fun i => (H i).componentRecord D
  let C := SIntegrableStrategy.processStoppingCalculus D
  intro η hη
  obtain ⟨c₀, hc₀, hJump⟩ := C.exists_lemma49TailMartingaleJumpEnvelope_threshold
    hUsual V q hq (fun i => (H i).decomposition.leftN) hBound hMaximal η hη
  refine ⟨c₀, hc₀, fun w c hc T hT J => ?_⟩
  obtain ⟨ξ, hξ, hξNonneg, hξJump, hξNorm⟩ :=
    hJump w.coeff w.rangeSize c hc w.coeff_nonneg_on_rangeSize w.sum_coeff_rangeSize_eq_one T hT
  have hEstimate := integral_lemma49_tail_test_le V w.coeff w.rangeSize c η hη.le T
    (fun i => (H i).decomposition.leftN) ξ hξ hξNonneg hξJump η hη.le hξNorm J
  have hM : (C.lemma48TailConvexStrategy V w.coeff w.rangeSize c).martingalePart =
      w.applyVector (fun i => absolutePassageTail (H i).decomposition.N c) := by
    rw [direct_tail_martingale_eq]
    funext t ω
    rw [TailConvexWeights.applyVector_process_apply]
    exact congrFun (w.apply_eq_sum_coeff_superset w.support_subset_rangeSize _) ω
  change (∫ ω, elementaryEmeryTestError
    (C.lemma48TailConvexStrategy V w.coeff w.rangeSize c).martingalePart 0 J T ω ∂Q) ≤
      2 * (η + η) + Q.real {ω | absoluteStrictHittingAfter
        (C.lemma48TailConvexStrategy V w.coeff w.rangeSize c).martingalePart η ω ≠ ⊤} at hEstimate
  rw [hM] at hEstimate
  convert hEstimate using 1
  dsimp only [convexTailPassageEvent]
  ring

end FTAPTheorem42.BoundedSourceIntegralMarket
