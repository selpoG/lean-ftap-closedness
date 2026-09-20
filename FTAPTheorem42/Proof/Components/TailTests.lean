/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.Emery
import FTAPTheorem42.Interface.TailTests
import FTAPTheorem42.Interface.GainStopping
import FTAPTheorem42.Foundations.ConvexProcesses
import FTAPTheorem42.Proof.Components.TailBoundedness

/-! # DS Lemma 4.9: a common cutoff for all elementary tests

Combine small passage probabilities with the finite tail-test estimate, then
apply the result to the same original-price gains.
-/

/-! ## The uniform cutoff argument -/

namespace FTAPTheorem42

open MeasureTheory
open scoped NNReal

/-- Combine small passage probabilities with the finite tail-test estimate.
The analytic estimate alone does not assert decay of the passage term. -/
theorem uniform_tail_tests_of_passage
    {W J : Type*} (valid : W → Prop)
    (passage : W → Real → Real → Real)
    (testError : W → Real → NNReal → J → Real)
    (hPassage : ∀ ε : Real, 0 < ε → ∃ c₀ : Real, 0 ≤ c₀ ∧
      ∀ (w : W) (c : Real), c₀ ≤ c → valid w → passage w c ε ≤ ε)
    (hEstimate : ∀ η : Real, 0 < η → ∃ c₀ : Real, 0 ≤ c₀ ∧
      ∀ (w : W) (c : Real), c₀ ≤ c → valid w →
        ∀ T : NNReal, 0 < T → ∀ j : J,
          testError w c T j ≤ 4 * η + passage w c η) :
    ∀ ε : Real, 0 < ε → ∃ c₀ : Real, 0 ≤ c₀ ∧
      ∀ (w : W) (c : Real), c₀ ≤ c → valid w →
        ∀ T : NNReal, 0 < T → ∀ j : J, testError w c T j ≤ ε := by
  intro ε hε
  have ha : 0 < ε / 8 := by positivity
  obtain ⟨cp, hcp, hPass⟩ := hPassage (ε / 8) ha
  obtain ⟨cj, _, hBound⟩ := hEstimate (ε / 8) ha
  refine ⟨max cp cj, hcp.trans (le_max_left _ _), ?_⟩
  intro w c hc hw T hT j
  have hp := hPass w c ((le_max_left _ _).trans hc) hw
  have ht := hBound w c ((le_max_right _ _).trans hc) hw T hT j
  linarith only [hp, ht, hε]

end FTAPTheorem42

/-! ## Tests of original gains -/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ Q : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
  [SigmaFiniteFiltration μ F] [SigmaFiniteFiltration Q F]

/-- Lemmas 4.7 and 4.8 supply the two inputs of the finite test estimate. -/
theorem originalGain_finiteTail_tests
    (source : BoundedSemimartingaleSource S F μ)
    (hNFLVR : LinftyNFLVR μ (LinftyClaims μ
      (C0AsDifference μ (generalTerminalClaims source))))
    (hQμ : Q ≪ μ) (hμQ : μ ≪ Q) (hUsual : Filtration.UsualConditions Q F)
    (H : Nat → FiniteOriginalSpecialGain source Q)
    (q : Ω → Real) (hq : MemLp q 2 Q)
    (hLower : ∀ i, ∀ᵐ ω ∂Q, ∀ t, (-1 : Real) ≤ (H i).original.gain t ω)
    (hBound : ∀ i, ∀ᵐ ω ∂Q, ∀ t, |(H i).original.gain t ω| ≤ ‖q ω‖) :
    ∀ ε : Real, 0 < ε → ∃ c₀ : Real, 0 ≤ c₀ ∧
      ∀ (w : TailConvexWeights 0) (c : Real), c₀ ≤ c →
        ∀ T : NNReal, 0 < T → ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
          (∫ ω, elementaryEmeryTestError
            (w.applyVector (fun i => absolutePassageTail (H i).decomposition.N c)) 0 J T ω ∂Q)
              ≤ ε := by
  have hMaximal := originalGain_class_boundedInProbability source hNFLVR hQμ hμQ hUsual
    (fun i => (H i).original) (fun i => (H i).decomposition) (fun i => (H i).predictable)
    (fun _ ω => ‖q ω‖) (fun _ => hq.norm) hBound hLower
    ENNReal.toReal_nonneg (fun _ => by
      rw [eLpNorm_norm _ hq.aestronglyMeasurable, ENNReal.ofReal_toReal hq.eLpNorm_ne_top])
  have hPassage := originalGain_finiteTail_tendsToZero source hNFLVR hQμ hμQ hUsual
    H q hq hLower hBound
  have hEstimate := originalGain_finiteTail_test_estimate source hUsual H q hq hBound hMaximal
  have hResult := uniform_tail_tests_of_passage (fun _ : TailConvexWeights 0 => True)
    (fun w c ε => Q.real (convexTailPassageEvent (fun i => (H i).decomposition.N) w c ε))
    (fun w c T (J : BoundedPredictableElementaryMultiplier (Ω := Ω) F) =>
      ∫ ω, elementaryEmeryTestError
        (w.applyVector (fun i => absolutePassageTail (H i).decomposition.N c)) 0 J T ω ∂Q)
    (fun ε hε => by
      obtain ⟨c₀, hc₀, hP⟩ := hPassage ε hε
      exact ⟨c₀, hc₀, fun w c hc _ => hP w c hc⟩)
    (fun η hη => by
      obtain ⟨c₀, hc₀, hE⟩ := hEstimate η hη
      exact ⟨c₀, hc₀, fun w c hc _ => hE w c hc⟩)
  intro ε hε
  obtain ⟨c₀, hc₀, hResult⟩ := hResult ε hε
  exact ⟨c₀, hc₀, fun w c hc => hResult w c hc trivial⟩

/-- Encode the input index and the deterministic horizon together. The finite
family estimate therefore chooses its cutoff before the test horizon. -/
theorem originalGain_tail_tests
    (source : BoundedSemimartingaleSource S F μ)
    (hNFLVR : LinftyNFLVR μ (LinftyClaims μ
      (C0AsDifference μ (generalTerminalClaims source))))
    (hQμ : Q ≪ μ) (hμQ : μ ≪ Q) (hUsual : Filtration.UsualConditions Q F)
    (H : Nat → OriginalSpecialGain source Q)
    (q : Ω → Real) (hq : MemLp q 2 Q)
    (hLower : ∀ i, ∀ᵐ ω ∂Q, ∀ t, (-1 : Real) ≤ (H i).original.gain t ω)
    (hBound : ∀ i, ∀ᵐ ω ∂Q, ∀ t, |(H i).original.gain t ω| ≤ ‖q ω‖) :
    ∀ ε : Real, 0 < ε → ∃ c₀ : Real, 0 ≤ c₀ ∧
      ∀ (w : TailConvexWeights 0) (c : Real), c₀ ≤ c →
        ∀ T : NNReal, 0 < T → ∀ J : BoundedPredictableElementaryMultiplier (Ω := Ω) F,
          (∫ ω, elementaryEmeryTestError
            (w.applyVector (fun i => absolutePassageTail (H i).decomposition.N c)) 0 J T ω ∂Q)
              ≤ ε := by
  let horizon : Nat → NNReal := fun k => ((Nat.unpair k).2 + 1 : NNReal)
  choose U hUX hUN hUA using fun k => originalSpecialGain_finiteStop source hQμ hμQ
    (H (Nat.unpair k).1) (horizon k) (by dsimp [horizon]; positivity)
  have hULower k : ∀ᵐ ω ∂Q, ∀ t, (-1 : Real) ≤ (U k).original.gain t ω := by
    rw [hUX k]
    filter_upwards [hLower (Nat.unpair k).1] with ω hω
    exact fun t => hω (min t (horizon k))
  have hUBound k : ∀ᵐ ω ∂Q, ∀ t, |(U k).original.gain t ω| ≤ ‖q ω‖ := by
    rw [hUX k]
    filter_upwards [hBound (Nat.unpair k).1] with ω hω
    exact fun t => hω (min t (horizon k))
  have hTests := originalGain_finiteTail_tests source hNFLVR hQμ hμQ hUsual
    U q hq hULower hUBound
  intro ε hε
  obtain ⟨c₀, hc₀, hTest⟩ := hTests ε hε
  refine ⟨c₀, hc₀, fun w c hc T hT J => ?_⟩
  obtain ⟨r, hr⟩ := exists_nat_ge T
  let W := w.atPair r
  have hEstimate := hTest W c hc T hT J
  have hPaths ω t (ht : t ≤ T) :
      W.applyVector (fun k => absolutePassageTail (U k).decomposition.N c) t ω =
        w.applyVector (fun i => absolutePassageTail (H i).decomposition.N c) t ω := by
    simp only [TailConvexWeights.applyVector_process_apply, W, TailConvexWeights.atPair_apply]
    simp only [hUN, Nat.unpair_pair, horizon, absolutePassageTail_deterministicallyStopped]
    rw [min_eq_left (ht.trans (hr.trans (le_add_of_nonneg_right zero_le_one)))]
    congr 1
    funext i
    rw [Nat.unpair_pair]
  have hErrors : elementaryEmeryTestError
      (W.applyVector (fun k => absolutePassageTail (U k).decomposition.N c)) 0 J T =
      elementaryEmeryTestError
        (w.applyVector (fun i => absolutePassageTail (H i).decomposition.N c)) 0 J T := by
    funext ω
    exact elementaryEmeryTestError_congr_upto J T ω (hPaths ω) (fun _ _ => rfl)
  rw [hErrors] at hEstimate
  exact hEstimate

end FTAPTheorem42.BoundedSourceIntegralMarket
