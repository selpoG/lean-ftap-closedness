/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Proof.Selection.PathLimit
import FTAPTheorem42.Proof.Components.MartingaleCauchy
import FTAPTheorem42.Interface.Envelope
import FTAPTheorem42.Interface.GainDecomposition
import FTAPTheorem42.Interface.GainConvexity
import FTAPTheorem42.Interface.FiniteHahn

/-! # The main proof's selected, convexified Hahn sequence

Maximality supplies the uniform path limit; Lemmas 4.7–4.10 supply common
martingale weights. Only finite integration and quantitative analytic estimates
cross the appendix boundary.
-/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

/-- The same selected and convexified gains retain their own uniform and terminal limits. -/
theorem exists_original_oriented_sequence
    (source : BoundedSemimartingaleSource S F μ)
    (hNFLVR : LinftyNFLVR μ (LinftyClaims μ
      (C0AsDifference μ (generalTerminalClaims source))))
    {h : Ω → Real}
    (hmax : AEMaximalIn μ (InMeasureSequentialClosure μ
      (generalAdmissibleClaims source 1)) h) :
    ∃ (Q : Measure Ω) (_ : IsProbabilityMeasure Q), Q ≪ μ ∧ μ ≪ Q ∧
      ∃ (X : Process Ω) (K Y : Nat → Process Ω) (E : ∀ n, J1Decomposition (Y n) F Q),
        (∀ n, GeneralIntegralGraph source (K n) (Y n)) ∧
        (∀ n, StronglyAdapted F (Y n)) ∧
        (∀ n ω t, ContinuousWithinAt (Y n · ω) (Ici t) t) ∧
        StronglyAdapted F X ∧
        (∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t) ∧ ProcessHasLeftLimits X ∧
        X 0 =ᵐ[μ] 0 ∧ (∀ t, AELowerBoundedBy μ (-1) (X t)) ∧
        (∀ᵐ ω ∂μ, Tendsto (X · ω) atTop (𝓝 (h ω))) ∧
        ElementaryEmeryCauchy Q F (fun n => (E n).N) ∧
        (∀ T : NNReal, 0 < T → ∀ ε : Real, 0 < ε →
          ∃ N : Nat, ∀ n, N ≤ n → ∀ k, N ≤ k → ∀ δ : Real, 0 ≤ δ →
            OriginalPairHahnOrientedImprovement source (Y n) (Y k) (E n) (E k) T ε δ) ∧
        (∀ᵐ ω ∂μ, TendstoUniformly (fun n t => Y n t ω) (X · ω) atTop) := by
  classical
  let A := generalMarket source
  let O := Classical.choice (generalMarket_operations source)
  have hmaxA := hmax
  rw [generalAdmissibleClaims_one_eq_generalMarket_K1] at hmaxA
  obtain ⟨H, X, hOne, hHT, hXA, hXR, hXL, hX0, hXLb, hUniform, hTerminal⟩ :=
    exists_uniform_terminal_limit_of_maximal source hNFLVR hmaxA
  have hC := pairwise_allTimeGap_cauchyInMeasure_of_terminal_chronological_pasting
    source O hOne (fun n => O.adapted (H n)) hHT
    (fun q hq => ((generalMarket_terminal_properties source).1 q
      (A.K1_subset_K0OfGainProcessModel μ hq)).aestronglyMeasurable)
    (generalMarket_forwardConvexCandidates source hNFLVR) hmaxA
  obtain ⟨f, q, hf, hqMeas, hq0, hDom⟩ := AnalyticInterface.regular_common_envelope
    (fun n => A.gain (H n)) (fun n => O.adapted (H n))
    (fun n => O.rightContinuous (H n)) (fun n => O.leftLimits (H n))
    (fun n => A.terminalGain (H n)) (fun n => O.terminal (H n)) hC
  obtain ⟨Q, hQ, hQμ, hμQ, hq, hUsual⟩ := AnalyticInterface.equivalent_envelope_measure
    source.usualConditions q hqMeas hq0
  let : IsProbabilityMeasure Q := hQ
  choose K hK using fun n => O.gainGraph (H (f n))
  let Y : Nat → OriginalGain source := fun n => {
    integrand := K n
    gain := A.gain (H (f n))
    integralGraph := hK n
    adapted := O.adapted (H (f n))
    rightContinuous := O.rightContinuous (H (f n))
    leftLimits := O.leftLimits (H (f n))
    zero := O.zero (H (f n)) }
  have hYB n : ∀ᵐ ω ∂Q, ∀ t, |(Y n).gain t ω| ≤ q ω := by
    filter_upwards [hQμ.ae_le hDom] with ω hω
    exact hω n
  have hYBN n : ∀ᵐ ω ∂Q, ∀ t, |(Y n).gain t ω| ≤ ‖q ω‖ := by
    filter_upwards [hYB n] with ω hω
    exact fun t => (hω t).trans (le_abs_self _)
  have hYL n : ∀ᵐ ω ∂Q, ∀ t, (-1 : Real) ≤ (Y n).gain t ω :=
    hQμ.ae_le (ae_all_lowerBound_of_rightDense_skeleton _
      NNRealRightDenseSkeleton.skeleton NNRealRightDenseSkeleton.skeleton_rightDense
      (O.rightContinuous (H (f n))) (hOne (f n)).2)
  choose E hEP using fun n => originalGain_specialDecomposition source hQμ hμQ (Y n) q hq (hYBN n)
  let U : Nat → OriginalSpecialGain source Q := fun n => ⟨Y n, E n, hEP n⟩
  obtain ⟨w, hM⟩ := exists_original_martingale_convexification source hNFLVR
    hQμ hμQ hUsual U q hq hYL hYB
  choose V hV hVN hVA using fun n => originalGain_convexCombination source hQμ hμQ U (w n)
  have hVB n : ∀ᵐ ω ∂Q, ∀ t, |(V n).original.gain t ω| ≤ q ω := by
    filter_upwards [ae_all_iff.mpr hYB] with ω hω
    intro t
    rw [hV n, TailConvexWeights.applyVector_process_apply]
    calc
      _ ≤ ∑ i ∈ (w n).support, |(w n).weight i * (Y i).gain t ω| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ (w n).support, (w n).weight i * q ω := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul, abs_of_nonneg ((w n).nonneg i hi)]
        exact mul_le_mul_of_nonneg_left (hω i t) ((w n).nonneg i hi)
      _ = _ := by rw [← Finset.sum_mul, (w n).sum_eq_one, one_mul]
  have hVL n : ∀ᵐ ω ∂Q, ∀ t, (-1 : Real) ≤ (V n).original.gain t ω := by
    filter_upwards [ae_all_iff.mpr hYL] with ω hω
    intro t
    rw [hV n, TailConvexWeights.applyVector_process_apply]
    calc
      (-1 : Real) = ∑ i ∈ (w n).support, (w n).weight i * (-1) := by
        rw [← Finset.sum_mul, (w n).sum_eq_one, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_left (hω i t) ((w n).nonneg i hi)
  have hVM : ElementaryEmeryCauchy Q F (fun n => (V n).decomposition.N) := by
    have hEq : (fun n => (V n).decomposition.N) =
        (fun n => (w n).applyVector (fun i => (U i).decomposition.N)) := funext hVN
    rwa [hEq]
  refine ⟨Q, hQ, hQμ, hμQ, X, fun n => (V n).original.integrand,
    fun n => (V n).original.gain, fun n => (V n).decomposition,
    fun n => (V n).original.integralGraph, fun n => (V n).original.adapted,
    fun n => (V n).original.rightContinuous,
    hXA, hXR, hXL, hX0, hXLb, hTerminal, hVM, ?_, ?_⟩
  · intro T hT ε hε
    obtain ⟨N, hN⟩ := hVM T ε hε
    exact ⟨N, fun n hn k hk δ hδ => originalGain_finiteHahn source hQμ hμQ hUsual
      (V n) (V k) q hq (hVB n) (hVB k) (hVL n) (hVL k)
      T hT ε δ hδ (hN n hn k hk) (hN k hk n hn)⟩
  · filter_upwards [hUniform] with ω hω
    have hSelected : TendstoUniformly (fun n t => (Y n).gain t ω) (X · ω) atTop :=
      fun u hu => hf.tendsto_atTop.eventually (hω u hu)
    have hEq : (fun n t => (V n).original.gain t ω) =
        (fun n => (w n).apply (fun i t => (Y i).gain t ω)) := by
      funext n t
      rw [hV n, TailConvexWeights.applyVector_process_apply]
      rfl
    rw [hEq]
    exact TailConvexWeights.tendstoUniformly_apply w hSelected

end FTAPTheorem42.BoundedSourceIntegralMarket
