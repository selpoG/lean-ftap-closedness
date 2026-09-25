/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Proof.OrientedSequence
import FTAPTheorem42.Closedness.FiniteVariationCauchy

/-! # Both component Cauchy estimates for the main proof’s selected sequence -/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

/-- Maximality supplies FV Cauchy bounds for the sequence returned by the
analytic interface. Only its stated process estimates enter this proof. -/
theorem exists_selected_original_componentCauchy
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
        (∀ T : NNReal, ∀ ε : Real, 0 < ε →
          ∃ N : Nat, ∀ n, N ≤ n → ∀ k, N ≤ k →
            Q.real {ω | ε < finiteHorizonPathVariation ((E n).A - (E k).A)
              (fun ω a c ha hc => by
                simpa only [Pi.sub_apply, sub_eq_add_neg] using
                  boundedVariationOn_add ((E n).variationA ω a c ha hc)
                    (boundedVariationOn_neg ((E k).variationA ω a c ha hc))) T ω} ≤ ε) ∧
        (∀ᵐ ω ∂μ, TendstoUniformly (fun n t => Y n t ω) (X · ω) atTop) := by
  obtain ⟨Q, hQ, hQμ, hμQ, X, K, Y, E, hGraph, hYA, hYR,
    hXA, hXR, hXL, hX0, hLower, hTerminal, hM, hHahn, hUniform⟩ :=
    exists_original_oriented_sequence source hNFLVR hmax
  let := hQ
  refine ⟨Q, hQ, hQμ, hμQ, X, K, Y, E, hGraph, hYA, hYR,
    hXA, hXR, hXL, hX0, hLower, hTerminal, hM, ?_, hUniform⟩
  intro T ε hε
  by_cases hT : 0 < T
  · exact original_finiteVariation_cauchyInProbability source
      hμQ hQμ hNFLVR hmax Y hYA E hUniform hTerminal T (hHahn T hT) ε hε
  · have hT0 : T = 0 := le_antisymm (le_of_not_gt hT) zero_le
    subst T
    refine ⟨0, fun n _ k _ => ?_⟩
    have hVar : ∀ ω, finiteHorizonPathVariation ((E n).A - (E k).A)
        (fun ω a c ha hc => by
          simpa only [Pi.sub_apply, sub_eq_add_neg] using
            boundedVariationOn_add ((E n).variationA ω a c ha hc)
              (boundedVariationOn_neg ((E k).variationA ω a c ha hc))) 0 ω = 0 := by
      intro ω
      exact (finiteHorizonPathVariation_eq_eVariationOn _ _
        (fun ω t => ((E n).rightA ω t).sub ((E k).rightA ω t)) 0 ω).trans (by simp)
    simp only [hVar, not_lt_of_ge hε.le, Set.ofPred_false, measureReal_empty]
    exact hε.le

end FTAPTheorem42.BoundedSourceIntegralMarket
