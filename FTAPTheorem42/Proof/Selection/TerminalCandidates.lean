/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Interface.MarketOperations
import FTAPTheorem42.Interface.TerminalMarket
import FTAPTheorem42.Trading.Basic

/-! # Forward-convex candidates and equivalent-measure maximality -/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

/-- Proposition 3.1 supplies forward-convex terminal candidates in the original market. -/
theorem generalMarket_forwardConvexCandidates
    (source : BoundedSemimartingaleSource S F μ)
    (hNFLVR : LinftyNFLVR μ (LinftyClaims μ
      (C0AsDifference μ (generalTerminalClaims source)))) :
    TerminalGainHasAEForwardConvexCandidate μ ((generalMarket source).K1OfGainProcessModel μ) := by
  classical
  let A := generalMarket source
  let O := Classical.choice (generalMarket_operations source)
  obtain ⟨hMeas, hLower⟩ := generalMarket_terminal_properties source
  have hSaturated : AESaturated μ (A.K1OfGainProcessModel μ) := by
    rintro f g ⟨H, hH, rfl⟩ hfg
    obtain ⟨K, hK, hT⟩ := O.replaceTerminal H g hfg
    refine ⟨K, ?_, hT⟩
    change A.gain K = A.gain H at hK
    rcases hH with ⟨ha, hH⟩
    exact ⟨ha, fun t => by simpa only [hK] using hH t⟩
  rw [generalTerminalClaims_eq_generalMarket_K0] at hNFLVR
  exact A.terminalGainHasAEForwardConvexCandidate_K1_of_proposition31_generalFinite_ae
    μ (fun f hf => (hMeas f hf).aestronglyMeasurable) hSaturated hLower hNFLVR

open EquivalentMeasureTransfer
variable {Q : Measure Ω} [IsProbabilityMeasure Q]

/-- Transfer terminal sets, convex candidates and maximality, retaining the
original market. No special decomposition is transferred. -/
theorem generalMarket_maximalityData_equivalentMeasure
    (source : BoundedSemimartingaleSource S F μ) (hμQ : μ ≪ Q) (hQμ : Q ≪ μ)
    (hNFLVR : LinftyNFLVR μ (LinftyClaims μ
      (C0AsDifference μ (generalTerminalClaims source))))
    {h : Ω → Real}
    (hmax : AEMaximalIn μ (InMeasureSequentialClosure μ
      (generalAdmissibleClaims source 1)) h) :
    ClaimSetAEStronglyMeasurable Q ((generalMarket source).K1OfGainProcessModel Q) ∧
    TerminalGainHasAEForwardConvexCandidate Q ((generalMarket source).K1OfGainProcessModel Q) ∧
    AEMaximalIn Q (InMeasureSequentialClosure Q
      ((generalMarket source).K1OfGainProcessModel Q)) h := by
  let B := generalMarket source
  have hMeas : ClaimSetAEStronglyMeasurable μ (B.K1OfGainProcessModel μ) := fun q hq =>
    ((generalMarket_terminal_properties source).1 q
      (B.K1_subset_K0OfGainProcessModel μ hq)).aestronglyMeasurable
  have hEq := K1OfGainProcessModel_eq_of_mutuallyAbsolutelyContinuous B hμQ hQμ
  rw [generalAdmissibleClaims_one_eq_generalMarket_K1] at hmax
  have hCandidate := generalMarket_forwardConvexCandidates source hNFLVR
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    exact (hMeas q (by rwa [hEq])).mono_ac hQμ
  · rw [← hEq]
    exact (terminalGainHasAEForwardConvexCandidate_iff_of_mutuallyAbsolutelyContinuous
      hμQ hQμ).mp hCandidate
  · rw [← hEq, ← inMeasureSequentialClosure_eq_of_mutuallyAbsolutelyContinuous hμQ hQμ hMeas]
    exact (aEMaximalIn_iff_of_mutuallyAbsolutelyContinuous hμQ hQμ).mp hmax

end FTAPTheorem42.BoundedSourceIntegralMarket
