/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Proof.Selection.LowerBound
import FTAPTheorem42.Closedness.ComponentCauchy

/-! # Delbaen–Schachermayer Theorem 4.2

The maximal-claim realization and the final Fatou/weak-star closure theorem
for the original bounded real-valued semimartingale market.
-/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

/-! ## Attaining maximal closure claims in the original general integral market -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

/-- Original NFLVR supplies both component estimates for the same convex
sequence; its own all-time limit realizes the maximal terminal claim. -/
theorem maximal_mem_general_K1
    (source : BoundedSemimartingaleSource S F μ)
    (hNFLVR : LinftyNFLVR μ (LinftyClaims μ
      (C0AsDifference μ (generalTerminalClaims source))))
    {h : Ω → Real}
    (hmax : AEMaximalIn μ (InMeasureSequentialClosure μ
      (generalAdmissibleClaims source 1)) h) :
    h ∈ generalAdmissibleClaims source 1 := by
  classical
  obtain ⟨Q, hQ, hQμ, hμQ, X, K, Y, E, hGraph, hYA, hYR,
    hXA, hXR, hXL, hX0, hLower, hTerminal, hM, hV, hUniform⟩ :=
    exists_selected_original_componentCauchy source hNFLVR hmax
  let := hQ
  exact truncatedTerminalClaims_one_of_component_estimates source hQμ hμQ hGraph hYA hYR
    hXA hXR hXL hX0 hLower hUniform hTerminal (fun n => (E n).decomposition)
    (fun n k ω a c ha hc => by
      simpa only [Pi.sub_apply, sub_eq_add_neg] using
        boundedVariationOn_add ((E n).variationA ω a c ha hc)
          (boundedVariationOn_neg ((E k).variationA ω a c ha hc)))
    (fun n => (E n).rightA)
    (hM.uniform_probability (fun n =>
      StronglyAdapted.isStronglyProgressive_of_rightContinuous (E n).adaptedN (E n).rightN)) hV

/-! ## Theorem 4.2 for the original bounded semimartingale's general integral market -/

/-- The original general market attains each maximal closure claim; the
existing Fatou consumer only needs the resulting K0 representative. -/
theorem generalMarket_maximal_realization
    (source : BoundedSemimartingaleSource S F μ)
    (hNFLVR : LinftyNFLVR μ (LinftyClaims μ
      (C0AsDifference μ (generalTerminalClaims source)))) :
    MaximalInMeasureClosureAERealizableBetween μ
      ((generalMarket source).K1OfGainProcessModel μ)
      ((generalMarket source).K0OfGainProcessModel μ) := by
  intro h _hh hmax
  rw [← generalAdmissibleClaims_one_eq_generalMarket_K1 source] at hmax
  have hh := maximal_mem_general_K1 source hNFLVR hmax
  rw [generalAdmissibleClaims_one_eq_generalMarket_K1 source] at hh
  exact ⟨h, (generalMarket source).K1_subset_K0OfGainProcessModel μ hh, .rfl⟩

/-- Fatou and weak-star closedness for the original price and original
measure, with its general predictable integral terminal claims. -/
theorem theorem42_generalMarket
    (source : BoundedSemimartingaleSource S F μ)
    (hNFLVR : LinftyNFLVR μ (LinftyClaims μ
      (C0AsDifference μ (generalTerminalClaims source)))) :
    FatouClosed μ (C0AsDifference μ (generalTerminalClaims source)) ∧
      LinftyWeakStarClosed μ (C0AsDifference μ (generalTerminalClaims source)) := by
  let B := generalMarket source
  obtain ⟨hKmeas, hTerminal⟩ := generalMarket_terminal_properties source
  have hK0 : generalTerminalClaims source =
      K0OfTerminalGainModel (B.terminalGainModel μ) :=
    (generalTerminalClaims_eq_generalMarket_K0 source).trans
      (B.K0OfGainProcessModel_eq_terminalGainModel μ)
  have hResult := B.theorem42ConcreteWeakStar_from_gainProcessModel_K1_maximalRealization
    μ True (LinftyNFLVR μ (LinftyClaims μ
      (C0AsDifference μ (generalTerminalClaims source))))
    hKmeas hTerminal (generalMarket_terminalLowerBoundControlsGain source hNFLVR)
    (fun _ h => by rwa [← hK0])
    (fun _ h => generalMarket_maximal_realization source h) trivial hNFLVR
  rwa [← hK0] at hResult

end FTAPTheorem42.BoundedSourceIntegralMarket
