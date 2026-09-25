/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Proof.Selection.ChronologicalPasting
import FTAPTheorem42.Proof.Selection.TerminalCandidates
import FTAPTheorem42.Interface.PathLimits

/-! # Maximal terminal claims determine the uniform path limit -/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]

/-- Construct the all-time path limit directly from a maximal point of the
original completion's unit-admissible terminal closure. -/
theorem exists_uniform_terminal_limit_of_maximal
    (source : BoundedSemimartingaleSource S F μ)
    (hNFLVR : LinftyNFLVR μ (LinftyClaims μ (C0AsDifference μ
      (generalTerminalClaims source))))
    {h : Ω → ℝ}
    (hmax : AEMaximalIn μ (InMeasureSequentialClosure μ
      ((generalMarket source).K1OfGainProcessModel μ)) h) :
    ∃ (H : Nat → (generalMarket source).Strategy) (X : Process Ω),
      (∀ n, (generalMarket source).OneAdmissible μ (H n)) ∧
      TendstoAE μ (fun n => ((generalMarket source).terminalGain (H n))) h ∧
      StronglyAdapted F X ∧
      (∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t) ∧ ProcessHasLeftLimits X ∧
      X 0 =ᵐ[μ] 0 ∧ (∀ t, AELowerBoundedBy μ (-1) (X t)) ∧
      (∀ᵐ ω ∂μ, TendstoUniformly (fun n t => ((generalMarket source).gain (H n)) t ω) (X · ω)
        atTop) ∧
      (∀ᵐ ω ∂μ, Tendsto (X · ω) atTop (𝓝 (h ω))) := by
  classical
  let A := generalMarket source
  let O := Classical.choice (generalMarket_operations source)
  obtain ⟨v, hv, hlim⟩ := hmax.1
  choose V hV hvEq using hv
  change ∀ n, ((generalMarket source).terminalGain (V n)) = v n at hvEq
  obtain ⟨f, _hf, hAE⟩ := hlim.exists_seq_tendsto_ae
  let H : Nat → (generalMarket source).Strategy := fun n => V (f n)
  have hH : ∀ n, A.OneAdmissible μ (H n) := fun n => hV (f n)
  have hHT : TendstoAE μ (fun n => ((generalMarket source).terminalGain (H n))) h := by
    change ∀ᵐ ω ∂μ, Tendsto (fun n => ((generalMarket source).terminalGain (V (f n))) ω) atTop
      (𝓝 (h ω))
    simpa only [hvEq] using hAE
  have hHA : ∀ n, StronglyAdapted F ((generalMarket source).gain (H n)) :=
    fun n => O.adapted (H n)
  have hC := pairwise_allTimeGap_cauchyInMeasure_of_terminal_chronological_pasting
    source O hH hHA hHT
    (fun q hq => ((generalMarket_terminal_properties source).1 q
      (A.K1_subset_K0OfGainProcessModel μ hq)).aestronglyMeasurable)
    (generalMarket_forwardConvexCandidates source hNFLVR) hmax
  obtain ⟨g, X, hg, hXA, hXR, hXL, hU⟩ :=
    AnalyticInterface.regular_uniform_limit
      (fun n => ((generalMarket source).gain (H n))) source.usualConditions hHA
      (fun n => O.rightContinuous (H n))
      (fun n => O.leftLimits (H n)) hC
  refine ⟨fun n => H (g n), X, fun n => hH (g n), hHT.comp_strictMono hg,
    hXA, hXR, hXL, ?_, ?_, hU, ?_⟩
  · have h0 : ∀ᵐ ω ∂μ, ∀ n, ((generalMarket source).gain (H n)) 0 ω = 0 :=
      ae_all_iff.mpr fun n => O.zero (H n)
    filter_upwards [hU, h0] with ω hω h0ω
    have hLim := hω.tendsto_at 0
    have hConst : Tendsto (fun n => ((generalMarket source).gain (H (g n))) 0 ω) atTop (𝓝 0) := by
      simpa only [h0ω] using (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : Real)) atTop (𝓝 0))
    exact tendsto_nhds_unique hLim hConst
  · intro t
    have hLower : ∀ᵐ ω ∂μ, ∀ n, -1 ≤ ((generalMarket source).gain (H n)) t ω :=
      ae_all_iff.mpr fun n => (hH n).2 t
    filter_upwards [hU, hLower] with ω hω hLowerω
    exact ge_of_tendsto' (hω.tendsto_at t) (fun n => hLowerω (g n))
  · have hTerm : ∀ᵐ ω ∂μ, ∀ n,
        Tendsto (((generalMarket source).gain (H n)) · ω) atTop (𝓝 (((generalMarket
          source).terminalGain (H n)) ω)) :=
      ae_all_iff.mpr fun n => O.terminal (H n)
    filter_upwards [hU, hTerm, hHT.comp_strictMono hg] with ω hω hTermω hHTω
    exact tendsto_atTop_of_tendstoUniformly_terminal hω (fun n => hTermω (g n)) hHTω

end FTAPTheorem42.BoundedSourceIntegralMarket
