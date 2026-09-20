/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Closedness.HahnGaps
import FTAPTheorem42.Proof.Selection.TerminalCandidates

/-! # The original terminal market's maximality consumer under an equivalent measure -/

namespace FTAPTheorem42.BoundedSourceIntegralMarket

/-! ## Consume normalized original-market Hahn improvements in maximality -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

open EquivalentMeasureTransfer
variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ Q : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
  [SigmaFiniteFiltration μ F]

/-- Summable downside failure and persistent positive FV increments contradict
maximality in the original market. Both terminal sequences use the same normalization. -/
theorem not_originalHahn_improvements
    (source : BoundedSemimartingaleSource S F μ) (hμQ : μ ≪ Q) (hQμ : Q ≪ μ)
    (hNFLVR : LinftyNFLVR μ (LinftyClaims μ
      (C0AsDifference μ (generalTerminalClaims source))))
    {h : Ω → Real}
    (hmax : AEMaximalIn μ (InMeasureSequentialClosure μ
      (generalAdmissibleClaims source 1)) h)
    {Y M A : Nat → Process Ω} {T : NNReal} {U : Nat → NNReal}
    {b δ : Nat → Real} {α : Real} (hα : 0 < α)
    (P : ∀ r, OriginalHahnImprovement source Q (Y r) (M r) (A r) T (b r) (δ r))
    (hM : ∀ r, StronglyAdapted F (M r))
    (hMR : ∀ r ω t, ContinuousWithinAt (M r · ω) (Ici t) t)
    (hU : ∀ r, T ≤ U r)
    (hδ : ∀ r, 0 < δ r) (hδ1 : ∀ r, δ r ≤ 1) (hδα : ∀ r, δ r ≤ α / 8)
    (hδlim : Tendsto δ atTop (𝓝 0))
    (hδsum : (∑' r, ENNReal.ofReal (δ r)) ≠ ⊤)
    (hb : ∀ r, (b r + b r) / (δ r / 4) ≤ δ r)
    (hC : ∀ r, α / 2 < Q.real {ω | α / 2 < (P r).finiteVariation T ω})
    (hYmeas : ∀ r, AEStronglyMeasurable (Y r (U r)) Q)
    (hYlim : TendstoAE Q (fun r => Y r (U r)) h) : False := by
  let _ := source.usualConditions.rightContinuous
  let B := generalMarket source
  obtain ⟨hMeas, hCandidate, hMax⟩ :=
    generalMarket_maximalityData_equivalentMeasure source hμQ hQμ hNFLVR hmax
  let bad : Nat → Set Ω := fun r => {ω | lowerStrictHittingAfter
    (hahnMartingaleAdvantage (P r).martingale (M r)) (δ r) ω ≤ (T : WithTop NNReal)}
  let s : Nat → Set Ω := fun r => {ω | α / 2 < (P r).finiteVariation T ω} \ bad r
  have hBadMeas : ∀ r, MeasurableSet (bad r) := by
    intro r
    have hτ : IsStoppingTime F (lowerStrictHittingAfter
        (hahnMartingaleAdvantage (P r).martingale (M r)) (δ r)) := by
      apply lowerStrictHittingAfter_isStoppingTime
      · exact fun t => ((P r).martingale_adapted t).sub
          (((hM r t).measurable.max measurable_const).stronglyMeasurable)
      · exact fun ω t => ((P r).martingale_right ω t).sub
          ((hMR r ω t).max continuousWithinAt_const)
    exact F.le T _ (hτ T)
  have hBad : ∀ r, Q.real (bad r) ≤ δ r := fun r =>
    ((P r).downside_probability (hδ r) (hδ1 r)).trans (hb r)
  have hBadSum : (∑' r, Q (bad r)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hδsum
    apply ENNReal.tsum_le_tsum
    intro r
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (hBad r)
  let g : Nat → Ω → Real := fun r ω =>
    finiteHahnPastedGain (Y r) (P r).gain (P r).martingale (M r) (δ r) T (U r) (U r) ω /
      (1 + δ r)
  let f : Nat → Ω → Real := fun r ω => Y r (U r) ω / (1 + δ r)
  have hg : ∀ r, g r ∈ B.K1OfGainProcessModel Q := by
    intro r
    rw [← K1OfGainProcessModel_eq_of_mutuallyAbsolutelyContinuous B hμQ hQμ,
      ← generalAdmissibleClaims_one_eq_generalMarket_K1 source]
    exact truncatedTerminalClaimsBy_normalize source ((P r).terminal_mem (U r) (hU r))
  have hf : TendstoAE Q f h := by
    filter_upwards [hYlim] with ω hω
    have ht := hω.div (tendsto_const_nhds.add hδlim)
      (by norm_num : (1 : Real) + 0 ≠ 0)
    change Tendsto (fun r => f r ω) atTop (𝓝 (h ω / (1 + 0))) at ht
    simpa only [add_zero, div_one] using ht
  have hGap := fun r => (P r).normalized_terminal_gap_bounds
    (hU r) (hδ r).le (hδ1 r) (hδα r)
  have hError : TendstoAE Q (fun r ω => max (f r ω - g r ω) 0) (fun _ => 0) := by
    filter_upwards [ae_eventually_notMem hBadSum, ae_all_iff.mpr hGap] with ω hGood hGapω
    apply squeeze_zero' (Eventually.of_forall fun _ => le_max_right _ _) _ hδlim
    filter_upwards [hGood] with r hr
    exact (hGapω r (lt_of_not_ge hr)).1
  apply not_persistent_terminalGain_improvement_of_vanishing_lowerError
    (A := B) (μ := Q) (h := h) (b := f) (g := g) (s := s)
    (by positivity : 0 < α / 8) (by positivity : 0 < α / 4)
    hMeas hCandidate hg hMax
    (fun r => by
      simpa only [f, div_eq_mul_inv] using (hYmeas r).mul_const (1 + δ r)⁻¹) hf hError
  · intro r
    exact (measurableSet_lt measurable_const
      (((P r).finiteVariation_adapted T).mono (F.le T)).measurable).nullMeasurableSet.diff
        (hBadMeas r).nullMeasurableSet
  · intro r
    rw [← ofReal_measureReal]
    apply ENNReal.ofReal_le_ofReal
    have hDiff := le_measureReal_sdiff (μ := Q)
      (s₁ := {ω | α / 2 < (P r).finiteVariation T ω}) (s₂ := bad r)
    change α / 4 ≤ Q.real ({ω | α / 2 < (P r).finiteVariation T ω} \ bad r)
    linarith [hC r, hBad r, hδα r]
  · intro r
    filter_upwards [hGap r] with ω hω hs
    exact (hω (lt_of_not_ge hs.2)).2 hs.1

end FTAPTheorem42.BoundedSourceIntegralMarket
