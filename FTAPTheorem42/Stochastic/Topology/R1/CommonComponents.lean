/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Topology.R1.Metric
import FTAPTheorem42.Stochastic.Topology.J1.MartingaleRegularization
import FTAPTheorem42.Stochastic.Topology.J1.VariationSeries
import FTAPTheorem42.Stochastic.Topology.J1.QuadraticTail
import FTAPTheorem42.Stochastic.Martingale.Quadratic.LocalMartingaleQuadraticCappedLocalization

/-! # Common localization retaining the original decomposition sequence -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace FTAPTheorem42

open SIntegrableFiniteVariationBridge

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}

theorem J1Decomposition.stopped_component_cost_le_leftClock_add_jump
    {X : Process Ω} (D : J1Decomposition X F mu)
    (Q : LocalMartingaleQuadraticVariation D.N F mu)
    {tau : Ω → NNReal} {T : NNReal}
    (hTau : IsStoppingTime F (fun w => (tau w : WithTop NNReal)))
    (hTauT : ∀ w, tau w ≤ T) :
    (∫⁻ w, ENNReal.ofReal (Real.sqrt (Q.variation (tau w) w)) ∂mu) +
      (∫⁻ w, eVariationOn (strictPrefixProcess D.A tau · w) univ ∂mu) ≤
      (∫⁻ w, ENNReal.ofReal (D.leftClock Q (tau w) w) ∂mu) +
      ∫⁻ w, ENNReal.ofReal |processLeftJump D.N (tau w) w| ∂mu := by
  have hRoot : (∫⁻ w, ENNReal.ofReal (Real.sqrt (Q.variation (tau w) w)) ∂mu) ≤
      ∫⁻ w, ENNReal.ofReal (Real.sqrt (Function.leftLim (Q.variation · w) (tau w))) +
        ENNReal.ofReal |processLeftJump D.N (tau w) w| ∂mu := by
    apply lintegral_mono_ae
    filter_upwards [Q.root_le_leftRoot_add_jump] with w hw
    exact (ENNReal.ofReal_le_ofReal (hw (tau w))).trans_eq
      (ENNReal.ofReal_add (Real.sqrt_nonneg _) (abs_nonneg _))
  apply (add_le_add hRoot
    (D.lintegral_strictPrefix_variation_le_leftVariation tau hTauT)).trans
  apply (le_lintegral_add _ _).trans
  rw [← lintegral_add_right (fun w => ENNReal.ofReal (D.leftClock Q (tau w) w))
    (D.measurable_sampledJump hTau hTauT)]
  apply lintegral_mono
  intro w
  dsimp only [J1Decomposition.leftClock]
  rw [ENNReal.ofReal_add (Real.sqrt_nonneg _) (D.leftVariation_nonneg (tau w) w)]
  exact le_of_eq (add_right_comm _ _ _)

theorem J1Decomposition.exists_common_localizers_summable_component_costs
    [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
    [F.IsRightContinuous] (hUsual : Filtration.UsualConditions mu F)
    {Z : Nat → Process Ω} (D : ∀ k, J1Decomposition (Z k) F mu)
    (Q : ∀ k, LocalMartingaleQuadraticVariation (D k).N F mu)
    (hSum : (∑' k, (D k).r1Cost (Q k)) ≠ ∞) :
    ∃ tau : Nat → Ω → NNReal,
      IsLocalizingSequence F (fun r w => (tau r w : WithTop NNReal)) mu ∧
      (∀ r w, tau r w ≤ ((r + 1 : Nat) : NNReal)) ∧
      ∀ r, (∑' k, ((∫⁻ w, ENNReal.ofReal (Real.sqrt
          ((Q k).variation (tau r w) w)) ∂mu) +
        ∫⁻ w, eVariationOn (strictPrefixProcess (D k).A (tau r) · w) univ ∂mu)) ≤
        (r + 1 : Nat) + ∑' k, (D k).r1Cost (Q k) := by
  obtain ⟨hCap, _⟩ := J1Decomposition.capped_and_jump_summable_of_r1Cost D Q hSum
  obtain ⟨U, _, _, _, hLoc, hT, hGood⟩ :=
    J1Decomposition.exists_common_passage_leftClock_bound hUsual D Q hCap
  have hLoc' : IsLocalizingSequence F
      (fun r w => (cadlagAbsolutePassageLocalizerFinite U r w : WithTop NNReal)) mu := by
    simpa only [coe_cadlagAbsolutePassageLocalizerFinite] using hLoc
  refine ⟨cadlagAbsolutePassageLocalizerFinite U, hLoc', hT, ?_⟩
  intro r
  have hLeft := tsum_lintegral_le_of_ae_tsum_le _
    (hGood.mono (fun w hw => hw.2 r))
  calc
    _ ≤ ∑' k, ((∫⁻ w, ENNReal.ofReal ((D k).leftClock (Q k)
          (cadlagAbsolutePassageLocalizerFinite U r w) w) ∂mu) +
        ∫⁻ w, ENNReal.ofReal |processLeftJump (D k).N
          (cadlagAbsolutePassageLocalizerFinite U r w) w| ∂mu) :=
      ENNReal.tsum_le_tsum (fun k => (D k).stopped_component_cost_le_leftClock_add_jump
        (Q k) (hLoc'.isStoppingTime r) (hT r))
    _ ≤ _ := by
      rw [ENNReal.tsum_add]
      exact add_le_add hLeft (ENNReal.tsum_le_tsum (fun k =>
        (lintegral_jump_le_boundedStoppingJumpCost (hLoc'.isStoppingTime r) (hT r)).trans
          (show boundedStoppingJumpCost (D k).N F mu ≤ (D k).r1Cost (Q k) from
            le_add_right le_rfl)))

theorem R1Process.exists_common_decomposition_components_of_cauchy
    [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
    [hUsual : Fact (Filtration.UsualConditions mu F)] {Z : Nat → R1Process F mu}
    (h : CauchySeq (fun k => SeparationQuotient.mk (Z k))) :
    ∃ f : Nat → Nat, StrictMono f ∧
      ∃ (D : ∀ k, J1Decomposition ((Z (f (k + 1))).val - (Z (f k)).val) F mu)
        (Q : ∀ k, LocalMartingaleQuadraticVariation (D k).N F mu),
        (∑' k, (D k).r1Cost (Q k)) ≤ 2 ∧
        LocalMartingale (fun t w => ∑' k, (D k).N t w) F mu ∧
        (∀ᵐ w ∂mu,
          LocallyBoundedVariationOn (fun t => ∑' k, (D k).A t w) univ ∧
          ∀ T : NNReal,
            TendstoUniformlyOn (fun n t => ∑ k ∈ Finset.range n, (D k).A t w)
              (fun t => ∑' k, (D k).A t w) atTop (Icc 0 T) ∧
            Tendsto (fun n => eVariationOn (fun t => (∑' k, (D k).A t w) -
              ∑ k ∈ Finset.range n, (D k).A t w) (Icc 0 T)) atTop (𝓝 0)) ∧
        ∃ M : Process Ω, StronglyAdapted F M ∧ LocalMartingale M F mu ∧
          (∀ w t, ContinuousWithinAt (M · w) (Ici t) t) ∧ ProcessHasLeftLimits M ∧
          M 0 = 0 ∧ ProcessIndistinguishable mu M (fun t w => ∑' k, (D k).N t w) ∧
          boundedStoppingJumpCost M F mu ≤ ∑' k, boundedStoppingJumpCost (D k).N F mu ∧
          Tendsto (fun n => boundedStoppingJumpCost
            (fun t w => M t w - ∑ k ∈ Finset.range n, (D k).N t w) F mu) atTop (𝓝 0) ∧
        ∃ A : Process Ω, StronglyAdapted F A ∧
          (∀ w t, ContinuousWithinAt (A · w) (Ici t) t) ∧ ProcessHasLeftLimits A ∧
          (∀ w, LocallyBoundedVariationOn (A · w) univ) ∧ A 0 = 0 ∧
          ProcessIndistinguishable mu A (fun t w => ∑' k, (D k).A t w) ∧
          (∀ T : NNReal, Tendsto (fun n => ∫⁻ w, min (eVariationOn
            (fun t => A t w - ∑ k ∈ Finset.range n, (D k).A t w) (Icc 0 T)) 1 ∂mu)
              atTop (𝓝 0)) ∧
        ∃ P : ∀ n, LocalMartingaleQuadraticVariation
            (fun t w => M t w - ∑ k ∈ Finset.range n, (D k).N t w) F mu,
          (∀ T : NNReal, Tendsto (fun n => ∫⁻ w,
            min (ENNReal.ofReal (Real.sqrt ((P n).variation T w))) 1 ∂mu) atTop (𝓝 0)) ∧
        ∃ tau : Nat → Ω → NNReal,
          IsLocalizingSequence F (fun r w => (tau r w : WithTop NNReal)) mu ∧
          (∀ r w, tau r w ≤ ((r + 1 : Nat) : NNReal)) ∧
          ∀ r, (∑' k, ((∫⁻ w, ENNReal.ofReal (Real.sqrt
              ((Q k).variation (tau r w) w)) ∂mu) +
            ∫⁻ w, eVariationOn (strictPrefixProcess (D k).A (tau r) · w) univ ∂mu)) ≤
            (r + 3 : Nat) ∧
            Martingale (stoppedProcess (fun t w => ∑' k, (D k).N t w)
              (fun w => (tau r w : WithTop NNReal))) F mu ∧
            Tendsto (fun n => ∫⁻ w, ENNReal.ofReal
              (Real.sqrt ((P n).variation (tau r w) w)) ∂mu) atTop (𝓝 0) := by
  let : F.IsRightContinuous := hUsual.out.rightContinuous
  obtain ⟨f, hf, hSum⟩ := R1Process.exists_strictMono_summable_differences_of_cauchy h
  obtain ⟨D, Q, hCost, hFinite⟩ := exists_summable_r1Cost_decompositions
    (ne_top_of_le_ne_top (by norm_num) hSum)
  have hTwo : (∑' k, (D k).r1Cost (Q k)) ≤ 2 := by
    apply hCost.trans
    simpa only [one_add_one_eq_two] using add_le_add hSum (le_rfl : (1 : ENNReal) ≤ 1)
  obtain ⟨tau, hLoc, hT, hRows⟩ :=
    J1Decomposition.exists_common_localizers_summable_component_costs hUsual.out D Q hFinite
  have hRoot : ∀ r, (∑' k, ∫⁻ w, ENNReal.ofReal
      (Real.sqrt ((Q k).variation (tau r w) w)) ∂mu) ≠ ∞ := by
    intro r
    apply ne_top_of_le_ne_top (show
      ((r + 1 : Nat) : ENNReal) + (∑' k, (D k).r1Cost (Q k)) ≠ ∞ from
        ENNReal.add_ne_top.mpr ⟨by simp, hFinite⟩)
    exact (ENNReal.tsum_le_tsum (fun _ => le_add_right le_rfl)).trans (hRows r)
  have hSeries := fun r => (J1Decomposition.martingale_tsum_stopped_of_summable_roots
    D Q hUsual.out (hLoc.isStoppingTime r) (hT r) (hRoot r)).1
  have hLocal : LocalMartingale (fun t w => ∑' k, (D k).N t w) F mu := by
    apply LocalMartingale.of_closed_stops_of_zero _ _ hLoc hSeries
    funext w
    simp only [(D _).zeroN, Pi.zero_apply, tsum_zero]
  obtain ⟨A, hAA, hAR, hAL, hAV, hAZ, hAEq⟩ :=
    J1Decomposition.exists_regular_variation_series D Q hUsual.out hFinite
  obtain ⟨M, hMA, hMM, hMR, hML, hMZ, hMEq, hMJump, hMTail⟩ :=
    J1Decomposition.exists_regular_martingale_series D Q hUsual.out hLoc hT hRoot
  obtain ⟨P, hPTail⟩ := J1Decomposition.exists_quadratic_series_tails
    D Q hMM hMA hMR hML hMZ hMEq hUsual.out
  have hPStop := fun r => hPTail (tau r) ((r + 1 : Nat) : NNReal)
    (hLoc.isStoppingTime r) (hT r) (hRoot r)
  have hJumpSum := (J1Decomposition.capped_and_jump_summable_of_r1Cost D Q hFinite).2
  have hJumpLimit := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (ENNReal.tendsto_sum_nat_add (fun k => boundedStoppingJumpCost (D k).N F mu) hJumpSum)
    (fun _ => bot_le) hMTail
  refine ⟨f, hf, D, Q, hTwo, hLocal,
    J1Decomposition.ae_variation_series_of_summable_r1Cost D Q hFinite,
    M, hMA, hMM, hMR, hML, hMZ, hMEq, hMJump, hJumpLimit,
    A, hAA, hAR, hAL, hAV, hAZ, hAEq,
    J1Decomposition.tendsto_capped_variation_series_tail D Q hFinite hAA hAR hAEq,
    P, LocalMartingaleQuadraticVariation.tendsto_capped_root_of_localized P hLoc hPStop,
    tau, hLoc, hT, ?_⟩
  intro r
  have hBound := add_le_add (le_rfl : ((r + 1 : Nat) : ENNReal) ≤ _) hTwo
  have hRow : (∑' k, ((∫⁻ w, ENNReal.ofReal (Real.sqrt
          ((Q k).variation (tau r w) w)) ∂mu) +
        ∫⁻ w, eVariationOn (strictPrefixProcess (D k).A (tau r) · w) univ ∂mu)) ≤
      (r + 3 : Nat) := by
    apply (hRows r).trans
    convert hBound using 1
    norm_num [Nat.cast_add, add_assoc]
  exact ⟨hRow, hSeries r, hPStop r⟩

end FTAPTheorem42
