/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.R1.JumpLimit

/-! # Summing the same global martingale components after a common stop -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]

theorem J1Decomposition.martingale_tsum_stopped_of_summable_roots
    {Z : Nat → Process Ω} (D : ∀ k, J1Decomposition (Z k) F mu)
    (Q : ∀ k, LocalMartingaleQuadraticVariation (D k).N F mu)
    (hUsual : Filtration.UsualConditions mu F)
    {tau : Ω → NNReal} {T : NNReal}
    (hTau : IsStoppingTime F (fun w => (tau w : WithTop NNReal)))
    (hTauT : ∀ w, tau w ≤ T)
    (hSum : (∑' k, ∫⁻ w, ENNReal.ofReal (Real.sqrt ((Q k).variation (tau w) w)) ∂mu) ≠ ∞) :
    Martingale (stoppedProcess (fun t w => ∑' k, (D k).N t w)
      (fun w => (tau w : WithTop NNReal))) F mu ∧
      ∀ᵐ w ∂mu, TendstoUniformly
        (fun n t => ∑ k ∈ Finset.range n, stoppedProcess (D k).N
          (fun w => (tau w : WithTop NNReal)) t w)
        (fun t => stoppedProcess (fun t w => ∑' k, (D k).N t w)
          (fun w => (tau w : WithTop NNReal)) t w) atTop := by
  let E := fun k => (D k).stopped hTau
  let M := fun k => (E k).N
  let g := fun k => FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope (M k) T
  have hMeas : ∀ k, StronglyMeasurable (g k) := fun k =>
    (FactorialChronologicalGrid.stronglyMeasurable_finiteHorizonAbsoluteEnvelope
      (E k).adaptedN T).mono (F.le T)
  have hBound : ∀ k w t, |M k t w| ≤ g k w := by
    intro k w t
    have hClip : M k (min t T) w = M k t w := by
      have h := congrFun (congrFun (stoppedProcess_stoppedProcess_of_le_left
        (u := (D k).N) (fun w => WithTop.coe_le_coe.mpr (hTauT w))) t) w
      simpa only [M, E, J1Decomposition.stopped, stoppedProcess_const_apply] using h
    rw [← hClip]
    exact FactorialChronologicalGrid.abs_le_finiteHorizonAbsoluteEnvelope_of_cadlag
      (E k).rightN (E k).leftN T (min t T) (min_le_right _ _)
  have hCost : ∀ k, (∫⁻ w, ENNReal.ofReal (g k w) ∂mu) ≤
      6 * ∫⁻ w, ENNReal.ofReal (Real.sqrt ((Q k).variation (tau w) w)) ∂mu := by
    intro k
    let P := (Q k).stopped (D k).rightN (D k).leftN (D k).zeroN hTau
    apply le_trans _ (P.lintegral_allTime_maximal_le_six_root (E k).localMartingale
      (E k).adaptedN (E k).rightN (E k).leftN (E k).zeroN hUsual)
      |>.trans_eq ?_
    · apply lintegral_mono
      intro w
      change ENNReal.ofReal (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
        (M k) T w) ≤ ⨆ t : NNReal, ENNReal.ofReal |M k t w|
      rw [FactorialChronologicalGrid.ofReal_finiteHorizonAbsoluteEnvelope_eq_iSup
        (E k).rightN (E k).leftN T]
      exact iSup_le (fun t => le_iSup (fun s => ENNReal.ofReal |M k s w|) t.1)
    · congr 1
      apply lintegral_congr
      intro w
      exact (Q k).stopped_allTimeRoot_eq (D k).rightN (D k).leftN (D k).zeroN hTau w
  have hGSum : (∑' k, ∫⁻ w, ENNReal.ofReal (g k w) ∂mu) ≠ ∞ := by
    apply ne_top_of_le_ne_top (ENNReal.mul_ne_top (a := (6 : ENNReal)) (by norm_num) hSum)
    calc
      _ ≤ ∑' k, 6 * ∫⁻ w, ENNReal.ofReal (Real.sqrt ((Q k).variation (tau w) w)) ∂mu :=
        ENNReal.tsum_le_tsum hCost
      _ = _ := ENNReal.tsum_mul_left
  have hInt : ∀ k, Integrable (g k) mu := fun k =>
    (lintegral_ofReal_ne_top_iff_integrable (hMeas k).aestronglyMeasurable
      (Eventually.of_forall (fun _ => Real.sqrt_nonneg _))).mp
      (ne_top_of_le_ne_top hGSum
        (ENNReal.le_tsum (f := fun k => ∫⁻ w, ENNReal.ofReal (g k w) ∂mu) k))
  refine ⟨?_, ae_uniform_series_of_summable_envelopes M g
    (fun k => (hMeas k).measurable) (fun _ _ => Real.sqrt_nonneg _) hBound hGSum⟩
  exact martingale_tsum_of_summable_envelopes M g
    (fun k => LocalMartingale.martingale_of_integrable_bound (E k).localMartingale
      (E k).adaptedN (g k) (hInt k) (Eventually.of_forall (hBound k)))
    (fun k => (hMeas k).measurable) (fun _ _ => Real.sqrt_nonneg _) hBound hGSum

/-! ## Regularizing the same global martingale series through its common stops -/

theorem J1Decomposition.exists_regular_martingale_series
    {Z : Nat → Process Ω} (D : ∀ k, J1Decomposition (Z k) F mu)
    (Q : ∀ k, LocalMartingaleQuadraticVariation (D k).N F mu)
    (hUsual : Filtration.UsualConditions mu F)
    {tau : Nat → Ω → NNReal}
    (hLoc : IsLocalizingSequence F (fun r w => (tau r w : WithTop NNReal)) mu)
    (hT : ∀ r w, tau r w ≤ ((r + 1 : Nat) : NNReal))
    (hSum : ∀ r, (∑' k, ∫⁻ w, ENNReal.ofReal (Real.sqrt
      ((Q k).variation (tau r w) w)) ∂mu) ≠ ∞) :
    ∃ M : Process Ω, StronglyAdapted F M ∧ LocalMartingale M F mu ∧
      (∀ w t, ContinuousWithinAt (M · w) (Ici t) t) ∧ ProcessHasLeftLimits M ∧
      M 0 = 0 ∧ ProcessIndistinguishable mu M (fun t w => ∑' k, (D k).N t w) ∧
      boundedStoppingJumpCost M F mu ≤ ∑' k, boundedStoppingJumpCost (D k).N F mu ∧
      ∀ n, boundedStoppingJumpCost
        (fun t w => M t w - ∑ k ∈ Finset.range n, (D k).N t w) F mu ≤
        ∑' k, boundedStoppingJumpCost (D (k + n)).N F mu := by
  let X : Process Ω := fun t w => ∑' k, (D k).N t w
  let Y := fun r => stoppedProcess X (fun w => (tau r w : WithTop NNReal))
  have hRows := fun r => J1Decomposition.martingale_tsum_stopped_of_summable_roots
    D Q hUsual (hLoc.isStoppingTime r) (hT r) (hSum r)
  have hZero : X 0 = 0 := by funext w; simp only [X, (D _).zeroN, Pi.zero_apply, tsum_zero]
  have hLocal : LocalMartingale X F mu :=
    LocalMartingale.of_closed_stops_of_zero hZero _ hLoc (fun r => (hRows r).1)
  have hAdapted : StronglyAdapted F X := by
    intro t
    have hMeas : ∀ k, @Measurable Ω Real (F t) _ ((D k).N t) :=
      fun k => ((D k).adaptedN t).measurable
    let : MeasurableSpace Ω := F t
    exact (Measurable.tsum hMeas).stronglyMeasurable
  have hRegRows : ∀ r, ∀ᵐ w ∂mu,
      (∀ t, ContinuousWithinAt (Y r · w) (Ici t) t) ∧
      ∀ t, Tendsto (Y r · w) (𝓝[<] t) (𝓝 (Function.leftLim (Y r · w) t)) := by
    intro r
    filter_upwards [(hRows r).2] with w hw
    let P := fun n t => ∑ k ∈ Finset.range n,
      stoppedProcess (D k).N (fun w => (tau r w : WithTop NNReal)) t w
    have hPR : ∀ n t, ContinuousWithinAt (P n) (Ici t) t := by
      intro n t
      induction n with
      | zero => exact continuousWithinAt_const
      | succ n ih =>
        have hEq : P (n + 1) = P n +
            (fun s => ((D n).stopped (hLoc.isStoppingTime r)).N s w) := by
          funext s
          exact Finset.sum_range_succ _ _
        rw [hEq]
        exact ih.add (((D n).stopped (hLoc.isStoppingTime r)).rightN w t)
    have hPL : ∀ n t, Tendsto (P n) (𝓝[<] t) (𝓝 (Function.leftLim (P n) t)) := by
      intro n t
      induction n with
      | zero => exact tendsto_leftLim_of_tendsto ⟨0, tendsto_const_nhds⟩
      | succ n ih =>
        apply tendsto_leftLim_of_tendsto
        refine ⟨Function.leftLim (P n) t +
          Function.leftLim (((D n).stopped (hLoc.isStoppingTime r)).N · w) t, ?_⟩
        simpa only [P, Finset.sum_range_succ, J1Decomposition.stopped] using
          ih.add (((D n).stopped (hLoc.isStoppingTime r)).leftN w t)
    exact ⟨rightContinuous_of_tendstoUniformly P _ hw hPR,
      leftLimits_of_tendstoUniformly P _ hw hPL⟩
  have hRegular : ∀ᵐ w ∂mu,
      (∀ t, ContinuousWithinAt (X · w) (Ici t) t) ∧
      ∀ t, Tendsto (X · w) (𝓝[<] t) (𝓝 (Function.leftLim (X · w) t)) := by
    filter_upwards [ae_all_iff.mpr hRegRows, hLoc.tendsto_top] with w hw hTop
    rw [WithTop.tendsto_nhds_top_iff] at hTop
    have hEq (t : NNReal) : ∃ r, ∀ s, s < t + 1 → X s w = Y r s w := by
      obtain ⟨r, hr⟩ := (hTop (t + 1)).exists
      refine ⟨r, fun s hs => ?_⟩
      exact (stoppedProcess_eq_of_le (u := X) (τ := fun w => (tau r w : WithTop NNReal))
        ((WithTop.coe_le_coe.mpr hs.le).trans hr.le)).symm
    constructor
    · intro t
      obtain ⟨r, hr⟩ := hEq t
      have hNear : (X · w) =ᶠ[𝓝[Ici t] t] (Y r · w) := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_add_one t))] with s hs
        exact hr s hs
      exact (hw r).1 t |>.congr_of_eventuallyEq hNear (hr t (lt_add_one t))
    · intro t
      obtain ⟨r, hr⟩ := hEq t
      have hNear : (X · w) =ᶠ[𝓝[<] t] (Y r · w) := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact hr s (hs.trans (lt_add_one t))
      exact tendsto_leftLim_of_tendsto ⟨_, ((hw r).2 t).congr' hNear.symm⟩
  let bad := {w | ¬((∀ t, ContinuousWithinAt (X · w) (Ici t) t) ∧
    ∀ t, Tendsto (X · w) (𝓝[<] t) (𝓝 (Function.leftLim (X · w) t)))}
  have hNull : mu bad = 0 := ae_iff.mp hRegular
  have hOff : ∀ w, w ∉ bad →
      (∀ t, ContinuousWithinAt (X · w) (Ici t) t) ∧
      ∀ t, Tendsto (X · w) (𝓝[<] t) (𝓝 (Function.leftLim (X · w) t)) := by
    intro w hw
    simpa only [bad, mem_ofPred_eq, not_not] using hw
  let M := ProcessNullSetRegularization.zeroOn bad X
  have hMA : StronglyAdapted F M := ProcessNullSetRegularization.stronglyAdapted_zeroOn
    (hUsual.containsNullSetsAtZero bad hNull) hAdapted
  have hEq := ProcessNullSetRegularization.zeroOn_indistinguishable hNull X
  have hMR : ∀ w t, ContinuousWithinAt (M · w) (Ici t) t :=
    ProcessNullSetRegularization.zeroOn_isRightContinuous (fun w hw => (hOff w hw).1)
  have hML : ProcessHasLeftLimits M :=
    ProcessNullSetRegularization.zeroOn_hasLeftLimits (fun w hw => (hOff w hw).2)
  have hUniform : ∀ᵐ w ∂mu, ∀ T : NNReal, TendstoUniformlyOn
      (fun n t => ∑ k ∈ Finset.range n, (D k).N t w) (M · w) atTop (Icc 0 T) := by
    filter_upwards [ae_all_iff.mpr (fun r => (hRows r).2), hLoc.tendsto_top, hEq]
      with w hw hTop heq
    intro T
    rw [WithTop.tendsto_nhds_top_iff] at hTop
    obtain ⟨r, hr⟩ := (hTop T).exists
    have hStop : ∀ k t, t ∈ Icc 0 T →
        stoppedProcess (D k).N (fun w => (tau r w : WithTop NNReal)) t w = (D k).N t w := by
      intro k t ht
      exact stoppedProcess_eq_of_le ((WithTop.coe_le_coe.mpr ht.2).trans hr.le)
    have hU := (hw r).tendstoUniformlyOn.congr
      (Eventually.of_forall (fun n t ht => Finset.sum_congr rfl (fun k _ => hStop k t ht)))
    apply hU.congr_right
    intro t ht
    change (∑' k, stoppedProcess (D k).N (fun w => (tau r w : WithTop NNReal)) t w) = M t w
    change ∀ t, M t w = ∑' k, (D k).N t w at heq
    rw [heq t]
    exact tsum_congr (fun k => hStop k t ht)
  refine ⟨M, hMA, hLocal.congr_indistinguishable hMA hMR hEq.symm, hMR, hML, ?_, hEq,
    J1Decomposition.jumpCost_series_le D hML hUniform,
    J1Decomposition.jumpCost_series_tail_le D hML hUniform⟩
  funext w
  simp only [M, ProcessNullSetRegularization.zeroOn, hZero, Pi.zero_apply, ite_self]

end FTAPTheorem42
