/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.R1.Basic

/-! # Summable maximal functions on strict stochastic prefixes -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}

noncomputable def strictPrefixSkeletonMaximal (X : Process Ω) (tau : Ω → NNReal)
    (w : Ω) : ENNReal :=
  ⨆ n : Nat, if NNRealRightDenseSkeleton.skeleton n < tau w then
    ENNReal.ofReal |X (NNRealRightDenseSkeleton.skeleton n) w| else 0

theorem measurable_strictPrefixSkeletonMaximal {X : Process Ω} {tau : Ω → NNReal}
    (hX : StronglyAdapted F X)
    (hTau : IsStoppingTime F (fun w => (tau w : WithTop NNReal))) :
    Measurable (strictPrefixSkeletonMaximal X tau) := by
  apply Measurable.iSup
  intro n
  let t := NNRealRightDenseSkeleton.skeleton n
  have hs : MeasurableSet {w | t < tau w} := by
    have h : MeasurableSet {w | (tau w : WithTop NNReal) ≤ t} :=
      F.le t _ (hTau.measurableSet_le t)
    simpa only [compl_ofPred, not_le, WithTop.coe_lt_coe] using h.compl
  exact Measurable.ite hs (((hX t).mono (F.le t)).measurable.abs.ennreal_ofReal) measurable_const

omit [MeasurableSpace Ω] in
theorem ofReal_abs_le_strictPrefixSkeletonMaximal {X : Process Ω} {tau : Ω → NNReal}
    (hRight : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (w : Ω) {t : NNReal} (ht : t < tau w) :
    ENNReal.ofReal |X t w| ≤ strictPrefixSkeletonMaximal X tau w := by
  let s := range NNRealRightDenseSkeleton.skeleton ∩ Ici t
  have : NeBot (𝓝[s] t) := mem_closure_iff_nhdsWithin_neBot.mp
    (NNRealRightDenseSkeleton.skeleton_rightDense t)
  have hCont : ContinuousWithinAt (fun u => ENNReal.ofReal |X u w|) (Ici t) t :=
    ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt (hRight w t).abs
  apply le_of_tendsto (hCont.mono (show s ⊆ Ici t from inter_subset_right))
  filter_upwards [self_mem_nhdsWithin,
    (nhdsWithin_le_nhds : 𝓝[s] t ≤ 𝓝 t) (Iio_mem_nhds ht)] with u hu hBefore
  obtain ⟨n, rfl⟩ := hu.1
  exact le_iSup_of_le n (by
    rw [ite_eq_left (show NNRealRightDenseSkeleton.skeleton n < tau w from hBefore)])

variable [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]

theorem lintegral_strictPrefixSkeletonMaximal_le
    (hUsual : Filtration.UsualConditions mu F) (X : Process Ω) (tau : Ω → NNReal) :
    (∫⁻ w, strictPrefixSkeletonMaximal X tau w ∂mu) ≤
      6 * prelocalSemimartingaleJ1 X F mu (fun w => (tau w : WithTop NNReal)) := by
  apply le_trans _ (lintegral_strictPrefix_maximal_le_six_prelocalSemimartingaleJ1 hUsual)
  apply lintegral_mono
  intro w
  apply iSup_le
  intro n
  split_ifs with h
  · exact le_iSup (fun u : {u : NNReal // (u : WithTop NNReal) < (tau w : WithTop NNReal)} =>
      ENNReal.ofReal |X u.1 w|) ⟨_, WithTop.coe_lt_coe.mpr h⟩
  · exact bot_le

theorem ae_tsum_strictPrefixSkeletonMaximal_ne_top
    (hUsual : Filtration.UsualConditions mu F) {Z : Nat → Process Ω} {tau : Ω → NNReal}
    (hZ : ∀ k, StronglyAdapted F (Z k))
    (hTau : IsStoppingTime F (fun w => (tau w : WithTop NNReal)))
    (hSum : (∑' k, prelocalSemimartingaleJ1 (Z k) F mu
      (fun w => (tau w : WithTop NNReal))) ≠ ∞) :
    ∀ᵐ w ∂mu, (∑' k, strictPrefixSkeletonMaximal (Z k) tau w) ≠ ∞ := by
  have hMeas := fun k => measurable_strictPrefixSkeletonMaximal (hZ k) hTau
  have hInt : (∫⁻ w, ∑' k, strictPrefixSkeletonMaximal (Z k) tau w ∂mu) ≠ ∞ := by
    rw [lintegral_tsum (fun k => (hMeas k).aemeasurable)]
    apply ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num : (6 : ENNReal) ≠ ∞) hSum)
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum (fun k => lintegral_strictPrefixSkeletonMaximal_le hUsual (Z k) tau)
  filter_upwards [ae_lt_top (Measurable.tsum hMeas) hInt] with w hw
  exact hw.ne

theorem ae_tsum_maximal_ne_top_of_localizing_prelocalJ1
    (hUsual : Filtration.UsualConditions mu F) {Z : Nat → Process Ω}
    (hZ : ∀ k, StronglyAdapted F (Z k))
    (hRight : ∀ k w t, ContinuousWithinAt (Z k · w) (Ici t) t)
    {tau : Nat → Ω → NNReal}
    (hLoc : IsLocalizingSequence F (fun r w => (tau r w : WithTop NNReal)) mu)
    (hSum : ∀ r, (∑' k, prelocalSemimartingaleJ1 (Z k) F mu
      (fun w => (tau r w : WithTop NNReal))) ≠ ∞) :
    ∀ᵐ w ∂mu, ∀ T : NNReal, (∑' k, ⨆ t : Iic T, ENNReal.ofReal |Z k t.1 w|) ≠ ∞ := by
  have hAll := ae_all_iff.mpr (fun r => ae_tsum_strictPrefixSkeletonMaximal_ne_top
    hUsual hZ (hLoc.isStoppingTime r) (hSum r))
  filter_upwards [hAll, hLoc.tendsto_top] with w hw hTop
  intro T
  rw [WithTop.tendsto_nhds_top_iff] at hTop
  obtain ⟨r, hr⟩ := (hTop T).exists
  apply ne_top_of_le_ne_top (hw r)
  apply ENNReal.tsum_le_tsum
  intro k
  apply iSup_le
  intro t
  exact ofReal_abs_le_strictPrefixSkeletonMaximal (hRight k) w
    (t.2.trans_lt (WithTop.coe_lt_coe.mp hr))

theorem ae_tsum_maximal_ne_top_of_summable_r1
    [F.IsRightContinuous] (hUsual : Filtration.UsualConditions mu F) {Z : Nat → Process Ω}
    (hSum : (∑' k, semimartingaleR1 (Z k) F mu) ≠ ∞) :
    ∀ᵐ w ∂mu, ∀ T : NNReal, (∑' k, ⨆ t : Iic T, ENNReal.ofReal |Z k t.1 w|) ≠ ∞ := by
  obtain ⟨D, Q, _, hFinite⟩ := exists_summable_r1Cost_decompositions hSum
  let Y : Nat → Process Ω := fun k t w => (D k).N t w + (D k).A t w
  let E (k : Nat) : J1Decomposition (Y k) F mu := { D k with
    decomposition := Eventually.of_forall (fun _ _ => rfl) }
  have hEFinite : (∑' k, (E k).r1Cost (Q k)) ≠ ∞ := hFinite
  obtain ⟨hCap, hJump⟩ := J1Decomposition.capped_and_jump_summable_of_r1Cost E Q hEFinite
  obtain ⟨tau, hLoc, hT, hRows⟩ :=
    J1Decomposition.exists_common_localizers_prelocal_cost_bound hUsual E Q hCap
  have hJ : ∀ r, (∑' k, prelocalSemimartingaleJ1 (Y k) F mu
      (fun w => (tau r w : WithTop NNReal))) ≠ ∞ := by
    intro r
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, hJump⟩)
      ((hRows r).trans (add_le_add le_rfl (ENNReal.tsum_le_tsum (fun _ =>
        lintegral_jump_le_boundedStoppingJumpCost (hLoc.isStoppingTime r) (hT r)))))
  have hPath := ae_tsum_maximal_ne_top_of_localizing_prelocalJ1 hUsual
    (fun k => (D k).adaptedN.add (D k).adaptedA)
    (fun k w t => ((D k).rightN w t).add ((D k).rightA w t)) hLoc hJ
  have hAgree : ∀ᵐ w ∂mu, ∀ k t, Z k t w = Y k t w :=
    ae_all_iff.mpr (fun k => (D k).decomposition)
  filter_upwards [hPath, hAgree] with w hw hEq
  intro T
  have hT : (∑' k, ⨆ t : Iic T, ENNReal.ofReal |Y k t.1 w|) ≠ ∞ := hw T
  simpa only [hEq] using hT

theorem ae_tendsto_maximal_zero_of_summable_r1
    [F.IsRightContinuous] (hUsual : Filtration.UsualConditions mu F) {Z : Nat → Process Ω}
    (hSum : (∑' k, semimartingaleR1 (Z k) F mu) ≠ ∞) :
    ∀ᵐ w ∂mu, ∀ T : NNReal,
      Tendsto (fun k => ⨆ t : Iic T, ENNReal.ofReal |Z k t.1 w|) atTop (𝓝 0) := by
  filter_upwards [ae_tsum_maximal_ne_top_of_summable_r1 hUsual hSum] with w hw
  exact fun T => ENNReal.tendsto_atTop_zero_of_tsum_ne_top (hw T)

end FTAPTheorem42
