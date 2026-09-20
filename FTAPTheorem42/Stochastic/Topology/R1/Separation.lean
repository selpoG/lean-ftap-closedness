/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.R1.Basic

/-! # Indistinguishability and separation of the r1 core -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  {X Y : Process Ω}

theorem semimartingaleR1_congr (h : ProcessIndistinguishable mu X Y) :
    semimartingaleR1 X F mu = semimartingaleR1 Y F mu := by
  have hLe : ∀ U V : Process Ω, ProcessIndistinguishable mu U V →
      semimartingaleR1 U F mu ≤ semimartingaleR1 V F mu := by
    intro U V hUV
    apply le_iInf
    intro D
    apply le_iInf
    intro Q
    let E : J1Decomposition U F mu := { D with decomposition := hUV.trans D.decomposition }
    exact iInf_le_of_le E (iInf_le _ Q)
  exact le_antisymm (hLe X Y h) (hLe Y X h.symm)

variable [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] [F.IsRightContinuous]

private theorem exists_localizers_prelocalJ1_zero
    (hUsual : Filtration.UsualConditions mu F) (hZero : semimartingaleR1 X F mu = 0) :
    ∃ tau : Nat → Ω → NNReal,
      IsLocalizingSequence F (fun r w => (tau r w : WithTop NNReal)) mu ∧
      ∀ r, prelocalSemimartingaleJ1 X F mu (fun w => (tau r w : WithTop NNReal)) = 0 := by
  have hSum : (∑' _ : Nat, semimartingaleR1 X F mu) ≠ ∞ := by
    simp only [hZero, tsum_zero]
    exact ENNReal.zero_ne_top
  obtain ⟨D, Q, _, hFinite⟩ := exists_summable_r1Cost_decompositions hSum
  obtain ⟨hCap, hJump⟩ := J1Decomposition.capped_and_jump_summable_of_r1Cost D Q hFinite
  obtain ⟨tau, hLoc, hT, hRows⟩ :=
    J1Decomposition.exists_common_localizers_prelocal_cost_bound hUsual D Q hCap
  refine ⟨tau, hLoc, ?_⟩
  intro r
  have hFiniteJ : (∑' _ : Nat, prelocalSemimartingaleJ1 X F mu
      (fun w => (tau r w : WithTop NNReal))) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, hJump⟩)
      ((hRows r).trans (add_le_add le_rfl (ENNReal.tsum_le_tsum (fun _ =>
        lintegral_jump_le_boundedStoppingJumpCost (hLoc.isStoppingTime r) (hT r)))))
  exact tendsto_nhds_unique tendsto_const_nhds (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hFiniteJ)

omit [F.IsRightContinuous] in
private theorem ae_eq_zero_of_prelocalJ1_zero
    (hUsual : Filtration.UsualConditions mu F) (hX : StronglyAdapted F X)
    {tau : Ω → WithTop NNReal} (hTau : IsStoppingTime F tau)
    (hZero : prelocalSemimartingaleJ1 X F mu tau = 0) (t : NNReal) :
    ∀ᵐ w ∂mu, (t : WithTop NNReal) < tau w → X t w = 0 := by
  let s := {w | (t : WithTop NNReal) < tau w}
  have hs : MeasurableSet s := by
    have hMeas : MeasurableSet {w | tau w ≤ (t : WithTop NNReal)} :=
      F.le t _ (hTau.measurableSet_le t)
    simpa only [s, compl_ofPred, not_le] using hMeas.compl
  have hf : Measurable (s.indicator (fun w => ENNReal.ofReal |X t w|)) :=
    (((hX t).mono (F.le t)).measurable.abs.ennreal_ofReal).indicator hs
  have hInt : (∫⁻ w, s.indicator (fun w => ENNReal.ofReal |X t w|) w ∂mu) = 0 := by
    apply le_antisymm _ bot_le
    have hBound := lintegral_strictPrefix_maximal_le_six_prelocalSemimartingaleJ1
      (X := X) (tau := tau) hUsual
    rw [hZero, mul_zero] at hBound
    apply le_trans _ hBound
    apply lintegral_mono
    intro w
    by_cases hw : w ∈ s
    · rw [indicator_of_mem hw]
      exact le_iSup (fun u : {u : NNReal // (u : WithTop NNReal) < tau w} =>
        ENNReal.ofReal |X u.1 w|) ⟨t, hw⟩
    · rw [indicator_of_notMem hw]
      exact bot_le
  filter_upwards [(lintegral_eq_zero_iff hf).mp hInt] with w hw
  intro ht
  rw [indicator_of_mem (show w ∈ s from ht)] at hw
  exact abs_eq_zero.mp (le_antisymm (ENNReal.ofReal_eq_zero.mp hw) (abs_nonneg _))

private theorem indistinguishable_zero_of_regular_r1_zero
    (hUsual : Filtration.UsualConditions mu F) (hX : StronglyAdapted F X)
    (hRight : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hZero : semimartingaleR1 X F mu = 0) : ProcessIndistinguishable mu X 0 := by
  obtain ⟨tau, hLoc, hJ⟩ := exists_localizers_prelocalJ1_zero hUsual hZero
  have hEq (t : NNReal) : X t =ᵐ[mu] 0 := by
    have hAll : ∀ᵐ w ∂mu, ∀ r, (t : WithTop NNReal) < (tau r w : WithTop NNReal) →
        X t w = 0 := ae_all_iff.mpr (fun r =>
      ae_eq_zero_of_prelocalJ1_zero hUsual hX (hLoc.isStoppingTime r) (hJ r) t)
    filter_upwards [hLoc.tendsto_top, hAll] with w hTop hw
    rw [WithTop.tendsto_nhds_top_iff] at hTop
    obtain ⟨r, hr⟩ := (hTop t).exists
    exact hw r hr
  exact ProcessIndistinguishable.of_ae_eq_on_rightDense X 0
    NNRealRightDenseSkeleton.skeleton NNRealRightDenseSkeleton.skeleton_rightDense
    (Eventually.of_forall hRight) (Eventually.of_forall (fun _ _ => continuousWithinAt_const))
    (fun k => hEq _)

theorem indistinguishable_zero_of_semimartingaleR1_zero
    (hUsual : Filtration.UsualConditions mu F) (hZero : semimartingaleR1 X F mu = 0) :
    ProcessIndistinguishable mu X 0 := by
  have hSmall : semimartingaleR1 X F mu < 1 := by rw [hZero]; exact zero_lt_one
  obtain ⟨D, _⟩ := iInf_lt_iff.mp hSmall
  let Y : Process Ω := fun t w => D.N t w + D.A t w
  have hY : semimartingaleR1 Y F mu = 0 :=
    (semimartingaleR1_congr D.decomposition).symm.trans hZero
  exact D.decomposition.trans (indistinguishable_zero_of_regular_r1_zero hUsual
    (D.adaptedN.add D.adaptedA) (fun w t => (D.rightN w t).add (D.rightA w t)) hY)

omit [F.IsRightContinuous] [SigmaFiniteFiltration mu F] in
theorem semimartingaleR1_zero : semimartingaleR1 (0 : Process Ω) F mu = 0 := by
  let Q : LocalMartingaleQuadraticVariation (0 : Process Ω) F mu :=
    LocalMartingaleQuadraticVariation.zeroProcess
  let D : J1Decomposition (0 : Process Ω) F mu := {
    N := 0
    A := 0
    decomposition := Eventually.of_forall (fun _ _ => by simp)
    localMartingale := Locally.of_prop (martingale_zero Real F mu)
    adaptedN := Q.stronglyAdapted
    rightN := Q.rightContinuous
    leftN := Q.leftLimits
    zeroN := rfl
    adaptedA := Q.stronglyAdapted
    rightA := Q.rightContinuous
    leftA := Q.leftLimits
    variationA := Q.locallyBoundedVariation
    zeroA := rfl }
  have hJump : ∀ t w, processLeftJump (0 : Process Ω) t w = 0 := by
    intro t w
    change processLeftJump (fun _ _ => (0 : Real)) t w = 0
    simpa using processLeftJump_const_mul Q.leftLimits 0 t w
  have hVar (s : Set NNReal) : eVariationOn (fun _ : NNReal => (0 : Real)) s = 0 := by
    apply eVariationOn.constant_on
    rintro _ ⟨_, _, rfl⟩ _ ⟨_, _, rfl⟩
    rfl
  apply le_antisymm _ bot_le
  apply (iInf_le_of_le D (iInf_le _ Q)).trans_eq
  simp [J1Decomposition.r1Cost, boundedStoppingJumpCost, J1Decomposition.clock,
    D, Q, LocalMartingaleQuadraticVariation.zeroProcess, hJump, hVar]

theorem semimartingaleR1_eq_zero_iff (hUsual : Filtration.UsualConditions mu F) :
    semimartingaleR1 X F mu = 0 ↔ ProcessIndistinguishable mu X 0 := by
  constructor
  · exact indistinguishable_zero_of_semimartingaleR1_zero hUsual
  · intro h
    rw [semimartingaleR1_congr h, semimartingaleR1_zero]

theorem semimartingaleR1_sub_eq_zero_iff (hUsual : Filtration.UsualConditions mu F) :
    semimartingaleR1 (X - Y) F mu = 0 ↔ ProcessIndistinguishable mu X Y := by
  rw [semimartingaleR1_eq_zero_iff hUsual]
  constructor
  · intro h
    filter_upwards [h] with w hw
    exact fun t => sub_eq_zero.mp (hw t)
  · intro h
    filter_upwards [h] with w hw
    intro t
    exact sub_eq_zero.mpr (hw t)

end FTAPTheorem42
