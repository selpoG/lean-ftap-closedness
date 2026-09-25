/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Topology.J1.Boundary

/-! # The factor-two strict-prefix bound for j1 -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace FTAPTheorem42

open SIntegrableFiniteVariationBridge RightContinuousStoppedMartingale

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  {X : Process Ω} {tau : Ω → NNReal} {T : NNReal}

omit [MeasurableSpace Ω] in
theorem strictPrefixProcess_eq_of_agree_before {U V : Process Ω}
    (hU : ProcessHasLeftLimits U) (w : Ω)
    (hZero : U 0 w = V 0 w) (h : ∀ t, t < tau w → U t w = V t w) :
    ∀ t, strictPrefixProcess U tau t w = strictPrefixProcess V tau t w := by
  have hLeft : Function.leftLim (U · w) (tau w) = Function.leftLim (V · w) (tau w) := by
    by_cases hz : tau w = 0
    · rw [hz, leftLim_eq_of_isBot (f := (U · w)) (a := (0 : NNReal)) isBot_bot,
        leftLim_eq_of_isBot (f := (V · w)) (a := (0 : NNReal)) isBot_bot, hZero]
    · let : NeBot (𝓝[<] tau w) :=
        nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr hz⟩
      symm
      apply leftLim_eq_of_tendsto
      apply (hU w (tau w)).congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact h s hs
  intro t
  by_cases ht : t < tau w
  · rw [strictPrefixProcess_eq_of_lt U tau ht, strictPrefixProcess_eq_of_lt V tau ht, h t ht]
  · rw [strictPrefixProcess_eq_of_ge U tau (le_of_not_gt ht),
      strictPrefixProcess_eq_of_ge V tau (le_of_not_gt ht), hLeft]

theorem LocalMartingaleQuadraticVariation.abs_jump_le_root
    (Q : LocalMartingaleQuadraticVariation X F mu) :
    ∀ᵐ w ∂mu, ∀ t, |processLeftJump X t w| ≤ Real.sqrt (Q.variation t w) := by
  filter_upwards [Q.jump_sq] with w hw
  intro t
  have hLeft : 0 ≤ Function.leftLim (Q.variation · w) t := by
    by_cases ht : t = 0
    · rw [ht, leftLim_eq_of_isBot (f := (Q.variation · w)) (a := (0 : NNReal)) isBot_bot, Q.zero]
      exact le_rfl
    · have h := (Q.monotone w).le_leftLim (pos_iff_ne_zero.mpr ht)
      simpa only [Q.zero, Pi.zero_apply] using h
  have hSq : (processLeftJump X t w) ^ 2 ≤ Q.variation t w := by
    rw [← hw t]
    exact sub_le_self _ hLeft
  simpa only [Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt hSq

variable [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]

theorem J1Decomposition.strictPrefix_cost_le (D : J1Decomposition X F mu)
    (hUsual : Filtration.UsualConditions mu F)
    (hTau : IsStoppingTime F (fun w => (tau w : WithTop NNReal)))
    (hTauT : ∀ w, tau w ≤ T) :
    semimartingaleJ1 (strictPrefixProcess X tau) F mu ≤ 2 * D.cost := by
  obtain ⟨Q, _⟩ := exists_unique_localMartingaleQuadraticVariation
    D.localMartingale D.adaptedN D.rightN D.leftN D.zeroN hUsual
  let A := deterministicallyStoppedProcess D.A T
  have hAA : StronglyAdapted F A :=
    StronglyAdapted.stoppedProcess_of_rightContinuous D.adaptedA (isStoppingTime_const F T) D.rightA
  have hAR := stoppedProcess_rightContinuous D.A D.rightA (τ := fun _ => (T : WithTop NNReal))
  have hAL : ProcessHasLeftLimits A := D.leftA.stoppedProcess _
  have hAV : ∀ w, BoundedVariationOn (A · w) univ := fun w =>
    FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn
      (D.variationA w) T
  have hAZero : A 0 = 0 := by
    funext w
    change D.A (min 0 T) w = 0
    rw [min_eq_left (show (0 : NNReal) ≤ T from bot_le)]
    exact congrFun D.zeroA w
  have hPrefix : ∀ w t, strictPrefixProcess A tau t w = strictPrefixProcess D.A tau t w := by
    intro w
    apply strictPrefixProcess_eq_of_agree_before hAL w
    · simp only [hAZero, D.zeroA, Pi.zero_apply]
    · intro t ht
      change D.A (min t T) w = D.A t w
      rw [min_eq_left (ht.le.trans (hTauT w))]
  let B := strictPrefixBoundaryRemainder D.N A tau
  let E : J1Decomposition (strictPrefixProcess X tau) F mu := {
    N := stoppedProcess D.N (fun w => (tau w : WithTop NNReal))
    A := B
    decomposition := by
      filter_upwards [D.decomposition] with w hw
      have hEq : ∀ t, strictPrefixProcess X tau t w =
          strictPrefixProcess (fun t w => D.N t w + D.A t w) tau t w := by
        intro t
        by_cases ht : t < tau w
        · rw [strictPrefixProcess_eq_of_lt X tau ht,
            strictPrefixProcess_eq_of_lt _ tau ht, hw t]
        · rw [strictPrefixProcess_eq_of_ge X tau (le_of_not_gt ht),
            strictPrefixProcess_eq_of_ge _ tau (le_of_not_gt ht)]
          exact congrArg (fun f => Function.leftLim f (tau w)) (funext hw)
      intro t
      rw [hEq t, strictPrefixProcess_add_boundaryJumpProcess_eq_stoppedParts tau D.leftN D.leftA]
      dsimp only [B, strictPrefixBoundaryRemainder]
      rw [hPrefix, hAZero]
      simp only [Pi.zero_apply]
      ring
    localMartingale := D.localMartingale.stoppedProcess_of_zero_of_rightContinuous
      D.zeroN D.rightN hTau
    adaptedN := StronglyAdapted.stoppedProcess_of_rightContinuous D.adaptedN hTau D.rightN
    rightN := stoppedProcess_rightContinuous D.N D.rightN
    leftN := D.leftN.stoppedProcess _
    zeroN := (D.stopped hTau).zeroN
    adaptedA := strictPrefixBoundaryRemainder_stronglyAdapted
      D.adaptedN D.rightN D.leftN hAA hAR hAL hTau
    rightA := strictPrefixBoundaryRemainder_rightContinuous hAR
    leftA := strictPrefixBoundaryRemainder_hasLeftLimits hAL
    variationA := by
      intro w
      have h := strictPrefixBoundaryRemainder_boundedVariation (N := D.N) (tau := tau) hAV w
      exact h.locallyBoundedVariationOn
    zeroA := strictPrefixBoundaryRemainder_zero D.N A tau }
  have hStrict : ∀ w, eVariationOn (strictPrefixProcess A tau · w) univ ≤
      eVariationOn (D.A · w) univ := by
    intro w
    have hBefore : ∀ t, t < tau w → variationOnFromTo (A · w) univ 0 t ≤
        (eVariationOn (A · w) univ).toReal := by
      intro t _
      rw [variationOnFromTo.eq_of_le _ _ (show (0 : NNReal) ≤ t from bot_le)]
      exact ENNReal.toReal_mono (hAV w) (eVariationOn.mono _ inter_subset_left)
    apply (strictPrefixProcess_variation_le_of_before A tau w (hAV w) hBefore).trans
    rw [ENNReal.ofReal_toReal (hAV w)]
    exact eVariationOn.comp_le_of_monotoneOn (D.A · w) (fun t => min t T)
      ((FiniteVariationStoppedPath.monotone_clamp T).monotoneOn univ) (mapsTo_univ _ _)
  have hVar : ∀ᵐ w ∂mu, eVariationOn (B · w) univ ≤ eVariationOn (D.A · w) univ +
      ⨆ t : NNReal, ENNReal.ofReal (Real.sqrt (Q.variation t w)) := by
    filter_upwards [Q.abs_jump_le_root] with w hw
    have hB : (B · w) = fun t => strictPrefixProcess A tau t w +
        -boundaryJumpProcess D.N tau t w := by
      funext t
      dsimp only [B, strictPrefixBoundaryRemainder]
      rw [hAZero]
      change _ - (0 : Real) = _
      ring
    have hNeg : eVariationOn (fun t => -boundaryJumpProcess D.N tau t w) univ =
        eVariationOn (boundaryJumpProcess D.N tau · w) univ := by
      rw [eVariationOn]
      congr 1
      funext p
      congr 1
      funext i
      rw [edist_neg_neg]
    rw [hB]
    apply (eVariationOn_add_le_real _ _ _).trans
    rw [hNeg]
    exact add_le_add (hStrict w)
      ((boundaryJumpProcess_eVariationOn_univ_le tau hTauT w).trans
        ((ENNReal.ofReal_le_ofReal (hw (tau w))).trans
          (le_iSup (fun t : NNReal => ENNReal.ofReal (Real.sqrt (Q.variation t w))) (tau w))))
  apply (iInf_le _ E).trans
  rw [E.cost_eq hUsual (Q.stopped D.rightN D.leftN D.zeroN hTau), D.cost_eq hUsual Q]
  have hRoot : (∫⁻ w, ⨆ t : NNReal, ENNReal.ofReal
      (Real.sqrt ((Q.stopped D.rightN D.leftN D.zeroN hTau).variation t w)) ∂mu) ≤
      ∫⁻ w, ⨆ t : NNReal, ENNReal.ofReal (Real.sqrt (Q.variation t w)) ∂mu := by
    apply lintegral_mono
    intro w
    apply iSup_le
    intro t
    exact le_iSup (fun s : NNReal => ENNReal.ofReal (Real.sqrt (Q.variation s w)))
      (boundedTime t (fun w => (tau w : WithTop NNReal)) w)
  have hVarInt := lintegral_mono_ae hVar
  rw [lintegral_add_right _ Q.measurable_allTimeRoot] at hVarInt
  exact (add_le_add hRoot hVarInt).trans (by
    rw [two_mul]
    calc
      _ ≤ _ + ∫⁻ w, eVariationOn (D.A · w) univ ∂mu := le_self_add
      _ = _ := by ac_rfl)

theorem semimartingaleJ1_strictPrefix_le_two_mul_prelocal
    (hUsual : Filtration.UsualConditions mu F) (hZero : X 0 = 0)
    (hTau : IsStoppingTime F (fun w => (tau w : WithTop NNReal)))
    (hTauT : ∀ w, tau w ≤ T) :
    semimartingaleJ1 (strictPrefixProcess X tau) F mu ≤
      2 * prelocalSemimartingaleJ1 X F mu (fun w => (tau w : WithTop NNReal)) := by
  unfold prelocalSemimartingaleJ1
  rw [ENNReal.mul_iInf_of_ne (by norm_num : (2 : ENNReal) ≠ 0)
    (by norm_num : (2 : ENNReal) ≠ ∞)]
  apply le_iInf
  intro Y
  rw [ENNReal.mul_iInf_of_ne (by norm_num : (2 : ENNReal) ≠ 0)
    (by norm_num : (2 : ENNReal) ≠ ∞)]
  apply le_iInf
  intro hY
  change _ ≤ 2 * ⨅ D : J1Decomposition Y F mu, D.cost
  rw [ENNReal.mul_iInf_of_ne (by norm_num : (2 : ENNReal) ≠ 0)
    (by norm_num : (2 : ENNReal) ≠ ∞)]
  apply le_iInf
  intro D
  have hEq : ProcessIndistinguishable mu (strictPrefixProcess X tau)
      (strictPrefixProcess Y tau) := by
    filter_upwards [hY, D.decomposition] with w hy hd
    let U : Process Ω := fun t w => D.N t w + D.A t w
    have hUZ : U 0 w = 0 := by simp only [U, D.zeroN, D.zeroA, Pi.zero_apply, add_zero]
    have hUX := strictPrefixProcess_eq_of_agree_before (D.leftN.add D.leftA) w
      (show U 0 w = X 0 w by rw [hUZ, hZero]; rfl)
      (fun t ht => (hd t).symm.trans (hy t (WithTop.coe_lt_coe.mpr ht)))
    have hUY := strictPrefixProcess_eq_of_agree_before (tau := tau) (D.leftN.add D.leftA) w
      (hd 0).symm (fun t _ => (hd t).symm)
    exact fun t => (hUX t).symm.trans (hUY t)
  rw [semimartingaleJ1_congr hEq]
  exact D.strictPrefix_cost_le hUsual hTau hTauT

theorem semimartingaleJ1_stopped_le_two_mul_prelocal_add_jump
    (hUsual : Filtration.UsualConditions mu F) (hZero : X 0 = 0)
    (hX : StronglyAdapted F X)
    (hRight : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X)
    (hTau : IsStoppingTime F (fun w => (tau w : WithTop NNReal)))
    (hTauT : ∀ w, tau w ≤ T) :
    semimartingaleJ1 (stoppedProcess X (fun w => (tau w : WithTop NNReal))) F mu ≤
      2 * prelocalSemimartingaleJ1 X F mu (fun w => (tau w : WithTop NNReal)) +
        ∫⁻ w, ENNReal.ofReal |processLeftJump X (tau w) w| ∂mu :=
  (semimartingaleJ1_stopped_le_strictPrefix_add_jump hUsual hX hRight hLeft hTau hTauT).trans
    (add_le_add_left (semimartingaleJ1_strictPrefix_le_two_mul_prelocal
      hUsual hZero hTau hTauT) _)

end FTAPTheorem42
