/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.J1.Triangle

/-! # The j1 cost of the actual boundary jump in a closed stop -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace FTAPTheorem42

open SIntegrableFiniteVariationBridge

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  {X Y : Process Ω}

theorem semimartingaleJ1_congr (h : ProcessIndistinguishable mu X Y) :
    semimartingaleJ1 X F mu = semimartingaleJ1 Y F mu := by
  have hLe : ∀ {U V : Process Ω}, ProcessIndistinguishable mu U V →
      semimartingaleJ1 U F mu ≤ semimartingaleJ1 V F mu := by
    intro U V hUV
    apply le_iInf
    intro D
    let E : J1Decomposition U F mu := { D with
      decomposition := by
        filter_upwards [hUV, D.decomposition] with w hw hd
        exact fun t => (hw t).trans (hd t) }
    exact iInf_le_of_le E le_rfl
  exact le_antisymm (hLe h) (hLe (by
    filter_upwards [h] with w hw
    exact fun t => (hw t).symm))

variable [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]

def LocalMartingaleQuadraticVariation.zeroProcess :
    LocalMartingaleQuadraticVariation (0 : Process Ω) F mu where
  variation := 0
  stronglyAdapted := (martingale_zero Real F mu).stronglyAdapted
  rightContinuous := fun _ _ => continuousWithinAt_const
  leftLimits := by
    intro w t
    apply tendsto_leftLim_of_tendsto
    exact ⟨0, tendsto_const_nhds⟩
  locallyBoundedVariation := by
    intro w a b _ _
    unfold BoundedVariationOn
    rw [eVariationOn.constant_on (by
      rintro _ ⟨_, _, rfl⟩ _ ⟨_, _, rfl⟩
      rfl)]
    exact ENNReal.zero_ne_top
  monotone := fun _ => monotone_const
  zero := rfl
  jump_sq := Eventually.of_forall (fun _ t => by
    have h : Function.leftLim (fun _ : NNReal => (0 : Real)) t = 0 := by
      by_cases ht : t = 0
      · subst t
        exact leftLim_eq_of_isBot isBot_bot
      · let : NeBot (𝓝[<] t) := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
        exact leftLim_eq_of_tendsto tendsto_const_nhds
    simp [processLeftJump, h])
  squareResidual := by
    have h : LocalMartingale (0 : Process Ω) F mu :=
      Locally.of_prop (martingale_zero Real F mu)
    convert h using 1
    ext
    simp

omit [SigmaFiniteFiltration mu F] in
theorem semimartingaleJ1_le_expected_variation
    (hA : StronglyAdapted F X)
    (hRight : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X)
    (hBV : ∀ w, LocallyBoundedVariationOn (X · w) univ) (hZero : X 0 = 0) :
    semimartingaleJ1 X F mu ≤ ∫⁻ w, eVariationOn (X · w) univ ∂mu := by
  let Q : LocalMartingaleQuadraticVariation (0 : Process Ω) F mu :=
    LocalMartingaleQuadraticVariation.zeroProcess
  let D : J1Decomposition X F mu := {
    N := 0
    A := X
    decomposition := Eventually.of_forall (fun _ _ => by simp)
    localMartingale := Locally.of_prop (martingale_zero Real F mu)
    adaptedN := Q.stronglyAdapted
    rightN := Q.rightContinuous
    leftN := Q.leftLimits
    zeroN := rfl
    adaptedA := hA
    rightA := hRight
    leftA := hLeft
    variationA := hBV
    zeroA := hZero }
  apply (iInf_le _ D).trans
  apply (iInf_le _ Q).trans
  simp [Q, LocalMartingaleQuadraticVariation.zeroProcess, D]

omit [MeasurableSpace Ω] in
theorem boundaryJumpProcess_eVariationOn_univ_le
    (tau : Ω → NNReal) {T : NNReal} (hTauT : ∀ w, tau w ≤ T) (w : Ω) :
    eVariationOn (boundaryJumpProcess X tau · w) univ ≤
      ENNReal.ofReal |processLeftJump X (tau w) w| := by
  let B := boundaryJumpProcess X tau
  have hPath : (B · w) = (B · w) ∘ (fun t => min t T) := by
    funext t
    by_cases ht : t ≤ T
    · simp only [Function.comp_apply, min_eq_left ht]
    · change B t w = B (min t T) w
      rw [min_eq_right (le_of_not_ge ht)]
      exact boundaryJumpProcess_constant_after hTauT w t (le_of_not_ge ht)
  calc
    eVariationOn (B · w) univ =
        eVariationOn ((B · w) ∘ (fun t => min t T)) univ := congrArg (eVariationOn · univ) hPath
    _ ≤ eVariationOn (B · w) (Icc 0 T) :=
      eVariationOn.comp_le_of_monotoneOn _ _
        ((FiniteVariationStoppedPath.monotone_clamp T).monotoneOn univ)
        (fun _ _ => ⟨bot_le, min_le_right _ _⟩)
    _ ≤ ENNReal.ofReal |processLeftJump X (tau w) w| := by
      simpa only [B, boundaryJumpProcess_at_horizon_eq_processLeftJump hTauT w] using
        boundaryJumpProcess_eVariationOn_Icc_le (N := X) hTauT w

omit [SigmaFiniteFiltration mu F] in
theorem semimartingaleJ1_boundaryJump_le
    {tau : Ω → NNReal} {T : NNReal}
    (hX : StronglyAdapted F X)
    (hRight : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X)
    (hTau : IsStoppingTime F (fun w => (tau w : WithTop NNReal)))
    (hTauT : ∀ w, tau w ≤ T) :
    semimartingaleJ1 (boundaryJumpProcess X tau) F mu ≤
      ∫⁻ w, ENNReal.ofReal |processLeftJump X (tau w) w| ∂mu := by
  apply (semimartingaleJ1_le_expected_variation
    (boundaryJumpProcess_stronglyAdapted hX hRight hLeft hTau)
    (boundaryJumpProcess_rightContinuous X tau) (boundaryJumpProcess_hasLeftLimits X tau)
    (fun w => (boundaryJumpProcess_boundedVariation X tau w).locallyBoundedVariationOn)
    boundaryJumpProcess_zero).trans
  exact lintegral_mono (boundaryJumpProcess_eVariationOn_univ_le tau hTauT)

theorem semimartingaleJ1_stopped_le_strictPrefix_add_jump
    (hUsual : Filtration.UsualConditions mu F) {tau : Ω → NNReal} {T : NNReal}
    (hX : StronglyAdapted F X)
    (hRight : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hLeft : ProcessHasLeftLimits X)
    (hTau : IsStoppingTime F (fun w => (tau w : WithTop NNReal)))
    (hTauT : ∀ w, tau w ≤ T) :
    semimartingaleJ1 (stoppedProcess X (fun w => (tau w : WithTop NNReal))) F mu ≤
      semimartingaleJ1 (strictPrefixProcess X tau) F mu +
        ∫⁻ w, ENNReal.ofReal |processLeftJump X (tau w) w| ∂mu := by
  rw [semimartingaleJ1_congr (X := stoppedProcess X (fun w => (tau w : WithTop NNReal)))
    (Y := strictPrefixProcess X tau + boundaryJumpProcess X tau)
    (Eventually.of_forall (fun w t =>
      (strictPrefixProcess_add_postStopSampled_processLeftJump X tau t w).symm))]
  exact (semimartingaleJ1_add_le hUsual).trans
    (add_le_add_right (semimartingaleJ1_boundaryJump_le hX hRight hLeft hTau hTauT) _)

end FTAPTheorem42
