/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.J1.StrictPrefix
import FTAPTheorem42.Stochastic.Martingale.Quadratic.LocalMartingaleQuadraticBoundaryRoot

/-! # Strict-prefix variation bounded by the pre-stop cumulative variation -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace FTAPTheorem42

open SIntegrableFiniteVariationBridge

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  {X : Process Ω}

theorem J1Decomposition.strictPrefix_variation_le_leftVariation
    (D : J1Decomposition X F mu) (tau : Ω → NNReal) {T : NNReal}
    (hTauT : ∀ w, tau w ≤ T) (w : Ω) :
    eVariationOn (strictPrefixProcess D.A tau · w) univ ≤
      ENNReal.ofReal (Function.leftLim (variationOnFromTo (D.A · w) univ 0) (tau w)) := by
  let A := deterministicallyStoppedProcess D.A T
  have hAV : BoundedVariationOn (A · w) univ :=
    FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn
      (D.variationA w) T
  have hAL : ProcessHasLeftLimits A := D.leftA.stoppedProcess _
  have hEq : ∀ t, strictPrefixProcess A tau t w = strictPrefixProcess D.A tau t w := by
    apply strictPrefixProcess_eq_of_agree_before hAL w
    · change D.A (min 0 T) w = D.A 0 w
      rw [min_eq_left (show (0 : NNReal) ≤ T from bot_le)]
    · intro t ht
      change D.A (min t T) w = D.A t w
      rw [min_eq_left (ht.le.trans (hTauT w))]
  rw [← funext hEq]
  apply strictPrefixProcess_variation_le_of_before A tau w hAV
  intro t ht
  have hVar : variationOnFromTo (A · w) univ 0 t =
      variationOnFromTo (D.A · w) univ 0 t := by
    rw [variationOnFromTo.eq_of_le _ _ (show (0 : NNReal) ≤ t from bot_le),
      variationOnFromTo.eq_of_le _ _ (show (0 : NNReal) ≤ t from bot_le), univ_inter]
    congr 1
    apply eVariationOn.congr
    intro s hs
    change D.A (min s T) w = D.A s w
    rw [min_eq_left (hs.2.trans (ht.le.trans (hTauT w)))]
  rw [hVar]
  have hMono : Monotone (variationOnFromTo (D.A · w) univ 0) := by
    rw [← monotoneOn_univ]
    exact variationOnFromTo.monotoneOn (D.variationA w) (mem_univ 0)
  exact hMono.le_leftLim ht

theorem J1Decomposition.lintegral_strictPrefix_variation_le_leftVariation
    (D : J1Decomposition X F mu) (tau : Ω → NNReal) {T : NNReal}
    (hTauT : ∀ w, tau w ≤ T) :
    (∫⁻ w, eVariationOn (strictPrefixProcess D.A tau · w) univ ∂mu) ≤
      ∫⁻ w, ENNReal.ofReal (Function.leftLim
        (variationOnFromTo (D.A · w) univ 0) (tau w)) ∂mu :=
  lintegral_mono (D.strictPrefix_variation_le_leftVariation tau hTauT)

theorem J1Decomposition.prelocal_cost_le_left_components_add_jump
    [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
    (D : J1Decomposition X F mu) (Q : LocalMartingaleQuadraticVariation D.N F mu)
    (hUsual : Filtration.UsualConditions mu F) {tau : Ω → NNReal} {T : NNReal}
    (hTau : IsStoppingTime F (fun w => (tau w : WithTop NNReal)))
    (hTauT : ∀ w, tau w ≤ T) :
    prelocalSemimartingaleJ1 X F mu (fun w => (tau w : WithTop NNReal)) ≤
      (∫⁻ w, ENNReal.ofReal (Real.sqrt (Function.leftLim (Q.variation · w) (tau w))) +
        ENNReal.ofReal |processLeftJump D.N (tau w) w| ∂mu) +
      ∫⁻ w, ENNReal.ofReal (Function.leftLim
        (variationOnFromTo (D.A · w) univ 0) (tau w)) ∂mu := by
  let M := stoppedProcess D.N (fun w => (tau w : WithTop NNReal))
  let A := strictPrefixProcess D.A tau
  let Y : Process Ω := fun t w => M t w + A t w
  let E : J1Decomposition Y F mu := { D.stopped hTau with
    A := A
    decomposition := Eventually.of_forall (fun _ _ => rfl)
    adaptedA := strictPrefixProcess_stronglyAdapted D.A tau D.adaptedA D.rightA D.leftA hTau
    rightA := strictPrefixProcess_rightContinuous D.A tau D.rightA
    leftA := strictPrefixProcess_hasLeftLimits D.A tau D.leftA
    variationA := fun w => (show BoundedVariationOn (A · w) univ from
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (D.strictPrefix_variation_le_leftVariation tau hTauT w)).locallyBoundedVariationOn
    zeroA := by
      change strictPrefixProcess D.A tau 0 = 0
      rw [strictPrefixProcess_zero, D.zeroA] }
  have hPrefix : ∀ᵐ w ∂mu, ∀ t : NNReal, (t : WithTop NNReal) <
      (tau w : WithTop NNReal) → Y t w = X t w := by
    filter_upwards [D.decomposition] with w hw
    intro t ht
    dsimp only [Y, M, A]
    rw [stoppedProcess_eq_of_le (u := D.N)
      (τ := fun w => (tau w : WithTop NNReal)) ht.le,
      strictPrefixProcess_eq_of_lt D.A tau (WithTop.coe_lt_coe.mp ht)]
    exact (hw t).symm
  have hCost : prelocalSemimartingaleJ1 X F mu (fun w => (tau w : WithTop NNReal)) ≤ E.cost := by
    apply iInf_le_of_le Y
    apply iInf_le_of_le hPrefix
    exact iInf_le _ E
  apply hCost.trans
  rw [E.cost_eq hUsual (Q.stopped D.rightN D.leftN D.zeroN hTau)]
  exact add_le_add
    (Q.lintegral_stopped_root_le_leftRoot_add_jump D.rightN D.leftN D.zeroN hTau)
    (D.lintegral_strictPrefix_variation_le_leftVariation tau hTauT)

end FTAPTheorem42
