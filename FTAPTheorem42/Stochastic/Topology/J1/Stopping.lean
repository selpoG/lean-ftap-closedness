/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.J1.Basic

/-! # Closed stopping contracts the zero-initial j1 gauge -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

open RightContinuousStoppedMartingale

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  {X : Process Ω} {tau : Ω → WithTop NNReal}

omit [MeasurableSpace Ω] in
private theorem monotone_boundedTime (w : Ω) : Monotone (fun t => boundedTime t tau w) := by
  intro s t hst
  apply WithTop.coe_le_coe.mp
  rw [coe_boundedTime, coe_boundedTime]
  exact min_le_min_right _ (WithTop.coe_le_coe.mpr hst)

noncomputable def J1Decomposition.stopped (D : J1Decomposition X F mu)
    (hTau : IsStoppingTime F tau) : J1Decomposition (stoppedProcess X tau) F mu where
  N := stoppedProcess D.N tau
  A := stoppedProcess D.A tau
  decomposition := by
    filter_upwards [D.decomposition] with w hw
    exact fun t => hw (boundedTime t tau w)
  localMartingale := D.localMartingale.stoppedProcess_of_zero_of_rightContinuous
    D.zeroN D.rightN hTau
  adaptedN := StronglyAdapted.stoppedProcess_of_rightContinuous D.adaptedN hTau D.rightN
  rightN := stoppedProcess_rightContinuous D.N D.rightN
  leftN := D.leftN.stoppedProcess tau
  zeroN := by
    funext w
    rw [stoppedProcess_eq_of_le (show ((0 : NNReal) : WithTop NNReal) ≤ tau w from bot_le)]
    exact congrFun D.zeroN w
  adaptedA := StronglyAdapted.stoppedProcess_of_rightContinuous D.adaptedA hTau D.rightA
  rightA := stoppedProcess_rightContinuous D.A D.rightA
  leftA := D.leftA.stoppedProcess tau
  variationA := by
    intro w a b ha hb
    change eVariationOn ((D.A · w) ∘ (fun t => boundedTime t tau w)) (univ ∩ Icc a b) ≠ ∞
    exact ne_top_of_le_ne_top (D.variationA w 0 b (mem_univ _) (mem_univ _))
      (eVariationOn.comp_le_of_monotoneOn _ _
        ((monotone_boundedTime w).monotoneOn _) (fun t ht =>
          ⟨mem_univ _, bot_le, (boundedTime_le t tau w).trans ht.2.2⟩))
  zeroA := by
    funext w
    rw [stoppedProcess_eq_of_le (show ((0 : NNReal) : WithTop NNReal) ≤ tau w from bot_le)]
    exact congrFun D.zeroA w

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## The outer strict-prefix extension infimum for the zero-initial j1 core -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  {X : Process Ω} {tau : Ω → WithTop NNReal}

/-- The outer infimum quantifies every global extension agreeing before `tau`
on a single full-measure set. It does not assert that the strict prefix is an integral. -/
noncomputable def prelocalSemimartingaleJ1 (X : Process Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω)) (mu : Measure Ω)
    (tau : Ω → WithTop NNReal) : ENNReal :=
  ⨅ Y : Process Ω, ⨅ (_ : ∀ᵐ w ∂mu, ∀ t : NNReal,
    (t : WithTop NNReal) < tau w → Y t w = X t w),
    semimartingaleJ1 Y F mu

variable [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]

theorem lintegral_strictPrefix_maximal_le_six_prelocalSemimartingaleJ1
    (hUsual : Filtration.UsualConditions mu F) :
    (∫⁻ w, ⨆ t : {t : NNReal // (t : WithTop NNReal) < tau w}, ENNReal.ofReal |X t.1 w| ∂mu) ≤
      6 * prelocalSemimartingaleJ1 X F mu tau := by
  unfold prelocalSemimartingaleJ1
  rw [ENNReal.mul_iInf_of_ne (by norm_num : (6 : ENNReal) ≠ 0)
    (by norm_num : (6 : ENNReal) ≠ ∞)]
  apply le_iInf
  intro Y
  rw [ENNReal.mul_iInf_of_ne (by norm_num : (6 : ENNReal) ≠ 0)
    (by norm_num : (6 : ENNReal) ≠ ∞)]
  apply le_iInf
  intro hY
  apply le_trans _ (lintegral_maximal_le_six_semimartingaleJ1 (X := Y) hUsual)
  apply lintegral_mono_ae
  filter_upwards [hY] with w hw
  apply iSup_le
  intro t
  rw [← hw t.1 t.2]
  exact le_iSup (fun s : NNReal => ENNReal.ofReal |Y s w|) t.1

end FTAPTheorem42
