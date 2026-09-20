/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.J1.Stopping
import FTAPTheorem42.Stochastic.Martingale.Quadratic.LocalMartingaleQuadraticRootTriangle

/-! # Triangle inequalities for the j1 and strict-prefix extension gauges -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  {X Y : Process Ω}

theorem J1Decomposition.measurable_variation (D : J1Decomposition X F mu) :
    Measurable (fun w => eVariationOn (D.A · w) univ) := by
  have hEq : (fun w => eVariationOn (D.A · w) univ) =
      (fun w => ⨆ n : Nat, eVariationOn (D.A · w) (Icc 0 (n : NNReal))) := by
    funext w
    apply le_antisymm
    · rw [eVariationOn.eq_biSup_inter_Icc]
      apply iSup_le
      intro p
      apply iSup_le
      intro hp
      exact le_iSup_of_le (Nat.ceil p.2) (eVariationOn.mono _ (fun t ht =>
        ⟨bot_le, ht.2.2.trans (Nat.le_ceil p.2)⟩))
    · exact iSup_le (fun n => eVariationOn.mono _ (subset_univ _))
  rw [hEq]
  exact Measurable.iSup (fun _ =>
    SIntegrableFiniteVariationBridge.measurable_eVariationOn_Icc_of_stronglyAdapted_rightContinuous
      D.adaptedA D.rightA)

variable [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]

noncomputable def J1Decomposition.add (D : J1Decomposition X F mu)
    (E : J1Decomposition Y F mu) : J1Decomposition (X + Y) F mu where
  N := D.N + E.N
  A := D.A + E.A
  decomposition := by
    filter_upwards [D.decomposition, E.decomposition] with w hw hv
    intro t
    change X t w + Y t w = (D.N t w + E.N t w) + (D.A t w + E.A t w)
    rw [hw t, hv t]
    ring
  localMartingale := D.localMartingale.add_of_rightContinuous E.localMartingale D.rightN E.rightN
  adaptedN := D.adaptedN.add E.adaptedN
  rightN := fun w t => (D.rightN w t).add (E.rightN w t)
  leftN := D.leftN.add E.leftN
  zeroN := by simp only [Pi.add_apply, D.zeroN, E.zeroN, add_zero]
  adaptedA := D.adaptedA.add E.adaptedA
  rightA := fun w t => (D.rightA w t).add (E.rightA w t)
  leftA := D.leftA.add E.leftA
  variationA := fun w a b ha hb =>
    boundedVariationOn_add (D.variationA w a b ha hb) (E.variationA w a b ha hb)
  zeroA := by simp only [Pi.add_apply, D.zeroA, E.zeroA, add_zero]

theorem J1Decomposition.add_cost_le (D : J1Decomposition X F mu)
    (E : J1Decomposition Y F mu) (hUsual : Filtration.UsualConditions mu F) :
    (D.add E).cost ≤ D.cost + E.cost := by
  obtain ⟨QD, QE, QS, hTriangle⟩ := exists_quadraticVariations_root_triangle hUsual
    D.localMartingale E.localMartingale D.adaptedN E.adaptedN D.rightN E.rightN
    D.leftN E.leftN D.zeroN E.zeroN
  rw [(D.add E).cost_eq hUsual QS, D.cost_eq hUsual QD, E.cost_eq hUsual QE]
  have hRoot : (∫⁻ w, ⨆ t : NNReal, ENNReal.ofReal (Real.sqrt (QS.variation t w)) ∂mu) ≤
      (∫⁻ w, ⨆ t : NNReal, ENNReal.ofReal (Real.sqrt (QD.variation t w)) ∂mu) +
      ∫⁻ w, ⨆ t : NNReal, ENNReal.ofReal (Real.sqrt (QE.variation t w)) ∂mu := by
    rw [← lintegral_add_left QD.measurable_allTimeRoot]
    apply lintegral_mono_ae
    filter_upwards [hTriangle] with w hw
    apply iSup_le
    intro t
    exact (ENNReal.ofReal_le_ofReal (hw t)).trans
      ((le_of_eq (ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).trans
        (add_le_add
          (le_iSup (fun s : NNReal => ENNReal.ofReal (Real.sqrt (QD.variation s w))) t)
          (le_iSup (fun s : NNReal => ENNReal.ofReal (Real.sqrt (QE.variation s w))) t)))
  have hVar : (∫⁻ w, eVariationOn ((D.add E).A · w) univ ∂mu) ≤
      (∫⁻ w, eVariationOn (D.A · w) univ ∂mu) + ∫⁻ w, eVariationOn (E.A · w) univ ∂mu := by
    rw [← lintegral_add_left D.measurable_variation]
    exact lintegral_mono (fun w => eVariationOn_add_le_real (D.A · w) (E.A · w) univ)
  exact (add_le_add hRoot hVar).trans_eq (by ac_rfl)

theorem semimartingaleJ1_add_le (hUsual : Filtration.UsualConditions mu F) :
    semimartingaleJ1 (X + Y) F mu ≤ semimartingaleJ1 X F mu + semimartingaleJ1 Y F mu := by
  apply ENNReal.le_iInf_add_iInf
  intro D E
  exact (iInf_le _ (D.add E)).trans (D.add_cost_le E hUsual)

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## Symmetry and difference estimates for the j1 gauges -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  {X Y : Process Ω}

def LocalMartingaleQuadraticVariation.neg (Q : LocalMartingaleQuadraticVariation X F mu)
    (hLeft : ProcessHasLeftLimits X) : LocalMartingaleQuadraticVariation (-X) F mu where
  variation := Q.variation
  stronglyAdapted := Q.stronglyAdapted
  rightContinuous := Q.rightContinuous
  leftLimits := Q.leftLimits
  locallyBoundedVariation := Q.locallyBoundedVariation
  monotone := Q.monotone
  zero := Q.zero
  jump_sq := by
    filter_upwards [Q.jump_sq] with w hw
    intro t
    have hj := processLeftJump_const_mul hLeft (-1) t w
    have hProcess : (fun s w => (-1 : Real) * X s w) = -X := by
      funext s w
      exact neg_one_mul (X s w)
    rw [hProcess, neg_one_mul] at hj
    rw [hj, neg_sq]
    exact hw t
  squareResidual := by
    simpa only [Pi.neg_apply, neg_sq] using Q.squareResidual

def J1Decomposition.neg (D : J1Decomposition X F mu) : J1Decomposition (-X) F mu where
  N := -D.N
  A := -D.A
  decomposition := by
    filter_upwards [D.decomposition] with w hw
    intro t
    change -X t w = -D.N t w + -D.A t w
    rw [hw t, neg_add]
  localMartingale := D.localMartingale.neg
  adaptedN := D.adaptedN.neg
  rightN := fun w t => (D.rightN w t).neg
  leftN := D.leftN.neg
  zeroN := by simp only [Pi.neg_apply, D.zeroN, neg_zero]
  adaptedA := D.adaptedA.neg
  rightA := fun w t => (D.rightA w t).neg
  leftA := D.leftA.neg
  variationA := fun w a b ha hb => boundedVariationOn_neg (D.variationA w a b ha hb)
  zeroA := by simp only [Pi.neg_apply, D.zeroA, neg_zero]

variable [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]

end FTAPTheorem42
