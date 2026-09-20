/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.R1.Basic

/-! # The triangle inequality for the joint r1 infimum -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  {X Y : Process Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]

theorem J1Decomposition.add_jumpCost_le (D : J1Decomposition X F mu)
    (E : J1Decomposition Y F mu) :
    boundedStoppingJumpCost (D.add E).N F mu ≤
      boundedStoppingJumpCost D.N F mu + boundedStoppingJumpCost E.N F mu := by
  apply iSup_le
  intro T
  apply iSup_le
  intro tau
  apply iSup_le
  intro hTau
  apply iSup_le
  intro hTauT
  apply le_trans _ (add_le_add
    (lintegral_jump_le_boundedStoppingJumpCost hTau hTauT)
    (lintegral_jump_le_boundedStoppingJumpCost hTau hTauT))
  rw [← lintegral_add_left (D.measurable_sampledJump hTau hTauT)]
  apply lintegral_mono
  intro w
  change ENNReal.ofReal |processLeftJump (fun t w => D.N t w + E.N t w) (tau w) w| ≤ _
  rw [processLeftJump_add D.leftN E.leftN]
  exact (ENNReal.ofReal_le_ofReal (abs_add_le _ _)).trans_eq
    (ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _))

theorem J1Decomposition.add_clock_le (D : J1Decomposition X F mu)
    (E : J1Decomposition Y F mu) (hUsual : Filtration.UsualConditions mu F)
    (QD : LocalMartingaleQuadraticVariation D.N F mu)
    (QE : LocalMartingaleQuadraticVariation E.N F mu)
    (QS : LocalMartingaleQuadraticVariation (D.add E).N F mu) :
    ∀ᵐ w ∂mu, ∀ t, (D.add E).clock QS t w ≤ D.clock QD t w + E.clock QE t w := by
  have hRoot := QD.root_triangle hUsual D.localMartingale E.localMartingale
    D.adaptedN E.adaptedN D.rightN E.rightN D.leftN E.leftN D.zeroN E.zeroN QE QS
  filter_upwards [hRoot] with w hw
  intro t
  have hRoot' := (ENNReal.ofReal_le_ofReal (hw t)).trans_eq
    (ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hVar := eVariationOn_add_le_real (D.A · w) (E.A · w) (Icc 0 t)
  exact (add_le_add hRoot' hVar).trans_eq (by
    change (_ + _) + (_ + _) = (_ + _) + (_ + _)
    ac_rfl)

theorem min_add_one_le (a b : ENNReal) : min (a + b) 1 ≤ min a 1 + min b 1 := by
  by_cases ha : a ≤ 1
  · rw [min_eq_left ha]
    by_cases hb : b ≤ 1
    · rw [min_eq_left hb]
      exact min_le_left _ _
    · rw [min_eq_right (le_of_not_ge hb)]
      exact (min_le_right _ _).trans (le_add_left le_rfl)
  · rw [min_eq_right (le_of_not_ge ha)]
    exact (min_le_right _ _).trans (le_add_right le_rfl)

theorem J1Decomposition.add_r1Cost_le (D : J1Decomposition X F mu)
    (E : J1Decomposition Y F mu) (hUsual : Filtration.UsualConditions mu F)
    (QD : LocalMartingaleQuadraticVariation D.N F mu)
    (QE : LocalMartingaleQuadraticVariation E.N F mu)
    (QS : LocalMartingaleQuadraticVariation (D.add E).N F mu) :
    (D.add E).r1Cost QS ≤ D.r1Cost QD + E.r1Cost QE := by
  have hClock := D.add_clock_le E hUsual QD QE QS
  have hInt (n : Nat) : (∫⁻ w, min ((D.add E).clock QS (n : NNReal) w) 1 ∂mu) ≤
      (∫⁻ w, min (D.clock QD (n : NNReal) w) 1 ∂mu) +
        ∫⁻ w, min (E.clock QE (n : NNReal) w) 1 ∂mu := by
    rw [← lintegral_add_left ((D.clock_measurable QD _).min measurable_const)]
    apply lintegral_mono_ae
    filter_upwards [hClock] with w hw
    exact (min_le_min (hw _) le_rfl).trans (min_add_one_le _ _)
  have hSeries := ENNReal.tsum_le_tsum (fun n =>
    mul_le_mul (le_rfl : (2 : ENNReal)⁻¹ ^ (n + 1) ≤ _) (hInt n) bot_le bot_le)
  simp_rw [mul_add] at hSeries
  rw [ENNReal.tsum_add] at hSeries
  exact (add_le_add (D.add_jumpCost_le E) hSeries).trans_eq (by
    unfold J1Decomposition.r1Cost
    ac_rfl)

theorem semimartingaleR1_add_le (hUsual : Filtration.UsualConditions mu F) :
    semimartingaleR1 (X + Y) F mu ≤ semimartingaleR1 X F mu + semimartingaleR1 Y F mu := by
  apply ENNReal.le_iInf₂_add_iInf₂
  intro D QD E QE
  obtain ⟨QS, _⟩ := exists_unique_localMartingaleQuadraticVariation
    (D.add E).localMartingale (D.add E).adaptedN (D.add E).rightN
    (D.add E).leftN (D.add E).zeroN hUsual
  have hInf : semimartingaleR1 (X + Y) F mu ≤ (D.add E).r1Cost QS :=
    iInf_le_of_le (D.add E) (iInf_le _ QS)
  exact hInf.trans (D.add_r1Cost_le E hUsual QD QE QS)

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## Symmetry and successive differences for the joint r1 cost -/

open Filter MeasureTheory Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  {X Y : Process Ω}

theorem J1Decomposition.neg_r1Cost (D : J1Decomposition X F mu)
    (Q : LocalMartingaleQuadraticVariation D.N F mu) :
    D.neg.r1Cost (Q.neg D.leftN) = D.r1Cost Q := by
  have hJump : ∀ t w, |processLeftJump D.neg.N t w| = |processLeftJump D.N t w| := by
    intro t w
    have hj := processLeftJump_const_mul D.leftN (-1) t w
    have hEq : (fun s w => (-1 : Real) * D.N s w) = D.neg.N := by
      funext s w
      exact neg_one_mul _
    rw [hEq, neg_one_mul] at hj
    rw [hj, abs_neg]
  have hClock : ∀ t w, D.neg.clock (Q.neg D.leftN) t w = D.clock Q t w := by
    intro t w
    simp only [J1Decomposition.clock, J1Decomposition.neg, LocalMartingaleQuadraticVariation.neg,
      eVariationOn, Pi.neg_apply, edist_neg_neg]
  simp only [J1Decomposition.r1Cost, boundedStoppingJumpCost, hJump, hClock]

theorem semimartingaleR1_neg : semimartingaleR1 (-X) F mu = semimartingaleR1 X F mu := by
  have hLe : ∀ Z : Process Ω, semimartingaleR1 (-Z) F mu ≤ semimartingaleR1 Z F mu := by
    intro Z
    apply le_iInf
    intro D
    apply le_iInf
    intro Q
    exact (iInf_le_of_le D.neg (iInf_le _ (Q.neg D.leftN))).trans_eq (D.neg_r1Cost Q)
  exact le_antisymm (hLe X) (by simpa only [neg_neg] using hLe (-X))

variable [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]

theorem semimartingaleR1_sub_le (hUsual : Filtration.UsualConditions mu F) :
    semimartingaleR1 (X - Y) F mu ≤ semimartingaleR1 X F mu + semimartingaleR1 Y F mu := by
  simpa only [sub_eq_add_neg, semimartingaleR1_neg] using
    semimartingaleR1_add_le (X := X) (Y := -Y) hUsual

end FTAPTheorem42
