/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Topology.R1.Triangle

/-! # Scalar multiplication of the joint r1 cost -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  {X : Process Ω}

def LocalMartingaleQuadraticVariation.smul
    (Q : LocalMartingaleQuadraticVariation X F mu)
    (hLeft : ProcessHasLeftLimits X) (c : Real) :
    LocalMartingaleQuadraticVariation (c • X) F mu where
  variation := fun t w => c ^ 2 * Q.variation t w
  stronglyAdapted := fun t => (Q.stronglyAdapted t).const_mul _
  rightContinuous := fun w t => (Q.rightContinuous w t).const_mul _
  leftLimits := Q.leftLimits.const_mul _
  locallyBoundedVariation := fun w a b ha hb =>
    boundedVariationOn_const_mul _ (Q.locallyBoundedVariation w a b ha hb)
  monotone := fun w a b hab => mul_le_mul_of_nonneg_left (Q.monotone w hab) (sq_nonneg c)
  zero := by simp only [Q.zero, Pi.zero_apply, mul_zero]; rfl
  jump_sq := by
    filter_upwards [Q.jump_sq] with w hw
    intro t
    rw [processLeftJump_const_mul Q.leftLimits, hw t]
    change c ^ 2 * processLeftJump X t w ^ 2 =
      processLeftJump (fun t w => c * X t w) t w ^ 2
    rw [processLeftJump_const_mul hLeft, mul_pow]
  squareResidual := by
    convert LocalMartingale.smul (c ^ 2) Q.squareResidual using 1
    funext t w
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

def J1Decomposition.smul (D : J1Decomposition X F mu) (c : Real) :
    J1Decomposition (c • X) F mu where
  N := c • D.N
  A := c • D.A
  decomposition := by
    filter_upwards [D.decomposition] with w hw
    intro t
    change c * X t w = c * D.N t w + c * D.A t w
    rw [hw t, mul_add]
  localMartingale := LocalMartingale.smul c D.localMartingale
  adaptedN := fun t => (D.adaptedN t).const_mul c
  rightN := fun w t => (D.rightN w t).const_mul c
  leftN := D.leftN.const_mul c
  zeroN := by simp only [Pi.smul_apply, D.zeroN, smul_zero]
  adaptedA := fun t => (D.adaptedA t).const_mul c
  rightA := fun w t => (D.rightA w t).const_mul c
  leftA := D.leftA.const_mul c
  variationA := fun w a b ha hb => boundedVariationOn_const_mul c (D.variationA w a b ha hb)
  zeroA := by simp only [Pi.smul_apply, D.zeroA, smul_zero]

theorem eVariationOn_const_mul_le {I : Type*} [LinearOrder I]
    (c : Real) (f : I → Real) (s : Set I) :
    eVariationOn (fun t => c * f t) s ≤ ENNReal.ofReal |c| * eVariationOn f s := by
  have hn : (‖c‖₊ : ENNReal) = ENNReal.ofReal |c| := by
    rw [← enorm_eq_nnnorm, ← ofReal_norm, Real.norm_eq_abs]
  simpa only [Function.comp_def, smul_eq_mul, hn] using
    (lipschitzWith_smul c (β := Real)).lipschitzOnWith.comp_eVariationOn_le
      (mapsTo_univ f s)

theorem J1Decomposition.smul_clock_le (D : J1Decomposition X F mu)
    (Q : LocalMartingaleQuadraticVariation D.N F mu) (c : Real) (t : NNReal) (w : Ω) :
    (D.smul c).clock (Q.smul D.leftN c) t w ≤ ENNReal.ofReal |c| * D.clock Q t w := by
  have hRoot : Real.sqrt (c ^ 2 * Q.variation t w) = |c| * Real.sqrt (Q.variation t w) := by
    rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  simp only [clock, smul, LocalMartingaleQuadraticVariation.smul, hRoot,
    ENNReal.ofReal_mul (abs_nonneg c), mul_add]
  exact add_le_add_right (eVariationOn_const_mul_le c (D.A · w) (Icc 0 t)) _

theorem boundedStoppingJumpCost_smul (hLeft : ProcessHasLeftLimits X) (c : Real) :
    boundedStoppingJumpCost (c • X) F mu =
      ENNReal.ofReal |c| * boundedStoppingJumpCost X F mu := by
  have hj : ∀ t w, ENNReal.ofReal |processLeftJump (c • X) t w| =
      ENNReal.ofReal |c| * ENNReal.ofReal |processLeftJump X t w| := by
    intro t w
    change ENNReal.ofReal |processLeftJump (fun t w => c * X t w) t w| = _
    rw [processLeftJump_const_mul hLeft, abs_mul, ENNReal.ofReal_mul (abs_nonneg c)]
  simp only [boundedStoppingJumpCost, hj,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← ENNReal.mul_iSup]

theorem J1Decomposition.smul_r1Cost_le (D : J1Decomposition X F mu)
    (Q : LocalMartingaleQuadraticVariation D.N F mu) (c : Real) :
    (D.smul c).r1Cost (Q.smul D.leftN c) ≤
      ENNReal.ofReal (max 1 |c|) * D.r1Cost Q := by
  let b : ENNReal := ENNReal.ofReal (max 1 |c|)
  have hb : 1 ≤ b := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (le_max_left 1 |c|)
  have hc : ENNReal.ofReal |c| ≤ b := ENNReal.ofReal_le_ofReal (le_max_right 1 |c|)
  have hCap : ∀ t w, min ((D.smul c).clock (Q.smul D.leftN c) t w) 1 ≤
      b * min (D.clock Q t w) 1 := by
    intro t w
    rw [mul_min, mul_one]
    exact le_min
      ((min_le_left _ _).trans ((D.smul_clock_le Q c t w).trans
        (mul_le_mul hc le_rfl bot_le bot_le)))
      ((min_le_right _ _).trans hb)
  change _ ≤ b * D.r1Cost Q
  simp only [r1Cost, mul_add]
  rw [← ENNReal.tsum_mul_left]
  apply add_le_add
  · exact (boundedStoppingJumpCost_smul D.leftN c).le.trans
      (mul_le_mul hc le_rfl bot_le bot_le)
  · apply ENNReal.tsum_le_tsum
    intro n
    calc
      _ ≤ (2 : ENNReal)⁻¹ ^ (n + 1) *
          ∫⁻ w, b * min (D.clock Q (n : NNReal) w) 1 ∂mu :=
        mul_le_mul le_rfl (lintegral_mono (hCap _)) bot_le bot_le
      _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]; ring

theorem semimartingaleR1_smul_le (c : Real) :
    semimartingaleR1 (c • X) F mu ≤
      ENNReal.ofReal (max 1 |c|) * semimartingaleR1 X F mu := by
  have hb : ENNReal.ofReal (max 1 |c|) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).ne'
  simp only [semimartingaleR1]
  rw [ENNReal.mul_iInf_of_ne hb ENNReal.ofReal_ne_top]
  apply le_iInf
  intro D
  rw [ENNReal.mul_iInf_of_ne hb ENNReal.ofReal_ne_top]
  apply le_iInf
  intro Q
  exact (iInf_le_of_le (D.smul c) (iInf_le _ (Q.smul D.leftN c))).trans
    (D.smul_r1Cost_le Q c)

end FTAPTheorem42
