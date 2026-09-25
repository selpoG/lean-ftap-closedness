/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.DoleansDadeYen.Quadratic
import FTAPTheorem42.Stochastic.Integral.Calculus.LocallySIntegrableStrategyAlgebra
import Mathlib.Algebra.QuadraticDiscriminant

/-! # Polarization of intrinsic quadratic variations -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  [F.IsRightContinuous] {X Y : Process Ω}

theorem LocalMartingaleQuadraticVariation.polarization
    (hUsual : Filtration.UsualConditions mu F)
    (hXR : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hYR : ∀ w t, ContinuousWithinAt (Y · w) (Ici t) t)
    (hXL : ProcessHasLeftLimits X) (hYL : ProcessHasLeftLimits Y)
    (QX : LocalMartingaleQuadraticVariation X F mu)
    (QY : LocalMartingaleQuadraticVariation Y F mu)
    (QS : LocalMartingaleQuadraticVariation (fun t w => X t w + Y t w) F mu)
    (a : Real)
    (QR : LocalMartingaleQuadraticVariation (fun t w => X t w + a * Y t w) F mu) :
    ProcessIndistinguishable mu QR.variation (fun t w =>
      a * QS.variation t w + (1 - a) * QX.variation t w +
        (a ^ 2 - a) * QY.variation t w) := by
  let A : Process Ω := fun t w => a * QS.variation t w + (1 - a) * QX.variation t w +
    (a ^ 2 - a) * QY.variation t w
  have hAA : StronglyAdapted F A := fun t =>
    (((QS.stronglyAdapted t).const_mul a).add ((QX.stronglyAdapted t).const_mul (1 - a))).add
      ((QY.stronglyAdapted t).const_mul (a ^ 2 - a))
  have hAR : ∀ w t, ContinuousWithinAt (A · w) (Ici t) t := fun w t =>
    (((QS.rightContinuous w t).const_mul a).add
      ((QX.rightContinuous w t).const_mul (1 - a))).add
        ((QY.rightContinuous w t).const_mul (a ^ 2 - a))
  have hAL : ProcessHasLeftLimits A :=
    ((QS.leftLimits.const_mul a).add (QX.leftLimits.const_mul (1 - a))).add
      (QY.leftLimits.const_mul (a ^ 2 - a))
  let RX : Process Ω := fun t w => X t w ^ 2 - QX.variation t w
  let RY : Process Ω := fun t w => Y t w ^ 2 - QY.variation t w
  let RS : Process Ω := fun t w => (X t w + Y t w) ^ 2 - QS.variation t w
  have hRX : ∀ w t, ContinuousWithinAt (RX · w) (Ici t) t :=
    fun w t => ((hXR w t).pow 2).sub (QX.rightContinuous w t)
  have hRY : ∀ w t, ContinuousWithinAt (RY · w) (Ici t) t :=
    fun w t => ((hYR w t).pow 2).sub (QY.rightContinuous w t)
  have hRS : ∀ w t, ContinuousWithinAt (RS · w) (Ici t) t :=
    fun w t => (((hXR w t).add (hYR w t)).pow 2).sub (QS.rightContinuous w t)
  have hM₁ := (QS.squareResidual.smul a).add_of_rightContinuous
    (QX.squareResidual.smul (1 - a))
    (fun w t => (hRS w t).const_mul a) (fun w t => (hRX w t).const_mul (1 - a))
  have hM := hM₁.add_of_rightContinuous (QY.squareResidual.smul (a ^ 2 - a))
        (fun w t => ((hRS w t).const_mul a).add ((hRX w t).const_mul (1 - a)))
        (fun w t => (hRY w t).const_mul (a ^ 2 - a))
  have hRes : LocalMartingale (fun t w => (X t w + a * Y t w) ^ 2 - A t w) F mu := by
    convert hM using 1
    funext t w
    dsimp only [A]
    ring
  apply quadraticVariation_indistinguishable hUsual
    (fun w t => (hXR w t).add ((hYR w t).const_mul a))
    QR.stronglyAdapted hAA QR.rightContinuous hAR QR.leftLimits hAL
    QR.locallyBoundedVariation _ _ _ QR.squareResidual hRes
  · intro w s t hs ht
    exact boundedVariationOn_add
      (boundedVariationOn_add
        (boundedVariationOn_const_mul a (QS.locallyBoundedVariation w s t hs ht))
        (boundedVariationOn_const_mul (1 - a) (QX.locallyBoundedVariation w s t hs ht)))
      (boundedVariationOn_const_mul (a ^ 2 - a) (QY.locallyBoundedVariation w s t hs ht))
  · funext w
    simp only [A, QR.zero, QS.zero, QX.zero, QY.zero, Pi.zero_apply, mul_zero, add_zero]
  · filter_upwards [QR.jump_sq, QS.jump_sq, QX.jump_sq, QY.jump_sq] with w hR hS hX hY
    intro t
    change processLeftJump QR.variation t w = processLeftJump
      (fun s w => a * QS.variation s w + (1 - a) * QX.variation s w +
        (a ^ 2 - a) * QY.variation s w) t w
    rw [processLeftJump_add
      ((QS.leftLimits.const_mul a).add (QX.leftLimits.const_mul (1 - a)))
      (QY.leftLimits.const_mul (a ^ 2 - a)),
      processLeftJump_add (QS.leftLimits.const_mul a) (QX.leftLimits.const_mul (1 - a)),
      processLeftJump_const_mul QS.leftLimits, processLeftJump_const_mul QX.leftLimits,
      processLeftJump_const_mul QY.leftLimits, hR t, hS t, hX t, hY t,
      processLeftJump_add hXL (hYL.const_mul a), processLeftJump_add hXL hYL,
      processLeftJump_const_mul hYL]
    ring

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## The quadratic-root triangle inequality on one common full-measure event -/

open Filter MeasureTheory Set Topology
open scoped NNReal

private theorem sqrt_le_add_of_rational_polarization
    {u v s : Real} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : ∀ a : Rat, 0 ≤ (a : Real) * s + (1 - a) * u + ((a : Real) ^ 2 - a) * v) :
    Real.sqrt s ≤ Real.sqrt u + Real.sqrt v := by
  have hAll : ∀ a : Real, 0 ≤ a * s + (1 - a) * u + (a ^ 2 - a) * v := by
    intro a
    refine (Rat.denseRange_cast : DenseRange (fun q : Rat => (q : Real))).induction_on a ?_ h
    exact isClosed_le continuous_const (by fun_prop)
  have hDiscrim := discrim_le_zero (a := v) (b := s - u - v) (c := u) (by
    intro a
    have hEq : v * (a * a) + (s - u - v) * a + u =
        a * s + (1 - a) * u + (a ^ 2 - a) * v := by ring
    rw [hEq]
    exact hAll a)
  dsimp only [discrim] at hDiscrim
  have hProd : (2 * Real.sqrt u * Real.sqrt v) ^ 2 = 4 * u * v := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hu, Real.sq_sqrt hv]
    ring
  have hCross : s - u - v ≤ 2 * Real.sqrt u * Real.sqrt v := by
    nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : Real) ≤ 2)
      (Real.sqrt_nonneg u)) (Real.sqrt_nonneg v)]
  apply (Real.sqrt_le_iff).mpr
  refine ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  nlinarith [Real.sq_sqrt hu, Real.sq_sqrt hv]

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  {X Y : Process Ω}

theorem LocalMartingaleQuadraticVariation.root_triangle
    (hUsual : Filtration.UsualConditions mu F)
    (hX : LocalMartingale X F mu) (hY : LocalMartingale Y F mu)
    (hXA : StronglyAdapted F X) (hYA : StronglyAdapted F Y)
    (hXR : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hYR : ∀ w t, ContinuousWithinAt (Y · w) (Ici t) t)
    (hXL : ProcessHasLeftLimits X) (hYL : ProcessHasLeftLimits Y)
    (hXZero : X 0 = 0) (hYZero : Y 0 = 0)
    (QX : LocalMartingaleQuadraticVariation X F mu)
    (QY : LocalMartingaleQuadraticVariation Y F mu)
    (QS : LocalMartingaleQuadraticVariation (fun t w => X t w + Y t w) F mu) :
    ∀ᵐ w ∂mu, ∀ t,
      Real.sqrt (QS.variation t w) ≤
        Real.sqrt (QX.variation t w) + Real.sqrt (QY.variation t w) := by
  let : F.IsRightContinuous := hUsual.rightContinuous
  have hPoly (a : Rat) : ∀ᵐ w ∂mu, ∀ t,
      0 ≤ (a : Real) * QS.variation t w + (1 - a) * QX.variation t w +
        ((a : Real) ^ 2 - a) * QY.variation t w := by
    have hA : StronglyAdapted F (fun t w => X t w + (a : Real) * Y t w) :=
      fun t => (hXA t).add ((hYA t).const_mul (a : Real))
    have hR : ∀ w t, ContinuousWithinAt (fun s => X s w + (a : Real) * Y s w) (Ici t) t :=
      fun w t => (hXR w t).add ((hYR w t).const_mul (a : Real))
    have hZero : (fun w => X 0 w + (a : Real) * Y 0 w) = 0 := by
      funext w
      simp only [hXZero, hYZero, Pi.zero_apply, mul_zero, add_zero]
    obtain ⟨QR, _⟩ := exists_unique_localMartingaleQuadraticVariation
      (hX.add_of_rightContinuous (hY.smul (a : Real)) hXR
        (fun w t => (hYR w t).const_mul (a : Real))) hA hR
      (hXL.add (hYL.const_mul (a : Real))) hZero hUsual
    filter_upwards [QX.polarization hUsual hXR hYR hXL hYL QY QS (a : Real) QR] with w hw
    intro t
    rw [← hw t]
    have hMono := QR.monotone w (show (0 : NNReal) ≤ t from bot_le)
    simpa only [QR.zero, Pi.zero_apply] using hMono
  filter_upwards [ae_all_iff.mpr hPoly] with w hw
  intro t
  apply sqrt_le_add_of_rational_polarization
  · have hMono := QX.monotone w (show (0 : NNReal) ≤ t from bot_le)
    simpa only [QX.zero, Pi.zero_apply] using hMono
  · have hMono := QY.monotone w (show (0 : NNReal) ≤ t from bot_le)
    simpa only [QY.zero, Pi.zero_apply] using hMono
  · exact fun a => hw a t

theorem exists_quadraticVariations_root_triangle
    (hUsual : Filtration.UsualConditions mu F)
    (hX : LocalMartingale X F mu) (hY : LocalMartingale Y F mu)
    (hXA : StronglyAdapted F X) (hYA : StronglyAdapted F Y)
    (hXR : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hYR : ∀ w t, ContinuousWithinAt (Y · w) (Ici t) t)
    (hXL : ProcessHasLeftLimits X) (hYL : ProcessHasLeftLimits Y)
    (hXZero : X 0 = 0) (hYZero : Y 0 = 0) :
    ∃ QX : LocalMartingaleQuadraticVariation X F mu,
      ∃ QY : LocalMartingaleQuadraticVariation Y F mu,
        ∃ QS : LocalMartingaleQuadraticVariation (fun t w => X t w + Y t w) F mu,
          ∀ᵐ w ∂mu, ∀ t, Real.sqrt (QS.variation t w) ≤
            Real.sqrt (QX.variation t w) + Real.sqrt (QY.variation t w) := by
  obtain ⟨QX, _⟩ := exists_unique_localMartingaleQuadraticVariation
    hX hXA hXR hXL hXZero hUsual
  obtain ⟨QY, _⟩ := exists_unique_localMartingaleQuadraticVariation
    hY hYA hYR hYL hYZero hUsual
  have hZero : (fun w => X 0 w + Y 0 w) = 0 := by
    funext w
    simp only [hXZero, hYZero, Pi.zero_apply, add_zero]
  obtain ⟨QS, _⟩ := exists_unique_localMartingaleQuadraticVariation
    (hX.add_of_rightContinuous hY hXR hYR) (hXA.add hYA)
    (fun w t => (hXR w t).add (hYR w t)) (hXL.add hYL) hZero hUsual
  exact ⟨QX, QY, QS, QX.root_triangle hUsual hX hY hXA hYA hXR hYR hXL hYL hXZero hYZero QY QS⟩

end FTAPTheorem42
