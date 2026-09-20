/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Quadratic.LocalMartingaleQuadraticCappedLocalization

/-! # Intrinsic certificates for existing finite-horizon and glued quadratic data -/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  {M : Process Ω} {T : NNReal}

noncomputable def BoundedMartingaleQuadraticKernel.Data.toIntrinsic
    (D : BoundedMartingaleQuadraticKernel.Data F mu M T)
    (hM : Martingale M F mu)
    (hRight : ∀ w t, ContinuousWithinAt (M · w) (Ici t) t)
    (hLeft : ProcessHasLeftLimits M) (hZero : M 0 = 0) :
    LocalMartingaleQuadraticVariation
      (deterministicallyStoppedProcess M T) F mu := by
  let X := deterministicallyStoppedProcess M T
  have hXR := BoundedMartingaleQuadraticApproximation.stoppedSource_rightContinuous M hRight T
  have hXM := martingale_deterministicallyStopped hM hRight T
  have hBV : ∀ w, LocallyBoundedVariationOn (D.variation · w) univ := fun w =>
    ((D.variation_monotone w).monotoneOn univ).locallyBoundedVariationOn
  refine {
    variation := D.variation
    stronglyAdapted := D.variation_isStronglyAdapted
    rightContinuous := D.variation_rightContinuous
    leftLimits :=
      SpecialSemimartingaleDecomposition.finiteVariationPart_hasLeftLimits_of_localBoundedVariation
        hBV
    locallyBoundedVariation := hBV
    monotone := D.variation_monotone
    zero := D.variation_zero
    jump_sq := D.processLeftJump_variation_eq_sq hLeft
    squareResidual := ?_ }
  have hLocal : LocalMartingale D.martingalePart F mu :=
    Locally.of_prop D.martingalePart_isMartingale
  apply hLocal.congr_indistinguishable
    (fun t => ((hXM.stronglyAdapted t).pow 2).sub (D.variation_isStronglyAdapted t))
    (fun w t => ((hXR w t).pow 2).sub (D.variation_rightContinuous w t))
  filter_upwards [D.variation_indistinguishable_raw] with w hw
  intro t
  have h := hw t
  simp only [BoundedMartingaleQuadraticKernel.rawVariation,
    deterministicallyStoppedProcess_apply, zero_min,
    hZero, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), sub_zero] at h
  change D.martingalePart t w = X t w ^ 2 - D.variation t w
  dsimp only [X]
  rw [deterministicallyStoppedProcess_apply]
  linarith

noncomputable def LocalMartingaleQuadratic.GluedQuadraticVariationCertificate.toIntrinsic
    {C : LocalMartingaleQuadratic.LocalMartingaleQuadraticSchedule
      (F := F) (mu := mu) (M := M)}
    (Q : LocalMartingaleQuadratic.GluedQuadraticVariationCertificate C) (hZero : M 0 = 0) :
    LocalMartingaleQuadraticVariation M F mu where
  variation := Q.variation
  stronglyAdapted := Q.variation_isStronglyAdapted
  rightContinuous := Q.variation_rightContinuous
  leftLimits := Q.variation_hasLeftLimits
  locallyBoundedVariation := Q.variation_locallyBoundedVariation
  monotone := Q.variation_monotone
  zero := Q.variation_zero
  jump_sq := Q.leftJump_eq_sq
  squareResidual := by
    simpa only [hZero, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), sub_zero] using
      Q.squareResidual_isLocalMartingale

end FTAPTheorem42
