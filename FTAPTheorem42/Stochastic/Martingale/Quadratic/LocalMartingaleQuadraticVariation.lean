/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.FiniteVariation.ContinuousLocalVariationRigidity

/-! # Intrinsic quadratic variation from square residuals and jumps -/

open Filter MeasureTheory Set Topology
open scoped NNReal

namespace FTAPTheorem42

open PredictableFiniteVariationLocalMartingale

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω}

/-- The comparison candidate need not be increasing. Equal jumps make
the finite-variation martingale difference continuous. -/
theorem quadraticVariation_indistinguishable
    [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] [F.IsRightContinuous]
    (hUsual : Filtration.UsualConditions mu F) {X V W : Process Ω}
    (hXRight : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (hVAdapted : StronglyAdapted F V) (hWAdapted : StronglyAdapted F W)
    (hVRight : ∀ w t, ContinuousWithinAt (V · w) (Ici t) t)
    (hWRight : ∀ w t, ContinuousWithinAt (W · w) (Ici t) t)
    (hVLeft : ProcessHasLeftLimits V) (hWLeft : ProcessHasLeftLimits W)
    (hVBV : ∀ w, LocallyBoundedVariationOn (V · w) univ)
    (hWBV : ∀ w, LocallyBoundedVariationOn (W · w) univ)
    (hZero : V 0 = W 0)
    (hJump : ∀ᵐ w ∂mu, ∀ t, processLeftJump V t w = processLeftJump W t w)
    (hV : LocalMartingale (fun t w => X t w ^ 2 - V t w) F mu)
    (hW : LocalMartingale (fun t w => X t w ^ 2 - W t w) F mu) :
    ProcessIndistinguishable mu V W := by
  let A : Process Ω := fun t w => V t w - W t w
  have hAdapted : StronglyAdapted F A := hVAdapted.sub hWAdapted
  have hRight : ∀ w t, ContinuousWithinAt (A · w) (Ici t) t :=
    fun w t => (hVRight w t).sub (hWRight w t)
  have hA : LocalMartingale A F mu := by
    have hDiff := hW.add_of_rightContinuous hV.neg
      (fun w t => ((hXRight w t).pow 2).sub (hWRight w t))
      (fun w t => (((hXRight w t).pow 2).sub (hVRight w t)).neg)
    apply hDiff.congr_indistinguishable hAdapted hRight
    exact Eventually.of_forall fun w t => by dsimp only [A]; ring
  have hContinuous : ∀ᵐ w ∂mu, Continuous (A · w) := by
    filter_upwards [hJump] with w hw
    apply continuous_of_rightContinuous_of_processLeftJump_eq_zero
        (A · w) (hRight w) ((hVLeft.sub hWLeft) w)
    intro t
    change processLeftJump (fun s w => V s w - W s w) t w = 0
    rw [processLeftJump_sub hVLeft hWLeft, hw t, sub_self]
  have hAZ := hA.indistinguishable_zero_of_ae_continuous_locallyBoundedVariation
    hUsual hAdapted hRight (fun w a b ha hb => ?_) hContinuous (by
      funext w
      change V 0 w - W 0 w = 0
      rw [hZero, sub_self])
  · filter_upwards [hAZ] with w hw
    exact fun t => sub_eq_zero.mp (hw t)
  · exact boundedVariationOn_add (hVBV w a b ha hb)
      (boundedVariationOn_neg (hWBV w a b ha hb))

/-- Semantic data for a zero-initial quadratic variation. Construction
choices such as DDY thresholds and convex grid schedules are absent. -/
structure LocalMartingaleQuadraticVariation (X : Process Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω)) (mu : Measure Ω) where
  variation : Process Ω
  stronglyAdapted : StronglyAdapted F variation
  rightContinuous : ∀ w t, ContinuousWithinAt (variation · w) (Ici t) t
  leftLimits : ProcessHasLeftLimits variation
  locallyBoundedVariation : ∀ w, LocallyBoundedVariationOn (variation · w) univ
  monotone : ∀ w, Monotone (variation · w)
  zero : variation 0 = 0
  jump_sq : ∀ᵐ w ∂mu, ∀ t, processLeftJump variation t w = (processLeftJump X t w) ^ 2
  squareResidual : LocalMartingale (fun t w => X t w ^ 2 - variation t w) F mu

theorem LocalMartingaleQuadraticVariation.unique
    [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] [F.IsRightContinuous]
    (hUsual : Filtration.UsualConditions mu F) {X : Process Ω}
    (hXRight : ∀ w t, ContinuousWithinAt (X · w) (Ici t) t)
    (Q R : LocalMartingaleQuadraticVariation X F mu) :
    ProcessIndistinguishable mu Q.variation R.variation := by
  apply quadraticVariation_indistinguishable hUsual hXRight
    Q.stronglyAdapted R.stronglyAdapted Q.rightContinuous R.rightContinuous
    Q.leftLimits R.leftLimits
    Q.locallyBoundedVariation R.locallyBoundedVariation (Q.zero.trans R.zero.symm)
    _ Q.squareResidual R.squareResidual
  filter_upwards [Q.jump_sq, R.jump_sq] with w hQ hR
  exact fun t => (hQ t).trans (hR t).symm

end FTAPTheorem42
