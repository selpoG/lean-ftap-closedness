/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Topology.J1.Basic
import FTAPTheorem42.Stochastic.Integral.Elementary.LocalizedGoodIntegrator

/-! # The finite-variation part of the decomposition-to-good-integrator bridge -/

namespace FTAPTheorem42

open Filter MeasureTheory Topology
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  [IsFiniteMeasure mu] {X : Process Ω}

theorem J1Decomposition.finiteVariation_isSemimartingale (D : J1Decomposition X F mu) :
    IsSemimartingale D.A F mu :=
  isSemimartingale_of_locallyBoundedVariation D.A D.adaptedA D.rightA D.variationA

/-- The finite-variation contribution and the indistinguishable raw target
are discharged here. Only the elementary local-martingale estimate remains. -/
theorem J1Decomposition.isSemimartingale_of_martingalePart
    (D : J1Decomposition X F mu) (hN : IsSemimartingale D.N F mu) :
    IsSemimartingale X F mu := by
  have hA := D.finiteVariation_isSemimartingale
  have hEq (H : PredictableElementaryStrategy F) (T : NNReal) :
      ElementaryStrategy.gain X H.toElementary T =ᵐ[mu]
        (fun w => ElementaryStrategy.gain D.N H.toElementary T w +
          ElementaryStrategy.gain D.A H.toElementary T w) := by
    filter_upwards [D.decomposition] with w hw
    exact (H.toElementary.gain_congr_price T w hw).trans
      (ElementaryStrategy.gain_add_price D.N D.A H.toElementary T w)
  refine ⟨fun H T => ((hN.1 H T).add (hA.1 H T)).congr (hEq H T).symm, ?_⟩
  intro H hH T
  have hSum := tendstoInMeasure_add (hN.2 H hH T) (hA.2 H hH T)
  simp only [Pi.zero_apply, zero_add] at hSum
  exact hSum.congr (fun n => (hEq (H n) T).symm) Filter.EventuallyEq.rfl

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## Every J1 decomposition gives an elementary good integrator -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {mu : Measure Ω}
  [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] {X : Process Ω}

/-- DDY separates the possibly non-square-integrable jumps into an adapted
finite-variation process. Its remaining martingale has bounded closed stops,
so the elementary L² estimate applies before removing localization. -/
theorem J1Decomposition.isSemimartingale (D : J1Decomposition X F mu)
    (hUsual : Filtration.UsualConditions mu F) : IsSemimartingale X F mu := by
  let := hUsual.rightContinuous
  obtain ⟨B⟩ := HorizonFactorialGrid.exists_doleansDadeYenData
    D.localMartingale D.adaptedN D.rightN D.leftN D.zeroN
      (show (0 : Real) < 1 by norm_num) hUsual
  obtain ⟨R⟩ := B.exists_common_localizer_integrableVariation (by norm_num : (0 : Real) ≤ 1)
  have hL : IsSemimartingale B.L F mu := by
    apply isSemimartingale_of_stoppedProcess B.L_isStronglyAdapted B.L_rightContinuous
      R.isLocalizingSequence.toIsPreLocalizingSequence
    intro n
    apply isSemimartingale_of_squareIntegrable_martingale (R.L_martingale n)
      (RightContinuousStoppedMartingale.stoppedProcess_rightContinuous B.L B.L_rightContinuous)
    intro T
    apply MemLp.of_bound (((R.L_martingale n).stronglyAdapted T).mono
      (F.le T)).aestronglyMeasurable (cadlagPassageLevel n + 2 * 1)
    filter_upwards [R.L_bound n] with w hw
    exact (Real.norm_eq_abs _).symm ▸ hw T
  let E : J1Decomposition X F mu := {
    N := B.L
    A := B.Q + D.A
    decomposition := by
      filter_upwards [D.decomposition] with w hw
      intro t
      have hN := congrFun (congrFun B.decomposition t) w
      rw [hw t, hN]
      exact add_assoc _ _ _
    localMartingale := B.L_isLocalMartingale
    adaptedN := B.L_isStronglyAdapted
    rightN := B.L_rightContinuous
    leftN := B.L_leftLimits
    zeroN := B.L_zero
    adaptedA := B.Q_isStronglyAdapted.add D.adaptedA
    rightA := fun w t => (B.Q_rightContinuous w t).add (D.rightA w t)
    leftA := B.Q_leftLimits.add D.leftA
    variationA := fun w a b ha hb =>
      boundedVariationOn_add (B.Q_locallyBoundedVariation w a b ha hb) (D.variationA w a b ha hb)
    zeroA := by simp only [Pi.add_apply, B.Q_zero, D.zeroA, add_zero] }
  exact E.isSemimartingale_of_martingalePart hL

end FTAPTheorem42
