/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.MaximalProbability
import FTAPTheorem42.Stochastic.Martingale.Quadratic.SquareIntegrableMartingaleQuadraticProcessLimit
import FTAPTheorem42.Stochastic.Integral.Localization.DirectPassageM2A
import FTAPTheorem42.Stochastic.Integral.Local.Construction.UnitSourceRealization
import FTAPTheorem42.Stochastic.Integral.General.IntegralGraphTruncationConvergence
import FTAPTheorem42.Stochastic.Integral.General.BoundedPredictableIntegralGraph
import FTAPTheorem42.Stochastic.Integral.General.CommonScheduleElementaryApproximation
import FTAPTheorem42.Stochastic.Topology.Emery.RealizedComposition

/-! # Actual integration of an L²-enveloped original gain

The jump envelope supplies a direct completed schedule. Elementary composition
then returns its actual integrals to the original price.
-/

/-! ## A direct completed schedule -/

open Filter MeasureTheory Set Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace FTAPTheorem42.LocalCompletedM2A

open SIntegrableFiniteVariationBridge

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  {D : SpecialSemimartingaleDecomposition S F μ}

/-- A direct M2/A1 schedule for a regular local special gain with an L2
all-time envelope and a centered martingale component. -/
noncomputable def directScheduleOfL2Gain
    (G : LocallySIntegrableStrategy D) (hUsual : Filtration.UsualConditions μ F)
    (hM0 : G.martingalePart 0 = 0) (hML : ProcessHasLeftLimits G.martingalePart)
    (ξ : Ω → Real) (hξ : MemLp ξ 2 μ)
    (hBound : ∀ᵐ ω ∂μ, ∀ t, |G.stochasticIntegral t ω| ≤ ξ ω) :
    LocalCompletedM2ASchedule G := by
  let := hUsual.rightContinuous
  let U n := G.deterministicallyStopped (cadlagPassageHorizon n) (cadlagPassageHorizon_pos n)
  have hU0 n : (U n).martingalePart 0 = 0 := by
    funext ω
    change G.martingalePart (min 0 _) ω = 0
    rw [min_eq_left (zero_le : (0 : NNReal) ≤ _), congrFun hM0 ω]
    rfl
  let P n := (U n).directPassage (hU0 n) n
  have hP n : Martingale (P n).martingalePart F μ ∧
      MemLp ((P n).martingalePart (cadlagPassageHorizon n)) 2 μ := by
    apply (U n).directPassage_martingale_l2 (hU0 n) (hML.deterministicallyStopped _)
      hUsual ξ hξ _ n
    filter_upwards [hBound] with ω hω
    intro t
    exact hω (min t (cadlagPassageHorizon n))
  have hStop n : (fun ω => (cadlagAbsolutePassageLocalizerFinite
      (U n).martingalePart n ω : WithTop NNReal)) =
      cadlagAbsolutePassageLocalizer G.martingalePart n := by
    funext ω
    rw [coe_cadlagAbsolutePassageLocalizerFinite]
    exact min_absoluteStrictHittingAfter_deterministicallyStopped
      G.martingalePart (cadlagPassageLevel n) (cadlagPassageHorizon n) ω
  refine {
    usualConditions := hUsual
    localizer := cadlagAbsolutePassageLocalizer G.martingalePart
    isLocalizingSequence := cadlagAbsolutePassageLocalizer_isLocalizingSequence
      G.martingalePart_isStronglyAdapted G.martingalePart_isRightContinuous hML
    horizon := cadlagPassageHorizon
    horizon_pos := cadlagPassageHorizon_pos
    localizer_le_horizon := fun _ _ => min_le_right _ _
    sourcePrefix := P
    sourcePrefix_stochasticIntegral := ?_
    sourcePrefix_martingalePart := ?_
    sourcePrefix_finiteVariationPart := ?_
    martingale := fun n => (hP n).1
    terminal_memLp := fun n => (hP n).2
    variationBridge := fun n => ofCumulativeVariationNormalized
      (P n).finiteVariationPart_isRightContinuous
    quadraticKernel := fun n => Classical.choice
      (SquareIntegrableMartingaleQuadraticKernel.exists_data hUsual (hP n).1
        (P n).martingalePart_isRightContinuous (cadlagPassageHorizon n) (hP n).2) }
  all_goals
    intro n
    dsimp only [P, SIntegrableStrategy.directPassage,
      LocallySIntegrableStrategy.finiteClosedStop,
      LocallySIntegrableStrategy.finiteClosedStopOfRightContinuous, SIntegrableStrategy.toLocally]
    rw [hStop]
    exact ProcessIndistinguishable.refl μ _

end FTAPTheorem42.LocalCompletedM2A

/-! ## Realization over the original price -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal

namespace FTAPTheorem42.LocalCompletedM2A

variable {Ω : Type*} [MeasurableSpace Ω]
  {S P : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  {D : SpecialSemimartingaleDecomposition P F μ}

/-- Every global actual integral of an L2-enveloped realized gain is itself
an integral of the original price. Its coefficient need not be bounded. -/
theorem exists_realization_of_actual_over_L2Gain
    (hS : IsStronglyProgressive F S)
    (hSR : ∀ ω t, ContinuousWithinAt (S · ω) (Ici t) t)
    (R : PredictableElementaryEmery.RealizedStrategy (ℱ := F) μ S)
    (G : LocallySIntegrableStrategy D) (hGain : G.stochasticIntegral = R.gain)
    (hUsual : Filtration.UsualConditions μ F)
    (hM0 : G.martingalePart 0 = 0) (hML : ProcessHasLeftLimits G.martingalePart)
    (ξ : Ω → Real) (hξ : MemLp ξ 2 μ)
    (hBound : ∀ᵐ ω ∂μ, ∀ t, |G.stochasticIntegral t ω| ≤ ξ ω)
    (H : ActualSIntegrableStrategy (realizationModel G)) :
    ∃ V : PredictableElementaryEmery.RealizedStrategy (ℱ := F) μ S,
      ProcessIndistinguishable μ V.gain H.val.stochasticIntegral := by
  let schedule := directScheduleOfL2Gain G hUsual hM0 hML ξ hξ hBound
  obtain ⟨A⟩ := IsTruncatedIntegralGraph.of_globalActual hML H
  have hApprox := A.elementaryApproximable schedule
  rw [hGain] at hApprox
  have hOrig := R.elementaryApproximable_comp hS hSR
    (StronglyAdapted.isStronglyProgressive_of_rightContinuous
      A.regularGain_adapted A.regularGain_right) A.regularGain_right hApprox
  obtain ⟨V, hV⟩ := hOrig.exists_realizedStrategy hS hSR A.regularGain_adapted
    A.regularGain_right A.regularGain_left A.regularGain_zero
  exact ⟨V, hV ▸ A.gain_indistinguishable⟩

end FTAPTheorem42.LocalCompletedM2A
