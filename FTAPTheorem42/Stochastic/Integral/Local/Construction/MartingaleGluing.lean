/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Basic.CompatibleLocalMartingaleGluing
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.M2ACoefficientRestriction
import FTAPTheorem42.Stochastic.Integral.Local.Construction.BoundedCoordinateSemantics

/-!
# Gluing local completed martingale coordinates

One intrinsic graph witness supplies a completed martingale integral on each
coordinate of an exhaustive schedule.  Predictable restriction acts on the
coefficient of every coordinate.  Pairwise schedule refinement shows that
these restricted completed integrals agree on overlaps, so they glue to one
global right-continuous local martingale.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace LocalCompletedM2A

open BoundedMartingaleQuadraticEnergy.Data
open SIntegrableFiniteVariationBridge

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  [F.IsRightContinuous]
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : LocallySIntegrableStrategy D}

/-- The completed martingale integral of one schedule coefficient. -/
noncomputable def completedMartingaleCoordinate
    (schedule : LocalCompletedM2ASchedule G)
    (coefficient : forall n, FiniteHorizonM2ACoefficient
      (schedule.variationBridge n) (schedule.quadraticKernel n))
    (n : Nat) : Process Omega :=
  finiteHorizonCompletedMartingalePart schedule.usualConditions
    (schedule.horizon n) (schedule.quadraticKernel n)
      (schedule.martingale n) (schedule.terminal_memLp n) (coefficient n)

omit [F.IsRightContinuous] in
/-- Two coefficients over the same finite-horizon source define the same
completed martingale process when their raw coefficients agree. -/
theorem completedMartingalePart_indistinguishable_of_coefficient_eq
    {P : SIntegrableStrategy D} {T : NNReal}
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data F mu P.martingalePart T)
    (E : SIntegrableFiniteVariationBridge P)
    (hPMartingale : Martingale P.martingalePart F mu)
    (hPTerminal : MemLp (P.martingalePart T) (2 : ENNReal) mu)
    (c d : FiniteHorizonM2ACoefficient E Q)
    (hcd : c.coefficient = d.coefficient) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedMartingalePart hUsual T Q hPMartingale
        hPTerminal c)
      (finiteHorizonCompletedMartingalePart hUsual T Q hPMartingale
        hPTerminal d) := by
  have hc : Function.uncurry c.integrand
      =ᵐ[Q.predictableEnergyMeasure] c.coefficient := by
    simpa only [FiniteHorizonM2ACoefficient.integrand] using
      finiteHorizonCoefficient_ae_eq
        Q c.coefficient
  have hd : Function.uncurry d.integrand
      =ᵐ[Q.predictableEnergyMeasure] d.coefficient := by
    simpa only [FiniteHorizonM2ACoefficient.integrand] using
      finiteHorizonCoefficient_ae_eq
        Q d.coefficient
  have hCoefficientAE : c.coefficient
      =ᵐ[Q.predictableEnergyMeasure] d.coefficient :=
    Filter.Eventually.of_forall fun point => congrFun hcd point
  have hcdAE : Function.uncurry c.integrand
      =ᵐ[Q.predictableEnergyMeasure] Function.uncurry d.integrand :=
    hc.trans (hCoefficientAE.trans hd.symm)
  exact finiteHorizonMartingaleIntegralProcess_indistinguishable_of_ae_eq
    hUsual Q hPMartingale P.martingalePart_isRightContinuous hPTerminal
      (Function.uncurry c.integrand) c.integrand_isStronglyPredictable
        c.integrand_memLp_energy
      (Function.uncurry d.integrand) d.integrand_isStronglyPredictable
        d.integrand_memLp_energy hcdAE

omit [F.IsRightContinuous] in
/-- A completed martingale coordinate is already stopped at the localizer
carried by its source prefix. -/
theorem completedMartingaleCoordinate_indistinguishable_stopped
    (schedule : LocalCompletedM2ASchedule G)
    (coefficient : forall n, FiniteHorizonM2ACoefficient
      (schedule.variationBridge n) (schedule.quadraticKernel n))
    (n : Nat) :
    ProcessIndistinguishable mu
      (completedMartingaleCoordinate schedule coefficient n)
      (MeasureTheory.stoppedProcess
        (completedMartingaleCoordinate schedule coefficient n)
        (schedule.localizer n)) := by
  let tau := scheduleFiniteLocalizer schedule n
  let B := stochasticIntervalIocZero tau
  let f := Function.uncurry (coefficient n).integrand
  let hB : MeasurableSet[F.predictable] B :=
    IsStoppingTime.measurableSet_stochasticIntervalIocZero
      (scheduleFiniteLocalizer_isStoppingTime schedule n)
  have hSupport : ∀ᵐ point ∂(schedule.quadraticKernel n
      ).predictableEnergyMeasure, point ∈ B := by
    simpa only [B, tau] using schedule_ae_mem_stochasticInterval schedule n
  have hAE : f =ᵐ[(schedule.quadraticKernel n).predictableEnergyMeasure]
      B.indicator f := by
    filter_upwards [hSupport] with point hPoint
    simp only [Set.indicator_of_mem hPoint]
  have hCongr : ProcessIndistinguishable mu
      (completedMartingaleCoordinate schedule coefficient n)
      (finiteHorizonMartingaleIntegralProcess schedule.usualConditions
        (schedule.quadraticKernel n) (schedule.martingale n)
        (schedule.sourcePrefix n).martingalePart_isRightContinuous
        (schedule.terminal_memLp n) (B.indicator f)
        ((coefficient n).integrand_isStronglyPredictable.indicator hB)
        ((coefficient n).integrand_memLp_energy.indicator hB)) := by
    exact finiteHorizonMartingaleIntegralProcess_indistinguishable_of_ae_eq
      schedule.usualConditions (schedule.quadraticKernel n)
      (schedule.martingale n)
      (schedule.sourcePrefix n).martingalePart_isRightContinuous
      (schedule.terminal_memLp n) f
      (coefficient n).integrand_isStronglyPredictable
      (coefficient n).integrand_memLp_energy (B.indicator f)
      ((coefficient n).integrand_isStronglyPredictable.indicator hB)
      ((coefficient n).integrand_memLp_energy.indicator hB) hAE
  have hStop :=
    finiteHorizonMartingaleIntegralProcess_restrict_stochasticInterval
      schedule.usualConditions (schedule.quadraticKernel n)
      (schedule.martingale n)
      (schedule.sourcePrefix n).martingalePart_isRightContinuous
      (schedule.terminal_memLp n) tau
      (scheduleFiniteLocalizer_isStoppingTime schedule n)
      (scheduleFiniteLocalizer_le_horizon schedule n) f
      (coefficient n).integrand_isStronglyPredictable
      (coefficient n).integrand_memLp_energy
  have hStopCoordinate : ProcessIndistinguishable mu
      (finiteHorizonMartingaleIntegralProcess schedule.usualConditions
        (schedule.quadraticKernel n) (schedule.martingale n)
        (schedule.sourcePrefix n).martingalePart_isRightContinuous
        (schedule.terminal_memLp n) (B.indicator f)
        ((coefficient n).integrand_isStronglyPredictable.indicator hB)
        ((coefficient n).integrand_memLp_energy.indicator hB))
      (MeasureTheory.stoppedProcess
        (completedMartingaleCoordinate schedule coefficient n)
        (schedule.localizer n)) := by
    rw [completedMartingaleCoordinate, finiteHorizonCompletedMartingalePart]
    simpa only [tau, B, f, hB, completedMartingaleCoordinate,
      coe_scheduleFiniteLocalizer] using hStop
  exact hCongr.trans hStopCoordinate

omit [F.IsRightContinuous] in
/-- A common raw coefficient on an exhaustive completed schedule yields
compatible completed martingale coordinates. -/
theorem completedMartingaleCoordinates_compatible
    (schedule : LocalCompletedM2ASchedule G)
    (coefficient : forall n, FiniteHorizonM2ACoefficient
      (schedule.variationBridge n) (schedule.quadraticKernel n))
    {f : NNReal × Omega -> Real}
    (hCoefficient : forall n, (coefficient n).coefficient = f)
    (n m : Nat) :
    ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess
        (completedMartingaleCoordinate schedule coefficient n)
        (min (schedule.localizer n) (schedule.localizer m)))
      (MeasureTheory.stoppedProcess
        (completedMartingaleCoordinate schedule coefficient m)
        (min (schedule.localizer n) (schedule.localizer m))) := by
  let left := schedule.tailFrom n
  let right := schedule.tailFrom m
  let c : FiniteHorizonM2ACoefficient
      (left.variationBridge 0) (left.quadraticKernel 0) := coefficient n
  let d : FiniteHorizonM2ACoefficient
      (right.variationBridge 0) (right.quadraticKernel 0) := coefficient m
  let pc := pairScheduleCoefficientLeft left right 0 c
  let pd := pairScheduleCoefficientRight left right 0 d
  have hpcd : pc.coefficient = pd.coefficient := by
    change (coefficient n).coefficient = (coefficient m).coefficient
    exact (hCoefficient n).trans (hCoefficient m).symm
  have hPair : ProcessIndistinguishable mu
      (finiteHorizonCompletedMartingalePart left.usualConditions
        (pairScheduleHorizon left right 0)
        (pairScheduleQuadraticKernel left right 0)
        (pairScheduleSourcePrefix_martingale left right 0)
        (pairScheduleSourcePrefix_terminal_memLp left right 0) pc)
      (finiteHorizonCompletedMartingalePart left.usualConditions
        (pairScheduleHorizon left right 0)
        (pairScheduleQuadraticKernel left right 0)
        (pairScheduleSourcePrefix_martingale left right 0)
        (pairScheduleSourcePrefix_terminal_memLp left right 0) pd) :=
    completedMartingalePart_indistinguishable_of_coefficient_eq
      left.usualConditions (pairScheduleQuadraticKernel left right 0)
      (pairScheduleFiniteVariationBridge left right 0)
      (pairScheduleSourcePrefix_martingale left right 0)
      (pairScheduleSourcePrefix_terminal_memLp left right 0) pc pd hpcd
  have hLeft := pairScheduleCompletedMartingalePart_left left right 0 c
  have hRight := pairScheduleCompletedMartingalePart_right left right 0 d
  have hResult := hLeft.symm.trans (hPair.trans hRight)
  change ProcessIndistinguishable mu
    (MeasureTheory.stoppedProcess
      (completedMartingaleCoordinate schedule coefficient n)
      (min (schedule.localizer n) (schedule.localizer m)))
    (MeasureTheory.stoppedProcess
      (completedMartingaleCoordinate schedule coefficient m)
      (min (schedule.localizer n) (schedule.localizer m))) at hResult
  exact hResult

omit [F.IsRightContinuous] in
/-- Predictably restricted completed martingale coordinates of one graph
witness glue to a global right-continuous local martingale. -/
theorem GraphWitness.exists_restrictedMartingalePart
    {H : SIntegrableStrategy D} (witness : GraphWitness G H)
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B) :
    exists M : Process Omega,
      StronglyAdapted F M /\
        LocalMartingale M F mu /\
        (forall omega t, ContinuousWithinAt (M · omega) (Ici t) t) /\
        forall n, ProcessIndistinguishable mu
          (MeasureTheory.stoppedProcess M (witness.schedule.localizer n))
          (completedMartingaleCoordinate witness.schedule
            (fun k => (witness.coefficient k).restrictPredictable B hB) n) := by
  let coefficient := fun n =>
    (witness.coefficient n).restrictPredictable B hB
  have hCoefficient : forall n,
      (coefficient n).coefficient = B.indicator (Function.uncurry H.integrand) := by
    intro n
    change B.indicator (witness.coefficient n).coefficient = _
    rw [witness.coefficient_eq n]
  have hMartingale : forall n,
      Martingale (completedMartingaleCoordinate witness.schedule coefficient n)
        F mu := by
    intro n
    exact finiteHorizonMartingaleIntegralProcess_isMartingale
      witness.schedule.usualConditions (witness.schedule.quadraticKernel n)
      (witness.schedule.martingale n)
      (witness.schedule.sourcePrefix n).martingalePart_isRightContinuous
      (witness.schedule.terminal_memLp n)
      (Function.uncurry (coefficient n).integrand)
      (coefficient n).integrand_isStronglyPredictable
      (coefficient n).integrand_memLp_energy
  have hRight : forall n omega t,
      ContinuousWithinAt
        (completedMartingaleCoordinate witness.schedule coefficient n · omega)
        (Ici t) t := by
    intro n
    exact finiteHorizonMartingaleIntegralProcess_rightContinuous
      witness.schedule.usualConditions (witness.schedule.quadraticKernel n)
      (witness.schedule.martingale n)
      (witness.schedule.sourcePrefix n).martingalePart_isRightContinuous
      (witness.schedule.terminal_memLp n)
      (Function.uncurry (coefficient n).integrand)
      (coefficient n).integrand_isStronglyPredictable
      (coefficient n).integrand_memLp_energy
  obtain ⟨M, hMAdapted, hMLocal, hMRight, hMStopped⟩ :=
    FTAPTheorem42.CompatibleLocalMartingaleGluing.exists_rightContinuous_localMartingale
      witness.schedule.usualConditions
        witness.schedule.isLocalizingSequence hMartingale hRight
        (completedMartingaleCoordinates_compatible witness.schedule
          coefficient hCoefficient)
  exact ⟨M, hMAdapted, hMLocal, hMRight, fun n =>
    (hMStopped n).trans
      (completedMartingaleCoordinate_indistinguishable_stopped
        witness.schedule coefficient n).symm⟩

end LocalCompletedM2A

end FTAPTheorem42
