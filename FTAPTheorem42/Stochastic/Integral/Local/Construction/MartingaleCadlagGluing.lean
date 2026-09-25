/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedM2ACadlag
import FTAPTheorem42.Stochastic.Integral.Local.Construction.MartingaleGluing

/-!
# Gluing càdlàg completed martingale coordinates

When every finite-horizon source martingale in a local completed schedule
has left limits, the corresponding completed integral has a càdlàg version.
Those versions retain the overlap compatibility of the ordinary completed
coordinates and therefore glue to one càdlàg local martingale.
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

/-- The càdlàg version of one completed martingale coordinate. -/
noncomputable def completedMartingaleCadlagCoordinate
    (schedule : LocalCompletedM2ASchedule G)
    (hSourceLeft : forall n,
      ProcessHasLeftLimits (schedule.sourcePrefix n).martingalePart)
    (coefficient : forall n, FiniteHorizonM2ACoefficient
      (schedule.variationBridge n) (schedule.quadraticKernel n))
    (n : Nat) : Process Omega :=
  finiteHorizonCompletedMartingaleCadlagPart schedule.usualConditions
    (schedule.quadraticKernel n) (schedule.martingale n) (hSourceLeft n)
      (schedule.terminal_memLp n) (coefficient n)

omit [F.IsRightContinuous] in
/-- The càdlàg coordinate is a version of the ordinary completed
coordinate. -/
theorem completedMartingaleCadlagCoordinate_indistinguishable
    (schedule : LocalCompletedM2ASchedule G)
    (hSourceLeft : forall n,
      ProcessHasLeftLimits (schedule.sourcePrefix n).martingalePart)
    (coefficient : forall n, FiniteHorizonM2ACoefficient
      (schedule.variationBridge n) (schedule.quadraticKernel n))
    (n : Nat) :
    ProcessIndistinguishable mu
      (completedMartingaleCadlagCoordinate schedule hSourceLeft coefficient n)
      (completedMartingaleCoordinate schedule coefficient n) := by
  exact finiteHorizonCompletedMartingaleCadlagPart_indistinguishable
    schedule.usualConditions (schedule.quadraticKernel n)
      (schedule.martingale n) (hSourceLeft n)
        (schedule.terminal_memLp n) (coefficient n)

omit [F.IsRightContinuous] in
/-- Càdlàg completed coordinates inherit overlap compatibility from the
ordinary completed coordinates. -/
theorem completedMartingaleCadlagCoordinates_compatible
    (schedule : LocalCompletedM2ASchedule G)
    (hSourceLeft : forall n,
      ProcessHasLeftLimits (schedule.sourcePrefix n).martingalePart)
    (coefficient : forall n, FiniteHorizonM2ACoefficient
      (schedule.variationBridge n) (schedule.quadraticKernel n))
    {f : NNReal × Omega -> Real}
    (hCoefficient : forall n, (coefficient n).coefficient = f)
    (n m : Nat) :
    ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess
        (completedMartingaleCadlagCoordinate schedule hSourceLeft coefficient n)
        (min (schedule.localizer n) (schedule.localizer m)))
      (MeasureTheory.stoppedProcess
        (completedMartingaleCadlagCoordinate schedule hSourceLeft coefficient m)
        (min (schedule.localizer n) (schedule.localizer m))) := by
  let tau := min (schedule.localizer n) (schedule.localizer m)
  have hLeft :=
    (completedMartingaleCadlagCoordinate_indistinguishable
      schedule hSourceLeft coefficient n).stoppedProcess tau
  have hMiddle := completedMartingaleCoordinates_compatible schedule
    coefficient hCoefficient n m
  have hRight :=
    (completedMartingaleCadlagCoordinate_indistinguishable
      schedule hSourceLeft coefficient m).stoppedProcess tau
  exact hLeft.trans (hMiddle.trans hRight.symm)

omit [F.IsRightContinuous] in
/-- A càdlàg coordinate remains unchanged after its schedule stop. -/
theorem completedMartingaleCadlagCoordinate_indistinguishable_stopped
    (schedule : LocalCompletedM2ASchedule G)
    (hSourceLeft : forall n,
      ProcessHasLeftLimits (schedule.sourcePrefix n).martingalePart)
    (coefficient : forall n, FiniteHorizonM2ACoefficient
      (schedule.variationBridge n) (schedule.quadraticKernel n))
    (n : Nat) :
    ProcessIndistinguishable mu
      (completedMartingaleCadlagCoordinate schedule hSourceLeft coefficient n)
      (MeasureTheory.stoppedProcess
        (completedMartingaleCadlagCoordinate schedule hSourceLeft coefficient n)
        (schedule.localizer n)) := by
  have hVersion := completedMartingaleCadlagCoordinate_indistinguishable
    schedule hSourceLeft coefficient n
  exact hVersion.trans
    ((completedMartingaleCoordinate_indistinguishable_stopped
      schedule coefficient n).trans
        (hVersion.stoppedProcess (schedule.localizer n)).symm)

omit [F.IsRightContinuous] in
/-- Compatible completed coefficients give a càdlàg local martingale without
requiring a previously realized global strategy. -/
theorem exists_completedCadlagMartingalePart
    (schedule : LocalCompletedM2ASchedule G)
    (hSourceLeft : ∀ n,
      ProcessHasLeftLimits (schedule.sourcePrefix n).martingalePart)
    (coefficient : ∀ n, FiniteHorizonM2ACoefficient
      (schedule.variationBridge n) (schedule.quadraticKernel n))
    {f : NNReal × Omega → Real}
    (hCoefficient : ∀ n, (coefficient n).coefficient = f) :
    ∃ M : Process Omega,
      StronglyAdapted F M ∧ LocalMartingale M F mu ∧
      (∀ omega t, ContinuousWithinAt (M · omega) (Ici t) t) ∧
      ProcessHasLeftLimits M ∧
      ∀ n, ProcessIndistinguishable mu
        (MeasureTheory.stoppedProcess M (schedule.localizer n))
        (completedMartingaleCadlagCoordinate schedule hSourceLeft coefficient n) := by
  have hMartingale : forall n,
      Martingale (completedMartingaleCadlagCoordinate schedule
        hSourceLeft coefficient n) F mu := by
    intro n
    exact finiteHorizonMartingaleIntegralCadlagProcess_isMartingale
      schedule.usualConditions (schedule.quadraticKernel n)
      (schedule.martingale n)
      (schedule.sourcePrefix n).martingalePart_isRightContinuous
      (hSourceLeft n) (schedule.terminal_memLp n)
      (Function.uncurry (coefficient n).integrand)
      (coefficient n).integrand_isStronglyPredictable
      (coefficient n).integrand_memLp_energy
  have hRight : forall n omega t,
      ContinuousWithinAt
        (completedMartingaleCadlagCoordinate schedule hSourceLeft
          coefficient n · omega) (Ici t) t := by
    intro n
    exact finiteHorizonMartingaleIntegralCadlagProcess_rightContinuous
      schedule.usualConditions (schedule.quadraticKernel n)
      (schedule.martingale n)
      (schedule.sourcePrefix n).martingalePart_isRightContinuous
      (hSourceLeft n) (schedule.terminal_memLp n)
      (Function.uncurry (coefficient n).integrand)
      (coefficient n).integrand_isStronglyPredictable
      (coefficient n).integrand_memLp_energy
  have hLeft : forall n, ProcessHasLeftLimits
      (completedMartingaleCadlagCoordinate schedule hSourceLeft
        coefficient n) := by
    intro n
    exact finiteHorizonMartingaleIntegralCadlagProcess_hasLeftLimits
      schedule.usualConditions (schedule.quadraticKernel n)
      (schedule.martingale n)
      (schedule.sourcePrefix n).martingalePart_isRightContinuous
      (hSourceLeft n) (schedule.terminal_memLp n)
      (Function.uncurry (coefficient n).integrand)
      (coefficient n).integrand_isStronglyPredictable
      (coefficient n).integrand_memLp_energy
  obtain ⟨M, hMAdapted, hMLocal, hMRight, hMLeft, hMStopped⟩ :=
    CompatibleLocalMartingaleGluing.exists_cadlag_localMartingale
      schedule.usualConditions schedule.isLocalizingSequence
      hMartingale hRight hLeft
      (completedMartingaleCadlagCoordinates_compatible schedule
        hSourceLeft coefficient hCoefficient)
  exact ⟨M, hMAdapted, hMLocal, hMRight, hMLeft, fun n =>
    (hMStopped n).trans
      (completedMartingaleCadlagCoordinate_indistinguishable_stopped
        schedule hSourceLeft coefficient n).symm⟩

omit [F.IsRightContinuous] in
/-- Predictably restricted càdlàg completed coordinates glue to one
càdlàg local martingale. -/
theorem ScheduleGraphRepresentation.exists_restrictedCadlagMartingalePart
    {schedule : LocalCompletedM2ASchedule G}
    {H : SIntegrableStrategy D}
    (representation : ScheduleGraphRepresentation schedule H)
    (hSourceLeft : forall n,
      ProcessHasLeftLimits (schedule.sourcePrefix n).martingalePart)
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B) :
    exists M : Process Omega,
      StronglyAdapted F M /\
        LocalMartingale M F mu /\
        (forall omega t, ContinuousWithinAt (M · omega) (Ici t) t) /\
        ProcessHasLeftLimits M /\
        forall n, ProcessIndistinguishable mu
          (MeasureTheory.stoppedProcess M (schedule.localizer n))
          (completedMartingaleCadlagCoordinate schedule hSourceLeft
            (fun k => (representation.coefficient k
              ).restrictPredictable B hB) n) := by
  apply exists_completedCadlagMartingalePart schedule hSourceLeft
    (fun n => (representation.coefficient n).restrictPredictable B hB)
    (f := B.indicator (Function.uncurry H.integrand))
  intro n
  change B.indicator (representation.coefficient n).coefficient = _
  rw [representation.coefficient_eq n]

end LocalCompletedM2A

end FTAPTheorem42
