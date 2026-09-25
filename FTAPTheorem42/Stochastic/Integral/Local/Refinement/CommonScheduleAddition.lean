/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedM2AAdditivity
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedM2AAlgebra
import FTAPTheorem42.Stochastic.Integral.Local.Construction.Realization
import FTAPTheorem42.Stochastic.DS.Lemma47.RightContinuousLocalizer
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableActualConvexCombination

/-!
# Addition on a common local-completed schedule

The completed operators are additive once two graphs are represented on the
same exhaustive schedule.  This module packages that data-level fact and
constructs the resulting actual graph in the intrinsic carrier.

It deliberately does not claim that two arbitrary strategy-dependent
schedules already have a common refinement.  Such a refinement must also
transport both coefficient memberships and both completed graph identities;
mere pointwise minima of the stopping times do not provide those semantic
facts.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace LocalCompletedM2A

open SIntegrableFiniteVariationBridge

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : LocallySIntegrableStrategy D}

/-- Representation of one graph on a prescribed local-completed schedule. -/
structure ScheduleGraphRepresentation
    (schedule : LocalCompletedM2ASchedule G)
    (H : SIntegrableStrategy D) where
  coefficient : forall n, FiniteHorizonM2ACoefficient
    (schedule.variationBridge n) (schedule.quadraticKernel n)
  coefficient_eq : forall n,
    (coefficient n).coefficient = Function.uncurry H.integrand
  stoppedGain_eq : forall n, ProcessIndistinguishable mu
    (MeasureTheory.stoppedProcess H.stochasticIntegral (schedule.localizer n))
    (finiteHorizonCompletedM2AGain schedule.usualConditions
      (schedule.horizon n) (schedule.quadraticKernel n)
        (schedule.variationBridge n) (schedule.martingale n)
          (schedule.terminal_memLp n) (coefficient n))

/-- Forget the fixed-schedule indexing and obtain an intrinsic graph
witness. -/
def ScheduleGraphRepresentation.toGraphWitness
    {schedule : LocalCompletedM2ASchedule G}
    {H : SIntegrableStrategy D}
    (representation : ScheduleGraphRepresentation schedule H) :
    GraphWitness G H where
  schedule := schedule
  coefficient := representation.coefficient
  coefficient_eq := representation.coefficient_eq
  stoppedGain_eq := representation.stoppedGain_eq

/-- Fix the schedule carried by an intrinsic graph witness and view the
graph on that prescribed schedule. -/
def GraphWitness.toScheduleGraphRepresentation
    {G : LocallySIntegrableStrategy D}
    {H : SIntegrableStrategy D}
    (witness : GraphWitness G H) :
    ScheduleGraphRepresentation witness.schedule H where
  coefficient := witness.coefficient
  coefficient_eq := witness.coefficient_eq
  stoppedGain_eq := witness.stoppedGain_eq

/-- Addition of two graph representations over exactly the same completed
source schedule. -/
def ScheduleGraphRepresentation.add
    {schedule : LocalCompletedM2ASchedule G}
    {H K : SIntegrableStrategy D}
    (hH : ScheduleGraphRepresentation schedule H)
    (hK : ScheduleGraphRepresentation schedule K) :
    ScheduleGraphRepresentation schedule (H.add_of_rightContinuous K) where
  coefficient := fun n => (hH.coefficient n).add (hK.coefficient n)
  coefficient_eq := fun n => by
    change (hH.coefficient n).coefficient + (hK.coefficient n).coefficient =
      Function.uncurry (H.add_of_rightContinuous K).integrand
    rw [hH.coefficient_eq n, hK.coefficient_eq n]
    rfl
  stoppedGain_eq := fun n => by
    have hStopped : ProcessIndistinguishable mu
        (MeasureTheory.stoppedProcess
          (H.add_of_rightContinuous K).stochasticIntegral
            (schedule.localizer n))
        (MeasureTheory.stoppedProcess H.stochasticIntegral
            (schedule.localizer n) +
          MeasureTheory.stoppedProcess K.stochasticIntegral
            (schedule.localizer n)) := by
      filter_upwards with omega
      intro t
      rfl
    have hOld := (hH.stoppedGain_eq n).add (hK.stoppedGain_eq n)
    have hCompleted := finiteHorizonCompletedM2AGain_add
      schedule.usualConditions (schedule.quadraticKernel n)
        (schedule.variationBridge n) (schedule.martingale n)
          (schedule.terminal_memLp n) (hH.coefficient n) (hK.coefficient n)
    exact hStopped.trans (hOld.trans hCompleted.symm)

/-- Two raw graphs represented on one schedule have an actual componentwise
sum in the intrinsic realization carrier. -/
noncomputable def actualAddOfCommonSchedule
    {schedule : LocalCompletedM2ASchedule G}
    {H K : SIntegrableStrategy D}
    (hH : ScheduleGraphRepresentation schedule H)
    (hK : ScheduleGraphRepresentation schedule K) :
    ActualSIntegrableStrategy (realizationModel G) :=
  ⟨H.add_of_rightContinuous K, ⟨(hH.add hK).toGraphWitness⟩⟩

end LocalCompletedM2A

end FTAPTheorem42
