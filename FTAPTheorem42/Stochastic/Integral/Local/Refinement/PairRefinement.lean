/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Local.Refinement.PairMartingale
import FTAPTheorem42.Stochastic.Integral.Local.Refinement.CommonScheduleAddition

/-!
# Completed finite-variation agreement on pairwise schedules

The martingale-energy transport supplies genuine left and right coefficients
on the pair-refined source.  This module consumes the common finite-variation
transport theorem to identify their completed finite-variation components
with the corresponding old components stopped at the common localizer.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega]

namespace LocalCompletedM2A

open SIntegrableFiniteVariationBridge

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : LocallySIntegrableStrategy D}

/-- The pair-refined completed finite-variation integral of a left
coefficient is the old left integral stopped at the common localizer. -/
theorem pairScheduleCompletedFiniteVariationPart_left
    (left right : LocalCompletedM2ASchedule G) (n : Nat)
    (c : FiniteHorizonM2ACoefficient
      (left.variationBridge n) (left.quadraticKernel n)) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedFiniteVariationPart left.usualConditions
        (pairScheduleHorizon left right n)
        (pairScheduleQuadraticKernel left right n)
        (pairScheduleFiniteVariationBridge left right n)
        (pairScheduleCoefficientLeft left right n c))
      (MeasureTheory.stoppedProcess
        (finiteHorizonCompletedFiniteVariationPart left.usualConditions
          (left.horizon n) (left.quadraticKernel n)
          (left.variationBridge n) c)
        (pairScheduleLocalizer left right n)) := by
  exact pairScheduleCompletedFiniteVariationPart_of_schedule
    left right left n (pairScheduleLocalizer_le_left left right n)
    (pairScheduleSourcePrefix_finiteVariationPart_left left right n) c
    (pairScheduleCoefficientLeft left right n c) rfl

/-- The pair-refined completed finite-variation integral of a right
coefficient is the old right integral stopped at the common localizer. -/
theorem pairScheduleCompletedFiniteVariationPart_right
    (left right : LocalCompletedM2ASchedule G) (n : Nat)
    (c : FiniteHorizonM2ACoefficient
      (right.variationBridge n) (right.quadraticKernel n)) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedFiniteVariationPart left.usualConditions
        (pairScheduleHorizon left right n)
        (pairScheduleQuadraticKernel left right n)
        (pairScheduleFiniteVariationBridge left right n)
        (pairScheduleCoefficientRight left right n c))
      (MeasureTheory.stoppedProcess
        (finiteHorizonCompletedFiniteVariationPart right.usualConditions
          (right.horizon n) (right.quadraticKernel n)
          (right.variationBridge n) c)
        (pairScheduleLocalizer left right n)) := by
  exact pairScheduleCompletedFiniteVariationPart_of_schedule
    left right right n (pairScheduleLocalizer_le_right left right n)
    (pairScheduleSourcePrefix_finiteVariationPart_right left right n) c
    (pairScheduleCoefficientRight left right n c) rfl

/-!
## Pairwise common refinement of local completed graph schedules

Two graph representations may initially use different exhaustive schedules.
The pointwise minimum of their localizers, together with the concrete common
finite-variation bridge and martingale energy kernel, carries both old
coefficients and both completed graph identities.  Thus both graphs obtain
representations on one genuine local-completed schedule.

The construction is semantic rather than merely set-theoretic: the completed
martingale and finite-variation operators on the refined schedule are proved
to be the corresponding old operators stopped at the common localizer.
-/

/-- The concrete schedule refining two old local-completed schedules. -/
noncomputable def pairCommonSchedule
    (left right : LocalCompletedM2ASchedule G) :
    LocalCompletedM2ASchedule G :=
  (pairCommonSourceScheduleSkeleton left right
    ).toLocalCompletedM2ASchedule
      (fun n => pairScheduleFiniteVariationBridge left right n)
      (fun n => pairScheduleQuadraticKernel left right n)

private theorem stoppedCompletedGain_eq_of_left
    (left right : LocalCompletedM2ASchedule G) (n : Nat)
    (c : FiniteHorizonM2ACoefficient
      (left.variationBridge n) (left.quadraticKernel n)) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedM2AGain left.usualConditions
        (pairScheduleHorizon left right n)
        (pairScheduleQuadraticKernel left right n)
        (pairScheduleFiniteVariationBridge left right n)
        (pairScheduleSourcePrefix_martingale left right n)
        (pairScheduleSourcePrefix_terminal_memLp left right n)
        (pairScheduleCoefficientLeft left right n c))
      (MeasureTheory.stoppedProcess
        (finiteHorizonCompletedM2AGain left.usualConditions
          (left.horizon n) (left.quadraticKernel n)
          (left.variationBridge n) (left.martingale n)
          (left.terminal_memLp n) c)
        (pairScheduleLocalizer left right n)) := by
  have hM := pairScheduleCompletedMartingalePart_left left right n c
  have hA := pairScheduleCompletedFiniteVariationPart_left left right n c
  filter_upwards [hM, hA] with omega hMOmega hAOmega
  intro t
  exact congrArg₂ (fun x y : Real => x + y) (hMOmega t) (hAOmega t)

private theorem stoppedCompletedGain_eq_of_right
    (left right : LocalCompletedM2ASchedule G) (n : Nat)
    (c : FiniteHorizonM2ACoefficient
      (right.variationBridge n) (right.quadraticKernel n)) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedM2AGain left.usualConditions
        (pairScheduleHorizon left right n)
        (pairScheduleQuadraticKernel left right n)
        (pairScheduleFiniteVariationBridge left right n)
        (pairScheduleSourcePrefix_martingale left right n)
        (pairScheduleSourcePrefix_terminal_memLp left right n)
        (pairScheduleCoefficientRight left right n c))
      (MeasureTheory.stoppedProcess
        (finiteHorizonCompletedM2AGain right.usualConditions
          (right.horizon n) (right.quadraticKernel n)
          (right.variationBridge n) (right.martingale n)
          (right.terminal_memLp n) c)
        (pairScheduleLocalizer left right n)) := by
  have hM := pairScheduleCompletedMartingalePart_right left right n c
  have hA := pairScheduleCompletedFiniteVariationPart_right left right n c
  filter_upwards [hM, hA] with omega hMOmega hAOmega
  intro t
  exact congrArg₂ (fun x y : Real => x + y) (hMOmega t) (hAOmega t)

/-- A graph represented on the left schedule is represented on the pairwise
common refinement. -/
noncomputable def ScheduleGraphRepresentation.pairRefineLeft
    {left right : LocalCompletedM2ASchedule G}
    {H : SIntegrableStrategy D}
    (representation : ScheduleGraphRepresentation left H) :
    ScheduleGraphRepresentation (pairCommonSchedule left right) H where
  coefficient := fun n =>
    pairScheduleCoefficientLeft left right n (representation.coefficient n)
  coefficient_eq := fun n => representation.coefficient_eq n
  stoppedGain_eq := fun n => by
    have hOld := (representation.stoppedGain_eq n).stoppedProcess
      (pairScheduleLocalizer left right n)
    rw [MeasureTheory.stoppedProcess_stoppedProcess_of_le_right
      (pairScheduleLocalizer_le_left left right n)] at hOld
    exact hOld.trans
      (stoppedCompletedGain_eq_of_left left right n
        (representation.coefficient n)).symm

/-- A graph represented on the right schedule is represented on the pairwise
common refinement. -/
noncomputable def ScheduleGraphRepresentation.pairRefineRight
    {left right : LocalCompletedM2ASchedule G}
    {H : SIntegrableStrategy D}
    (representation : ScheduleGraphRepresentation right H) :
    ScheduleGraphRepresentation (pairCommonSchedule left right) H where
  coefficient := fun n =>
    pairScheduleCoefficientRight left right n (representation.coefficient n)
  coefficient_eq := fun n => representation.coefficient_eq n
  stoppedGain_eq := fun n => by
    have hOld := (representation.stoppedGain_eq n).stoppedProcess
      (pairScheduleLocalizer left right n)
    rw [MeasureTheory.stoppedProcess_stoppedProcess_of_le_right
      (pairScheduleLocalizer_le_right left right n)] at hOld
    exact hOld.trans
      (stoppedCompletedGain_eq_of_right left right n
        (representation.coefficient n)).symm

/-- Any two locally completed graph representations have one common
schedule on which both graph identities hold. -/
theorem exists_pairCommonScheduleRepresentations
    {left right : LocalCompletedM2ASchedule G}
    {H K : SIntegrableStrategy D}
    (hH : ScheduleGraphRepresentation left H)
    (hK : ScheduleGraphRepresentation right K) :
    exists schedule : LocalCompletedM2ASchedule G,
      Nonempty (ScheduleGraphRepresentation schedule H) /\
        Nonempty (ScheduleGraphRepresentation schedule K) := by
  exact ⟨pairCommonSchedule left right,
    ⟨hH.pairRefineLeft⟩, ⟨hK.pairRefineRight⟩⟩

end LocalCompletedM2A

end FTAPTheorem42
