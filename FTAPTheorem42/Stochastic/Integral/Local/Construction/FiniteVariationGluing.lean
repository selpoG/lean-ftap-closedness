/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.FiniteVariation.CompatibleLocalFiniteVariationGluing
import FTAPTheorem42.Stochastic.Integral.Local.Refinement.PairRefinement
import FTAPTheorem42.Stochastic.Integral.Local.Construction.BoundedCoordinateSemantics

/-!
# Gluing local completed finite-variation coordinates

One exhaustive local-completed schedule carries a finite-horizon completed
finite-variation process at every coordinate.  Pairwise tail refinement puts
two coordinates on one common source and bridge.  Equality of their raw
coefficients then gives equality of the common completed processes, while the
pair transport identities return the two original processes stopped at the
minimum localizer.  This is the overlap law consumed by the generic local
finite-variation gluing theorem.
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

/-- The completed finite-variation integral of one schedule coefficient. -/
noncomputable def completedFiniteVariationCoordinate
    (schedule : LocalCompletedM2ASchedule G)
    (coefficient : forall n, FiniteHorizonM2ACoefficient
      (schedule.variationBridge n) (schedule.quadraticKernel n))
    (n : Nat) : Process Omega :=
  finiteHorizonCompletedFiniteVariationPart schedule.usualConditions
    (schedule.horizon n) (schedule.quadraticKernel n)
      (schedule.variationBridge n) (coefficient n)

omit [F.IsRightContinuous] [SigmaFiniteFiltration mu F] in
private theorem completedFiniteVariationPart_indistinguishable_of_coefficient_eq
    {P : SIntegrableStrategy D} {T : NNReal}
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data F mu P.martingalePart T)
    (E : SIntegrableFiniteVariationBridge P)
    (c d : FiniteHorizonM2ACoefficient E Q)
    (hcd : c.coefficient = d.coefficient) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedFiniteVariationPart hUsual T Q E c)
      (finiteHorizonCompletedFiniteVariationPart hUsual T Q E d) := by
  have hC := finiteHorizonCompletedFiniteVariationPart_indistinguishable
    hUsual E Q c
  have hD := finiteHorizonCompletedFiniteVariationPart_indistinguishable
    hUsual E Q d
  have hIntegrand : c.integrand = d.integrand := by
    funext t omega
    unfold FiniteHorizonM2ACoefficient.integrand
    unfold finiteHorizonCoefficient
    rw [hcd]
  have hRaw : ProcessIndistinguishable mu
      (finiteVariationIntegralProcess E c.integrand)
      (finiteVariationIntegralProcess E d.integrand) := by
    rw [hIntegrand]
    exact ProcessIndistinguishable.refl mu _
  exact hC.trans (hRaw.trans hD.symm)

omit [F.IsRightContinuous] in
/-- A common raw coefficient on an exhaustive completed schedule yields
compatible completed finite-variation coordinates. -/
theorem completedFiniteVariationCoordinates_compatible
    (schedule : LocalCompletedM2ASchedule G)
    (coefficient : forall n, FiniteHorizonM2ACoefficient
      (schedule.variationBridge n) (schedule.quadraticKernel n))
    {f : NNReal × Omega -> Real}
    (hCoefficient : forall n, (coefficient n).coefficient = f)
    (n m : Nat) :
    ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess
        (completedFiniteVariationCoordinate schedule coefficient n)
        (fun omega => min (schedule.localizer n omega)
          (schedule.localizer m omega)))
      (MeasureTheory.stoppedProcess
        (completedFiniteVariationCoordinate schedule coefficient m)
        (fun omega => min (schedule.localizer n omega)
          (schedule.localizer m omega))) := by
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
      (finiteHorizonCompletedFiniteVariationPart left.usualConditions
        (pairScheduleHorizon left right 0)
        (pairScheduleQuadraticKernel left right 0)
        (pairScheduleFiniteVariationBridge left right 0) pc)
      (finiteHorizonCompletedFiniteVariationPart left.usualConditions
        (pairScheduleHorizon left right 0)
        (pairScheduleQuadraticKernel left right 0)
        (pairScheduleFiniteVariationBridge left right 0) pd) :=
    completedFiniteVariationPart_indistinguishable_of_coefficient_eq
      left.usualConditions (pairScheduleQuadraticKernel left right 0)
      (pairScheduleFiniteVariationBridge left right 0) pc pd hpcd
  have hLeft := pairScheduleCompletedFiniteVariationPart_left left right 0 c
  have hRight := pairScheduleCompletedFiniteVariationPart_right left right 0 d
  have hResult := hLeft.symm.trans (hPair.trans hRight)
  change ProcessIndistinguishable mu
    (MeasureTheory.stoppedProcess
      (completedFiniteVariationCoordinate schedule coefficient n)
      (fun omega => min (schedule.localizer n omega)
        (schedule.localizer m omega)))
    (MeasureTheory.stoppedProcess
      (completedFiniteVariationCoordinate schedule coefficient m)
      (fun omega => min (schedule.localizer n omega)
        (schedule.localizer m omega))) at hResult
  exact hResult

/-! The preceding coordinate law supplies the nontrivial input to the global
finite-variation gluing primitive. -/
omit [F.IsRightContinuous] in
theorem exists_completedFiniteVariationCoordinatesGlue
    (schedule : LocalCompletedM2ASchedule G)
    (coefficient : forall n, FiniteHorizonM2ACoefficient
      (schedule.variationBridge n) (schedule.quadraticKernel n))
    {f : NNReal × Omega -> Real}
    (hCoefficient : forall n, (coefficient n).coefficient = f) :
    ∃ A : Process Omega,
      IsStronglyPredictable F A ∧
      (∀ omega t, ContinuousWithinAt (A · omega) (Ici t) t) ∧
      (∀ omega, LocallyBoundedVariationOn (A · omega) Set.univ) ∧
      ∀ n, ProcessIndistinguishable mu
        (MeasureTheory.stoppedProcess A (schedule.localizer n))
        (MeasureTheory.stoppedProcess
          (completedFiniteVariationCoordinate schedule coefficient n)
          (schedule.localizer n)) := by
  let A : Nat → Process Omega := completedFiniteVariationCoordinate schedule coefficient
  obtain ⟨A', hA'Predictable, hA'Right, hA'Variation, hA'Stop⟩ :=
    CompatibleLocalFiniteVariationGluing.exists_predictable_rightContinuous_locallyBoundedVariation
      schedule.usualConditions schedule.isLocalizingSequence
      (fun n => by
        exact completedFiniteVariationProcess_isStronglyPredictable _ _ _ _ _)
      (fun n => by
        exact completedFiniteVariationProcess_rightContinuous _ _ _ _ _)
      (fun n => by
        exact completedFiniteVariationProcess_isBoundedVariation _ _ _ _ _)
      (fun n m => completedFiniteVariationCoordinates_compatible schedule coefficient
        hCoefficient n m)
  exact ⟨A', hA'Predictable, hA'Right, hA'Variation, hA'Stop⟩

end LocalCompletedM2A

end FTAPTheorem42
