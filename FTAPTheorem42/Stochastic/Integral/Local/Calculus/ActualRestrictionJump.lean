/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedM2ARestrictionJump
import FTAPTheorem42.Stochastic.Integral.Local.Calculus.ActualRestrictionCadlag

/-!
# Jump semantics of intrinsic predictable restriction

The actual-first predictable restriction is assembled from completed local
coordinates, rather than from the underdetermined raw restriction record.
On the self-pair refinement of an actual graph witness, both the original
gain and the restricted gain are represented by càdlàg finite-horizon
completed graphs.  Their finite-horizon jump identity therefore globalizes
along the exhaustive schedule.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace LocalCompletedM2A

open SIntegrableFiniteVariationBridge

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  [F.IsRightContinuous]
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : LocallySIntegrableStrategy D}

/-- The càdlàg actual-first restriction has the same all-time jumps as the
predictable indicator transform of the original gain. -/
theorem actualRestrictPredictableCadlag_stochasticIntegral_leftJump
    (hGLeft : ProcessHasLeftLimits G.martingalePart)
    (H : ActualSIntegrableStrategy (realizationModel G))
    (hHLeft : ProcessHasLeftLimits H.val.stochasticIntegral)
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B) :
    ∀ᵐ omega ∂mu, forall t,
      processLeftJump
          (actualRestrictPredictableCadlag hGLeft H B hB
            ).val.stochasticIntegral t omega =
        predictableRestrictedLeftJump B H.val.stochasticIntegral
          t omega := by
  let witness := actualGraphWitness H
  let oldSchedule := witness.schedule
  let schedule := pairCommonSchedule oldSchedule oldSchedule
  let representation := witness.selfPairRepresentation
  let restrictedWitness :=
    restrictPredictableStrategy_graphWitness H B hB
  let restrictedRepresentation : ScheduleGraphRepresentation schedule
      (actualRestrictPredictable H B hB).val :=
    restrictedWitness.toScheduleGraphRepresentation.pairRefineLeft
  let R := actualRestrictPredictableCadlag hGLeft H B hB
  have hCoefficient (n : Nat) : restrictedRepresentation.coefficient n =
      (representation.coefficient n).restrictPredictable B hB := by
    apply FiniteHorizonM2ACoefficient.ext
    rfl
  have hOriginalCoordinate (n : Nat) : ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess H.val.stochasticIntegral
        (schedule.localizer n))
      (finiteHorizonCompletedM2ACadlagGain schedule.usualConditions
        (schedule.quadraticKernel n) (schedule.variationBridge n)
        (schedule.martingale n)
        (witness.selfPairSchedule_sourceLeft hGLeft n)
        (schedule.terminal_memLp n) (representation.coefficient n)) := by
    exact (representation.stoppedGain_eq n).trans
      (finiteHorizonCompletedM2ACadlagGain_indistinguishable
        schedule.usualConditions (schedule.quadraticKernel n)
        (schedule.variationBridge n) (schedule.martingale n)
        (witness.selfPairSchedule_sourceLeft hGLeft n)
        (schedule.terminal_memLp n) (representation.coefficient n)).symm
  have hRestrictedCoordinate (n : Nat) : ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess R.val.stochasticIntegral
        (schedule.localizer n))
      (finiteHorizonCompletedM2ACadlagGain schedule.usualConditions
        (schedule.quadraticKernel n) (schedule.variationBridge n)
        (schedule.martingale n)
        (witness.selfPairSchedule_sourceLeft hGLeft n)
        (schedule.terminal_memLp n)
        ((representation.coefficient n).restrictPredictable B hB)) := by
    have hVersion :=
      (restrictPredictableCadlagStrategy_gain_indistinguishable hGLeft H B hB).stoppedProcess
        (schedule.localizer n)
    have hGraph := restrictedRepresentation.stoppedGain_eq n
    rw [hCoefficient n] at hGraph
    have hCadlag :=
      finiteHorizonCompletedM2ACadlagGain_indistinguishable
        schedule.usualConditions (schedule.quadraticKernel n)
        (schedule.variationBridge n) (schedule.martingale n)
        (witness.selfPairSchedule_sourceLeft hGLeft n)
        (schedule.terminal_memLp n)
        ((representation.coefficient n).restrictPredictable B hB)
    exact hVersion.symm.trans (hGraph.trans hCadlag.symm)
  have hFiniteHorizon (n : Nat) :=
    finiteHorizonCompletedM2ACadlagGain_restrictPredictable_jump
      schedule.usualConditions (schedule.quadraticKernel n)
      (schedule.variationBridge n) (schedule.martingale n)
      (witness.selfPairSchedule_sourceLeft hGLeft n)
      (schedule.terminal_memLp n) B hB (representation.coefficient n)
  have hOriginalJump : ∀ᵐ omega ∂mu, forall n t,
      processLeftJump
          (MeasureTheory.stoppedProcess H.val.stochasticIntegral
            (schedule.localizer n)) t omega =
        processLeftJump
          (finiteHorizonCompletedM2ACadlagGain schedule.usualConditions
            (schedule.quadraticKernel n) (schedule.variationBridge n)
            (schedule.martingale n)
            (witness.selfPairSchedule_sourceLeft hGLeft n)
            (schedule.terminal_memLp n) (representation.coefficient n))
          t omega := by
    exact eventually_countable_forall.2 fun n =>
      (hOriginalCoordinate n).processLeftJump_eq
  have hRestrictedJump : ∀ᵐ omega ∂mu, forall n t,
      processLeftJump
          (MeasureTheory.stoppedProcess R.val.stochasticIntegral
            (schedule.localizer n)) t omega =
        processLeftJump
          (finiteHorizonCompletedM2ACadlagGain schedule.usualConditions
            (schedule.quadraticKernel n) (schedule.variationBridge n)
            (schedule.martingale n)
            (witness.selfPairSchedule_sourceLeft hGLeft n)
            (schedule.terminal_memLp n)
            ((representation.coefficient n).restrictPredictable B hB))
          t omega := by
    exact eventually_countable_forall.2 fun n =>
      (hRestrictedCoordinate n).processLeftJump_eq
  have hFiniteHorizonJump : ∀ᵐ omega ∂mu, forall n t,
      processLeftJump
          (finiteHorizonCompletedM2ACadlagGain schedule.usualConditions
            (schedule.quadraticKernel n) (schedule.variationBridge n)
            (schedule.martingale n)
            (witness.selfPairSchedule_sourceLeft hGLeft n)
            (schedule.terminal_memLp n)
            ((representation.coefficient n).restrictPredictable B hB))
          t omega =
        predictableRestrictedLeftJump B
          (finiteHorizonCompletedM2ACadlagGain schedule.usualConditions
            (schedule.quadraticKernel n) (schedule.variationBridge n)
            (schedule.martingale n)
            (witness.selfPairSchedule_sourceLeft hGLeft n)
            (schedule.terminal_memLp n) (representation.coefficient n))
          t omega := by
    exact eventually_countable_forall.2 hFiniteHorizon
  filter_upwards [schedule.isLocalizingSequence.tendsto_top,
      hOriginalJump, hRestrictedJump, hFiniteHorizonJump]
      with omega hTop hOriginalOmega hRestrictedOmega hFiniteOmega
  intro t
  rw [WithTop.tendsto_nhds_top_iff] at hTop
  obtain ⟨n, hn⟩ := (hTop t).exists
  have ht : (t : WithTop NNReal) <= schedule.localizer n omega := hn.le
  calc
    processLeftJump R.val.stochasticIntegral t omega =
        processLeftJump
          (MeasureTheory.stoppedProcess R.val.stochasticIntegral
            (schedule.localizer n)) t omega :=
      (processLeftJump_stoppedProcess_eq_of_le R.val.stochasticIntegral
        (actualRestrictPredictableCadlag_stochasticIntegral_hasLeftLimits hGLeft H B hB)
          (schedule.localizer n) t omega ht).symm
    _ = processLeftJump
          (finiteHorizonCompletedM2ACadlagGain schedule.usualConditions
            (schedule.quadraticKernel n) (schedule.variationBridge n)
            (schedule.martingale n)
            (witness.selfPairSchedule_sourceLeft hGLeft n)
            (schedule.terminal_memLp n)
            ((representation.coefficient n).restrictPredictable B hB))
          t omega := hRestrictedOmega n t
    _ = predictableRestrictedLeftJump B
          (finiteHorizonCompletedM2ACadlagGain schedule.usualConditions
            (schedule.quadraticKernel n) (schedule.variationBridge n)
            (schedule.martingale n)
            (witness.selfPairSchedule_sourceLeft hGLeft n)
            (schedule.terminal_memLp n) (representation.coefficient n))
          t omega := hFiniteOmega n t
    _ = predictableRestrictedLeftJump B
          (MeasureTheory.stoppedProcess H.val.stochasticIntegral
            (schedule.localizer n)) t omega := by
      unfold predictableRestrictedLeftJump
      by_cases hBt : (t, omega) ∈ B <;>
        simp [hBt, hOriginalOmega n t]
    _ = predictableRestrictedLeftJump B H.val.stochasticIntegral
          t omega := by
      have hStopped := processLeftJump_stoppedProcess_eq_of_le
        H.val.stochasticIntegral hHLeft (schedule.localizer n) t omega ht
      unfold predictableRestrictedLeftJump
      by_cases hBt : (t, omega) ∈ B <;> simp [hBt, hStopped]

end LocalCompletedM2A

end FTAPTheorem42
