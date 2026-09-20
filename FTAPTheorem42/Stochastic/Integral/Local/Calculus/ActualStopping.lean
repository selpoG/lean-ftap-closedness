/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedM2AStopping
import FTAPTheorem42.Stochastic.Integral.Local.Construction.Realization
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableActualScalarCalculus

/-!
# Actual stopping in the intrinsic local completed carrier

Stopping an intrinsic local-completed graph does not require changing its
exhaustive schedule.  At every coordinate we retain the original localizer
and restrict the common finite-horizon coefficient to the predictable
stochastic interval `(0, tau]`.  Finite-horizon completed stopping locality
then identifies the restricted completed graph with the stopped original
graph.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace LocalCompletedM2A

open SIntegrableFiniteVariationBridge

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}

omit [MeasurableSpace Omega] in
/-- Stopping two processes in the opposite orders gives the same process.
This data-level identity is used without altering the exhaustive schedule of
the local-completed witness. -/
private theorem stoppedProcess_comm
    (X : Process Omega) (tau sigma : Omega -> WithTop NNReal) :
    MeasureTheory.stoppedProcess
        (MeasureTheory.stoppedProcess X tau) sigma =
      MeasureTheory.stoppedProcess
        (MeasureTheory.stoppedProcess X sigma) tau := by
  rw [MeasureTheory.stoppedProcess_stoppedProcess',
    MeasureTheory.stoppedProcess_stoppedProcess']
  congr 1
  funext omega
  exact min_comm _ _

/-- The intrinsic local-completed realization carrier is closed under the
stopping operation supplied by any raw stopping calculus.  The witness uses
the same exhaustive schedule as the original graph; only its coordinate
coefficients are restricted to `(0, tau]`. -/
theorem actualStoppingCalculus
    (G : LocallySIntegrableStrategy D)
    (C : SIntegrableProcessStoppingCalculus D) :
    SIntegrableActualStoppingCalculus (realizationModel G) C := by
  refine { stopAtTop_isRealized := ?_ }
  · intro tau hTau H
    obtain ⟨witness⟩ := H.property
    let B := stochasticIntervalIocZeroTop tau
    let hB : MeasurableSet[F.predictable] B :=
      IsStoppingTime.measurableSet_stochasticIntervalIocZeroTop hTau
    refine ⟨{
      schedule := witness.schedule
      coefficient := fun n =>
        (witness.coefficient n).restrictPredictable B hB
      coefficient_eq := fun n => ?_
      stoppedGain_eq := fun n => ?_ }⟩
    · rw [FiniteHorizonM2ACoefficient.restrictPredictable_coefficient,
        witness.coefficient_eq n]
      rw [C.stopAtTop_integrand]
      rfl
    · have hStoppedRaw :=
        (C.stochasticIntegral_stopAtTop tau hTau H.val).stoppedProcess
          (witness.schedule.localizer n)
      have hCommute : ProcessIndistinguishable mu
          (MeasureTheory.stoppedProcess
            (MeasureTheory.stoppedProcess H.val.stochasticIntegral tau)
            (witness.schedule.localizer n))
          (MeasureTheory.stoppedProcess
            (MeasureTheory.stoppedProcess H.val.stochasticIntegral
              (witness.schedule.localizer n)) tau) := by
        rw [stoppedProcess_comm]
        exact ProcessIndistinguishable.refl mu _
      have hOldStopped :=
        (witness.stoppedGain_eq n).stoppedProcess tau
      have hCompleted :=
        finiteHorizonCompletedM2AGain_restrict_stochasticIntervalTop
          witness.schedule.usualConditions
          (witness.schedule.quadraticKernel n)
          (witness.schedule.variationBridge n)
          (witness.schedule.martingale n)
          (witness.schedule.terminal_memLp n)
          (witness.coefficient n) tau hTau
      exact hStoppedRaw.trans
        (hCommute.trans (hOldStopped.trans hCompleted.symm))

end LocalCompletedM2A

end FTAPTheorem42
