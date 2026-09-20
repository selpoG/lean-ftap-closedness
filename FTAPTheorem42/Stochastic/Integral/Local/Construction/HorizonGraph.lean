/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedM2AStopping
import FTAPTheorem42.Stochastic.Integral.Local.Construction.GainGluing
import FTAPTheorem42.Stochastic.Integral.Local.Construction.Realization

/-!
# Deterministic-horizon graph bridge for a completed local schedule

The common-schedule gain glue is stable under a deterministic horizon stop.
The coefficient is predictably restricted to `(0,T]`, and the completed
stopping locality theorem transports the coordinate gain identity.  This
module only constructs a finite-horizon `GraphWitness`; it does not assert
terminal convergence or actuality for an arbitrary local strategy.
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

omit [F.IsRightContinuous] in
/-- Restrict every coordinate of a common schedule to one positive
deterministic horizon and obtain a graph witness for the stopped local
strategy. -/
noncomputable def deterministicallyStoppedGraphWitness
    (schedule : LocalCompletedM2ASchedule G)
    (coefficient : forall n, FiniteHorizonM2ACoefficient
      (schedule.variationBridge n) (schedule.quadraticKernel n))
    {f : NNReal × Omega -> Real}
    (hCoefficient : forall n, (coefficient n).coefficient = f)
    (H : LocallySIntegrableStrategy D)
    (hHIntegrand : H.integrand = Function.curry f)
    (hHGain : forall n, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess H.stochasticIntegral
        (schedule.localizer n))
      (finiteHorizonCompletedM2AGain schedule.usualConditions
        (schedule.horizon n) (schedule.quadraticKernel n)
        (schedule.variationBridge n) (schedule.martingale n)
        (schedule.terminal_memLp n) (coefficient n)))
    (T : NNReal) (hT : 0 < T) :
    GraphWitness G (H.deterministicallyStopped T hT) := by
  let tauT : Omega -> WithTop NNReal := fun _ => (T : WithTop NNReal)
  let B : Set (NNReal × Omega) :=
    stochasticIntervalIocZeroTop tauT
  let hB : MeasurableSet[F.predictable] B :=
    IsStoppingTime.measurableSet_stochasticIntervalIocZeroTop
      (isStoppingTime_const F T)
  have hB_eq : B = stochasticIntervalIocZero (fun _ : Omega => T) := by
    ext point
    rcases point with ⟨t, omega⟩
    change ((t, omega) ∈ stochasticIntervalIocZeroTop tauT) ↔
      (t, omega) ∈ stochasticIntervalIocZero (fun _ : Omega => T)
    rw [mem_stochasticIntervalIocZeroTop_iff,
      mem_stochasticIntervalIocZero_iff]
    dsimp only [tauT]
    constructor
    · rintro ⟨ht, hTt⟩
      exact ⟨ht, WithTop.coe_le_coe.mp hTt⟩
    · rintro ⟨ht, hTt⟩
      exact ⟨ht, WithTop.coe_le_coe.mpr hTt⟩
  let coefficientT := fun n =>
    (coefficient n).restrictPredictable B hB
  have hCoefficientT : forall n,
      (coefficientT n).coefficient =
        Function.uncurry (H.deterministicallyStopped T hT).integrand := by
    intro n
    change B.indicator (coefficient n).coefficient =
      Function.uncurry (H.deterministicallyStopped T hT).integrand
    rw [hCoefficient n]
    change B.indicator f =
      Function.uncurry (PredictableProcess.restrict
        (stochasticIntervalIocZero (fun _ : Omega => T)) H.integrand)
    rw [hHIntegrand]
    rw [hB_eq]
    rfl
  have hGainT : forall n, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess
        (H.deterministicallyStopped T hT).stochasticIntegral
        (schedule.localizer n))
      (finiteHorizonCompletedM2AGain schedule.usualConditions
        (schedule.horizon n) (schedule.quadraticKernel n)
        (schedule.variationBridge n) (schedule.martingale n)
        (schedule.terminal_memLp n) (coefficientT n)) := by
    intro n
    have hTauT : IsStoppingTime F tauT := isStoppingTime_const F T
    have hStopLocal : ProcessIndistinguishable mu
        (MeasureTheory.stoppedProcess
          (H.deterministicallyStopped T hT).stochasticIntegral
          (schedule.localizer n))
        (MeasureTheory.stoppedProcess
          (MeasureTheory.stoppedProcess H.stochasticIntegral tauT)
            (schedule.localizer n)) := by
      filter_upwards with omega
      intro t
      rfl
    have hStopComm : ProcessIndistinguishable mu
        (MeasureTheory.stoppedProcess
          (MeasureTheory.stoppedProcess H.stochasticIntegral tauT)
            (schedule.localizer n))
        (MeasureTheory.stoppedProcess
          (MeasureTheory.stoppedProcess H.stochasticIntegral
            (schedule.localizer n)) tauT) := by
      filter_upwards with omega
      intro t
      rw [MeasureTheory.stoppedProcess_stoppedProcess']
      rw [MeasureTheory.stoppedProcess_stoppedProcess']
      congr 1
      funext omega'
      exact min_comm (schedule.localizer n omega') (tauT omega')
    have hCompleted :=
      finiteHorizonCompletedM2AGain_restrict_stochasticIntervalTop
        schedule.usualConditions (schedule.quadraticKernel n)
        (schedule.variationBridge n) (schedule.martingale n)
        (schedule.terminal_memLp n) (coefficient n) tauT hTauT
    exact hStopLocal.trans <|
      hStopComm.trans <|
        (hHGain n).stoppedProcess tauT |>.trans hCompleted.symm
  let witness : GraphWitness G
      (H.deterministicallyStopped T hT) := {
    schedule := schedule
    coefficient := coefficientT
    coefficient_eq := hCoefficientT
    stoppedGain_eq := hGainT }
  exact witness

omit [F.IsRightContinuous] in
/-- The graph-witness producer immediately supplies the realization
predicate of the intrinsic local-completed carrier. -/
theorem deterministicallyStoppedGraphWitness_isRealized
    (schedule : LocalCompletedM2ASchedule G)
    (coefficient : forall n, FiniteHorizonM2ACoefficient
      (schedule.variationBridge n) (schedule.quadraticKernel n))
    {f : NNReal × Omega -> Real}
    (hCoefficient : forall n, (coefficient n).coefficient = f)
    (H : LocallySIntegrableStrategy D)
    (hHIntegrand : H.integrand = Function.curry f)
    (hHGain : forall n, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess H.stochasticIntegral
        (schedule.localizer n))
      (finiteHorizonCompletedM2AGain schedule.usualConditions
        (schedule.horizon n) (schedule.quadraticKernel n)
        (schedule.variationBridge n) (schedule.martingale n)
        (schedule.terminal_memLp n) (coefficient n)))
    (T : NNReal) (hT : 0 < T) :
    (realizationModel G).IsRealized
      (H.deterministicallyStopped T hT) := by
  exact ⟨deterministicallyStoppedGraphWitness schedule coefficient
    hCoefficient H hHIntegrand hHGain T hT⟩

omit [F.IsRightContinuous] in
/-- A global graph supplies all deterministic stops on its own schedule.
No raw stopping calculus is needed to pass to the local carrier. -/
noncomputable def GraphWitness.toActualLocal
    {H : SIntegrableStrategy D} (w : GraphWitness G H) :
    ActualLocallySIntegrableStrategy (realizationModel G) where
  val := H.toLocally
  deterministicallyStopped_isRealized := fun T hT =>
    deterministicallyStoppedGraphWitness_isRealized w.schedule w.coefficient
      w.coefficient_eq H.toLocally rfl w.stoppedGain_eq T hT

omit [F.IsRightContinuous] in
/-- The common-schedule producer can be selected once, independently of the
deterministic horizon.  Every positive deterministic stop of the selected
local strategy is then realized by the preceding graph-witness construction;
the original localizer-wise gain semantics is retained as data. -/
theorem exists_actualLocal_of_commonSchedule
    (schedule : LocalCompletedM2ASchedule G)
    (coefficient : forall n, FiniteHorizonM2ACoefficient
      (schedule.variationBridge n) (schedule.quadraticKernel n))
    {f : NNReal × Omega -> Real}
    (hCoefficient : forall n, (coefficient n).coefficient = f) :
    ∃ actualLocal : ActualLocallySIntegrableStrategy (realizationModel G),
      actualLocal.val.integrand = Function.curry f ∧
      (∀ n, ProcessIndistinguishable mu
        (MeasureTheory.stoppedProcess actualLocal.val.stochasticIntegral
          (schedule.localizer n))
        (finiteHorizonCompletedM2AGain schedule.usualConditions
          (schedule.horizon n) (schedule.quadraticKernel n)
          (schedule.variationBridge n) (schedule.martingale n)
          (schedule.terminal_memLp n) (coefficient n))) ∧
      (∀ n, ProcessIndistinguishable mu
        (MeasureTheory.stoppedProcess actualLocal.val.martingalePart
          (schedule.localizer n))
        (finiteHorizonCompletedMartingalePart schedule.usualConditions
          (schedule.horizon n) (schedule.quadraticKernel n)
          (schedule.martingale n) (schedule.terminal_memLp n) (coefficient n))) ∧
      (∀ n, ProcessIndistinguishable mu
        (MeasureTheory.stoppedProcess actualLocal.val.finiteVariationPart
          (schedule.localizer n))
        (finiteHorizonCompletedFiniteVariationPart schedule.usualConditions
          (schedule.horizon n) (schedule.quadraticKernel n)
          (schedule.variationBridge n) (coefficient n))) := by
  obtain ⟨H, hHIntegrand, hHGain, hHMartingale, hHFiniteVariation⟩ :=
    exists_completedM2AGainStrategy_with_integrand schedule coefficient hCoefficient
  let actualLocal : ActualLocallySIntegrableStrategy (realizationModel G) := {
    val := H
    deterministicallyStopped_isRealized := fun T hT => by
      exact deterministicallyStoppedGraphWitness_isRealized
        schedule coefficient hCoefficient H hHIntegrand hHGain T hT }
  refine ⟨actualLocal, ?_, ?_, ?_, ?_⟩
  · simpa only [actualLocal] using hHIntegrand
  · simpa only [actualLocal] using hHGain
  · simpa only [actualLocal] using hHMartingale
  · simpa only [actualLocal] using hHFiniteVariation

end LocalCompletedM2A

end FTAPTheorem42
