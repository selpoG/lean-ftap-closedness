/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Local.Construction.MartingaleGluing
import FTAPTheorem42.Stochastic.Integral.Local.Construction.FiniteVariationGluing

/-!
# Gluing a local completed M² ⊕ A¹ gain

The martingale and finite-variation coordinate gluing theorems can be
consumed together on one completed schedule.  A common raw coefficient gives
one predictable integrand, while the two global component processes give a
locally S-integrable strategy whose gain is their sum.  The construction only
asserts local bounded variation for the finite-variation component; it does
not assert a global finite-variation bound, terminal convergence, or an
actual graph witness.
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

omit [F.IsRightContinuous] in
/-- The source-prefix identity implies that the prefix finite-variation path
is itself unchanged by the schedule localizer.  The right-hand side of the
schedule identity is already a stopped process, so applying the stop
operation once more and using its idempotence gives the self-stop law. -/
theorem sourcePrefix_finiteVariationPart_indistinguishable_stopped
    (schedule : LocalCompletedM2ASchedule G) (n : Nat) :
    ProcessIndistinguishable mu
      (schedule.sourcePrefix n).finiteVariationPart
      (MeasureTheory.stoppedProcess
        (schedule.sourcePrefix n).finiteVariationPart
        (schedule.localizer n)) := by
  have hSource := schedule.sourcePrefix_finiteVariationPart n
  have hSourceStopped := hSource.stoppedProcess (schedule.localizer n)
  rw [MeasureTheory.stoppedProcess_stoppedProcess'] at hSourceStopped
  have hStoppedEq :
      MeasureTheory.stoppedProcess
          (G.deterministicallyStopped (schedule.horizon n)
            (schedule.horizon_pos n)).finiteVariationPart
          (fun omega => min (schedule.localizer n omega)
            (schedule.localizer n omega)) =
        MeasureTheory.stoppedProcess
          (G.deterministicallyStopped (schedule.horizon n)
            (schedule.horizon_pos n)).finiteVariationPart
          (schedule.localizer n) := by
    funext t omega
    simp
  rw [hStoppedEq] at hSourceStopped
  exact hSource.trans hSourceStopped.symm

omit [F.IsRightContinuous] in
/-- The completed finite-variation coordinate is already stopped at its
localizer.  This is the direct source-path locality law, transported through
the raw/completed finite-variation integral agreement. -/
theorem completedFiniteVariationCoordinate_indistinguishable_stopped
    (schedule : LocalCompletedM2ASchedule G)
    (coefficient : forall n, FiniteHorizonM2ACoefficient
      (schedule.variationBridge n) (schedule.quadraticKernel n))
    (n : Nat) :
    ProcessIndistinguishable mu
      (completedFiniteVariationCoordinate schedule coefficient n)
      (MeasureTheory.stoppedProcess
        (completedFiniteVariationCoordinate schedule coefficient n)
        (schedule.localizer n)) := by
  have hCompleted := finiteHorizonCompletedFiniteVariationPart_indistinguishable
    schedule.usualConditions (schedule.variationBridge n)
      (schedule.quadraticKernel n) (coefficient n)
  have hRaw := finiteVariationIntegralProcess_eq_stopped_of_path
    (schedule.variationBridge n) (schedule.variationBridge n)
      (schedule.localizer n) (schedule.horizon n)
      (schedule.localizer_le_horizon n)
      (sourcePrefix_finiteVariationPart_indistinguishable_stopped schedule n)
      (coefficient n).integrand (coefficient n).integrand
      (by intro omega u hu; rfl)
  exact hCompleted.trans <| hRaw.trans <|
    hCompleted.symm.stoppedProcess (schedule.localizer n)

omit [F.IsRightContinuous] in
/-- A common coefficient family glues to one locally S-integrable
M² ⊕ A¹ candidate strategy. -/
theorem exists_completedM2AGainStrategy_with_integrand
    (schedule : LocalCompletedM2ASchedule G)
    (coefficient : forall n, FiniteHorizonM2ACoefficient
      (schedule.variationBridge n) (schedule.quadraticKernel n))
    {f : NNReal × Omega -> Real}
    (hCoefficient : forall n, (coefficient n).coefficient = f) :
    ∃ H : LocallySIntegrableStrategy D,
      H.integrand = Function.curry f ∧
      (∀ n, ProcessIndistinguishable mu
        (MeasureTheory.stoppedProcess H.stochasticIntegral
          (schedule.localizer n))
        (finiteHorizonCompletedM2AGain schedule.usualConditions
          (schedule.horizon n) (schedule.quadraticKernel n)
          (schedule.variationBridge n) (schedule.martingale n)
          (schedule.terminal_memLp n) (coefficient n))) ∧
      (∀ n, ProcessIndistinguishable mu
        (MeasureTheory.stoppedProcess H.martingalePart
          (schedule.localizer n))
        (finiteHorizonCompletedMartingalePart schedule.usualConditions
          (schedule.horizon n) (schedule.quadraticKernel n)
          (schedule.martingale n) (schedule.terminal_memLp n) (coefficient n))) ∧
      (∀ n, ProcessIndistinguishable mu
        (MeasureTheory.stoppedProcess H.finiteVariationPart
          (schedule.localizer n))
        (finiteHorizonCompletedFiniteVariationPart schedule.usualConditions
          (schedule.horizon n) (schedule.quadraticKernel n)
          (schedule.variationBridge n) (coefficient n))) := by
  have hf : StronglyMeasurable[F.predictable] f := by
    rw [← hCoefficient 0]
    exact (coefficient 0).coefficient_isStronglyMeasurable
  have hMartingale : forall n,
      Martingale (completedMartingaleCoordinate schedule coefficient n)
        F mu := by
    intro n
    exact finiteHorizonMartingaleIntegralProcess_isMartingale
      schedule.usualConditions (schedule.quadraticKernel n)
      (schedule.martingale n)
      (schedule.sourcePrefix n).martingalePart_isRightContinuous
      (schedule.terminal_memLp n)
      (Function.uncurry (coefficient n).integrand)
      (coefficient n).integrand_isStronglyPredictable
      (coefficient n).integrand_memLp_energy
  have hMartingaleRight : forall n omega t,
      ContinuousWithinAt
        (completedMartingaleCoordinate schedule coefficient n · omega)
        (Ici t) t := by
    intro n
    exact finiteHorizonMartingaleIntegralProcess_rightContinuous
      schedule.usualConditions (schedule.quadraticKernel n)
      (schedule.martingale n)
      (schedule.sourcePrefix n).martingalePart_isRightContinuous
      (schedule.terminal_memLp n)
      (Function.uncurry (coefficient n).integrand)
      (coefficient n).integrand_isStronglyPredictable
      (coefficient n).integrand_memLp_energy
  obtain ⟨M, hMAdapted, hMLocal, hMRight, hMStopped⟩ :=
    FTAPTheorem42.CompatibleLocalMartingaleGluing.exists_rightContinuous_localMartingale
      schedule.usualConditions schedule.isLocalizingSequence
      hMartingale hMartingaleRight
      (completedMartingaleCoordinates_compatible schedule
        coefficient hCoefficient)
  obtain ⟨A, hAPredictable, hARight, hALocalVariation, hAStopped⟩ :=
    exists_completedFiniteVariationCoordinatesGlue schedule
      coefficient hCoefficient
  let H : LocallySIntegrableStrategy D := {
    integrand := Function.curry f
    stochasticIntegral := fun t omega => M t omega + A t omega
    martingalePart := M
    finiteVariationPart := A
    integrand_isPredictable := by
      simpa only [IsStronglyPredictable, Function.uncurry_curry] using hf
    stochasticIntegral_isStronglyAdapted :=
      hMAdapted.add hAPredictable.stronglyAdapted
    stochasticIntegral_isRightContinuous := fun omega t =>
      (hMRight omega t).add (hARight omega t)
    martingalePart_isLocalMartingale := hMLocal
    martingalePart_isStronglyAdapted := hMAdapted
    martingalePart_isRightContinuous := hMRight
    finiteVariationPart_isPredictable := hAPredictable
    finiteVariationPart_isRightContinuous := hARight
    finiteVariationPart_isLocallyBoundedVariation := hALocalVariation
    integral_decomposition := ProcessIndistinguishable.refl mu _
    source_decomposition := G.source_decomposition }
  have hMUnstopped : forall n, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess M (schedule.localizer n))
      (finiteHorizonCompletedMartingalePart schedule.usualConditions
        (schedule.horizon n) (schedule.quadraticKernel n)
        (schedule.martingale n) (schedule.terminal_memLp n) (coefficient n)) := by
    intro n
    simpa only [completedMartingaleCoordinate] using
      (hMStopped n).trans
        (completedMartingaleCoordinate_indistinguishable_stopped
          schedule coefficient n).symm
  have hAUnstopped : forall n, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess A (schedule.localizer n))
      (finiteHorizonCompletedFiniteVariationPart schedule.usualConditions
        (schedule.horizon n) (schedule.quadraticKernel n)
        (schedule.variationBridge n) (coefficient n)) := by
    intro n
    simpa only [completedFiniteVariationCoordinate] using
      (hAStopped n).trans
        (completedFiniteVariationCoordinate_indistinguishable_stopped
          schedule coefficient n).symm
  have hGain : forall n, ProcessIndistinguishable mu
      (MeasureTheory.stoppedProcess H.stochasticIntegral
        (schedule.localizer n))
      (finiteHorizonCompletedM2AGain schedule.usualConditions
        (schedule.horizon n) (schedule.quadraticKernel n)
        (schedule.variationBridge n) (schedule.martingale n)
        (schedule.terminal_memLp n) (coefficient n)) := by
    intro n
    have hStopped := ProcessIndistinguishable.add
      (hMUnstopped n) (hAUnstopped n)
    have hStopped' : ProcessIndistinguishable mu
        (fun (t : NNReal) omega =>
          M (min (t : WithTop NNReal) (schedule.localizer n omega)).untopA omega +
            A (min (t : WithTop NNReal) (schedule.localizer n omega)).untopA omega)
        (fun (t : NNReal) omega =>
          finiteHorizonCompletedMartingalePart schedule.usualConditions
              (schedule.horizon n) (schedule.quadraticKernel n)
              (schedule.martingale n) (schedule.terminal_memLp n) (coefficient n) t omega +
            finiteHorizonCompletedFiniteVariationPart schedule.usualConditions
              (schedule.horizon n) (schedule.quadraticKernel n)
              (schedule.variationBridge n) (coefficient n) t omega) := by
      simpa only [MeasureTheory.stoppedProcess, Pi.add_apply] using hStopped
    change ProcessIndistinguishable mu
      (fun (t : NNReal) omega =>
        M (min (t : WithTop NNReal) (schedule.localizer n omega)).untopA omega +
          A (min (t : WithTop NNReal) (schedule.localizer n omega)).untopA omega)
      (fun (t : NNReal) omega =>
        finiteHorizonCompletedM2AGain schedule.usualConditions
          (schedule.horizon n) (schedule.quadraticKernel n)
          (schedule.variationBridge n) (schedule.martingale n)
          (schedule.terminal_memLp n) (coefficient n) t omega)
    simpa only [finiteHorizonCompletedM2AGain] using hStopped'
  exact ⟨H, rfl, hGain, hMUnstopped, hAUnstopped⟩

end LocalCompletedM2A

end FTAPTheorem42
