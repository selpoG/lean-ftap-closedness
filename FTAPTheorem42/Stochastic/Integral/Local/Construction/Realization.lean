/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedM2ARealization

/-!
# Strategy-dependent local completed M² ⊕ A¹ realization

A fixed passage carrier chooses one localizing schedule before it selects its
realized graphs.  The global stochastic-integral range instead has to allow
the localizing schedule to depend on the integrand.  This module separates
these two layers.

`LocalCompletedM2ASchedule` contains one exhaustive stopping schedule and the
concrete finite-horizon `M² ⊕ A¹` integrator at every coordinate.  Its three
component identities tie those integrators to the stopped raw source `G`.
They do not assert that `G` is the unit-integrand graph of the market source;
that semantic identification remains a separate theorem.

`GraphWitness` then supplies, for one raw strategy record, a
coefficient and a stopped-gain graph witness at every coordinate.  The
resulting realization model existentially quantifies the whole schedule for
each graph.  It is independent of any prior realization carrier.
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
  {D : SpecialSemimartingaleDecomposition S F mu}

/-- One exhaustive family of concrete finite-horizon integrators for a raw
locally finite-variation source.  The family is independent of the strategy
which will later be represented against it, while the component identities
prevent an unrelated family of finite-horizon integrators from serving as a
schedule for `G`. -/
structure LocalCompletedM2ASchedule (G : LocallySIntegrableStrategy D) where
  usualConditions : Filtration.UsualConditions mu F
  localizer : Nat -> Omega -> WithTop NNReal
  isLocalizingSequence : ProbabilityTheory.IsLocalizingSequence F localizer mu
  horizon : Nat -> NNReal
  horizon_pos : forall n, 0 < horizon n
  localizer_le_horizon : forall n omega,
    localizer n omega <= (horizon n : WithTop NNReal)
  sourcePrefix : Nat -> SIntegrableStrategy D
  sourcePrefix_stochasticIntegral : forall n,
    ProcessIndistinguishable mu (sourcePrefix n).stochasticIntegral
      (MeasureTheory.stoppedProcess
        (G.deterministicallyStopped (horizon n) (horizon_pos n)
          ).stochasticIntegral (localizer n))
  sourcePrefix_martingalePart : forall n,
    ProcessIndistinguishable mu (sourcePrefix n).martingalePart
      (MeasureTheory.stoppedProcess
        (G.deterministicallyStopped (horizon n) (horizon_pos n)
          ).martingalePart (localizer n))
  sourcePrefix_finiteVariationPart : forall n,
    ProcessIndistinguishable mu (sourcePrefix n).finiteVariationPart
      (MeasureTheory.stoppedProcess
        (G.deterministicallyStopped (horizon n) (horizon_pos n)
          ).finiteVariationPart (localizer n))
  martingale : forall n, Martingale (sourcePrefix n).martingalePart F mu
  terminal_memLp : forall n,
    MemLp ((sourcePrefix n).martingalePart (horizon n)) (2 : ENNReal) mu
  variationBridge : forall n,
    SIntegrableFiniteVariationBridge (sourcePrefix n)
  quadraticKernel : forall n,
    BoundedMartingaleQuadraticKernel.Data F mu
      (sourcePrefix n).martingalePart (horizon n)

/-- A raw strategy graph represented along one exhaustive completed schedule.
The schedule is part of the witness and may therefore depend on `H`. -/
structure GraphWitness
    (G : LocallySIntegrableStrategy D) (H : SIntegrableStrategy D) where
  schedule : LocalCompletedM2ASchedule G
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

/-- The graph-extensional carrier obtained by existentially choosing a local
completed schedule separately for every raw strategy graph. -/
def realizationModel (G : LocallySIntegrableStrategy D) :
    SIntegrableRealizationModel D where
  IsRealized H := Nonempty (GraphWitness G H)
  isRealized_congr := by
    intro H K hIntegrand hGain hH
    obtain ⟨witness⟩ := hH
    refine ⟨{
      schedule := witness.schedule
      coefficient := witness.coefficient
      coefficient_eq := fun n =>
        (witness.coefficient_eq n).trans
          (congrArg Function.uncurry hIntegrand)
      stoppedGain_eq := fun n => ?_ }⟩
    exact ((hGain.symm).stoppedProcess (witness.schedule.localizer n)).trans
      (witness.stoppedGain_eq n)

end LocalCompletedM2A

end FTAPTheorem42

namespace FTAPTheorem42

/-! ## Initial value of the completed integral graph

The zero initial gain follows from completion and the graph identity, without
any raw restriction calculus or normalization of the stored components.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
  {S : Process Ω} {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ F]
  {D : SpecialSemimartingaleDecomposition S F μ}

open SIntegrableFiniteVariationBridge
open BoundedMartingaleQuadraticEnergy.Data

omit [SigmaFiniteFiltration μ F] in
/-- Uniform completion retains the zero initial value of the Stieltjes integrals. -/
theorem completedFiniteVariationProcess_zero
    {G : SIntegrableStrategy D} (hUsual : Filtration.UsualConditions μ F)
    (E : SIntegrableFiniteVariationBridge G)
    (f : Process Ω) (hf : IsStronglyPredictable F f)
    (hVariation : MemLp (Function.uncurry f) 1 (canonicalVariationMeasure E)) :
    completedFiniteVariationProcess hUsual E f hf hVariation 0 =ᵐ[μ] 0 := by
  filter_upwards [(completedFiniteVariationProcessData
    hUsual E f hf hVariation).approximation_tendsto] with ω hω
  have h := hω.1.tendsto_at 0
  have hZero : ∀ n, commonFiniteVariationProcessApproximation E f hf n 0 ω = 0 := by
    intro n
    simp [commonFiniteVariationProcessApproximation, finiteVariationIntegralProcess,
      pathVariationMeasureUpTo]
  simp only [hZero] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

namespace LocalCompletedM2A

/-- Even a single completed coordinate forces the raw gain to start from zero. -/
theorem GraphWitness.stochasticIntegral_zero
    {G : LocallySIntegrableStrategy D} {H : SIntegrableStrategy D}
    (w : GraphWitness G H) : H.stochasticIntegral 0 =ᵐ[μ] 0 := by
  let c := w.coefficient 0
  have hM := finiteHorizonMartingaleIntegralProcess_zero
    w.schedule.usualConditions (w.schedule.quadraticKernel 0)
    (w.schedule.martingale 0)
    (w.schedule.sourcePrefix 0).martingalePart_isRightContinuous
    (w.schedule.terminal_memLp 0) (Function.uncurry c.integrand)
    c.integrand_isStronglyPredictable c.integrand_memLp_energy
  have hA := completedFiniteVariationProcess_zero
    w.schedule.usualConditions (w.schedule.variationBridge 0)
    c.integrand c.integrand_isStronglyPredictable c.integrand_memLp_variation
  filter_upwards [w.stoppedGain_eq 0, hM, hA] with ω hEq hM hA
  have h := hEq 0
  rw [MeasureTheory.stoppedProcess_eq_of_le bot_le] at h
  change H.stochasticIntegral 0 ω = _ + _ at h
  exact h.trans ((congrArg₂ (· + ·) hM hA).trans (add_zero 0))

/-- Actual membership supplies the initial value independently of restriction. -/
theorem actual_stochasticIntegral_zero
    {G : LocallySIntegrableStrategy D}
    (H : ActualSIntegrableStrategy (realizationModel G)) :
    H.val.stochasticIntegral 0 =ᵐ[μ] 0 := by
  obtain ⟨w⟩ := H.property
  exact w.stochasticIntegral_zero

end LocalCompletedM2A

end FTAPTheorem42
