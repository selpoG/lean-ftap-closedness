/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.Local.Construction.Realization
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedM2AAgreement
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationIntegralProcessGeneralMeasure

/-!
# Martingale coordinates of locally completed graphs

An actual graph in the strategy-dependent local completed carrier comes with
one exhaustive schedule and one common `M² ⊕ A¹` coefficient at every
coordinate.  This module selects that witness once and identifies the
centered stopped martingale coordinate of the raw graph with the completed
martingale integral determined by the selected coefficient.

The proof uses only the stopped-gain identity stored by the graph witness,
the raw stopping calculus, and uniqueness of the special semimartingale
decomposition.  In particular, it does not appeal to membership in any
fixed passage carrier.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega]

namespace LocalCompletedM2A

open SIntegrableFiniteVariationBridge
open BoundedMartingaleQuadraticEnergy.Data

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  [F.IsRightContinuous]
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}

/-- A fixed choice of the local completed witness carried by an actual
graph.  Keeping this choice outside the coordinate theorem ensures that all
coordinates use the same exhaustive schedule. -/
noncomputable def actualGraphWitness
    {G : LocallySIntegrableStrategy D}
    (H : ActualSIntegrableStrategy (realizationModel G)) :
    GraphWitness G H.val :=
  Classical.choice H.property

end LocalCompletedM2A

/-!
## Finite-variation coordinates of locally completed graphs

An intrinsic actual graph is represented by one completed `M2 + A1` graph
at every coordinate of an exhaustive schedule.  Equality of the stopped
gains and uniqueness of the centered martingale coordinate identify the
remaining finite-variation coordinates up to their initial constants.  The
canonical completed finite-variation process starts at zero and agrees with
the raw cumulative Stieltjes integral, so this gives the precise local
finite-variation semantics needed by the intrinsic Stieltjes calculus.
-/

namespace LocalCompletedM2A

open SIntegrableFiniteVariationBridge

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  [F.IsRightContinuous]
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}

/-- At one coordinate of an intrinsic graph, the raw integrand belongs to
the source-prefix variation space and the centered stopped
finite-variation component is its raw cumulative Stieltjes integral. -/
theorem actualCoordinate_finiteVariationSemantics
    {G : LocallySIntegrableStrategy D}
    (H : ActualSIntegrableStrategy (realizationModel G))
    (n : Nat) :
    let witness := actualGraphWitness H
    exists _hVariation : MemLp (Function.uncurry H.val.integrand) 1
        (canonicalVariationMeasure (witness.schedule.variationBridge n)),
      ProcessIndistinguishable mu
        (fun t omega =>
          MeasureTheory.stoppedProcess H.val.finiteVariationPart
              (witness.schedule.localizer n) t omega -
            H.val.finiteVariationPart 0 omega)
        (finiteVariationIntegralProcess
          (witness.schedule.variationBridge n)
          (witness.coefficient n).integrand) := by
  let witness := actualGraphWitness H
  let schedule := witness.schedule
  let tau := schedule.localizer n
  let T := schedule.horizon n
  let c := witness.coefficient n
  let E := schedule.variationBridge n
  let sigma := RightContinuousStoppedMartingale.boundedTime T tau
  have hSigma : (fun omega => (sigma omega : WithTop NNReal)) = tau := by
    funext omega
    exact (RightContinuousStoppedMartingale.coe_boundedTime T tau omega).trans
      (min_eq_right (schedule.localizer_le_horizon n omega))
  have hStopping : IsStoppingTime F (fun omega => (sigma omega : WithTop NNReal)) := by
    rw [hSigma]
    exact schedule.isLocalizingSequence.isStoppingTime n
  let K := H.val.toLocally.finiteClosedStopOfRightContinuous sigma hStopping
  let V := finiteHorizonCompletedM2AStrategy schedule.usualConditions T
    (schedule.quadraticKernel n) E (schedule.martingale n)
      (schedule.terminal_memLp n) c
  have hVariation : MemLp (Function.uncurry H.val.integrand) 1
      (canonicalVariationMeasure E) := by
    rw [<- witness.coefficient_eq n]
    exact c.coefficient_memLp_variation
  refine ⟨hVariation, ?_⟩
  have hGain : ProcessIndistinguishable mu K.stochasticIntegral
      V.stochasticIntegral :=
    by
      change ProcessIndistinguishable mu
        (MeasureTheory.stoppedProcess H.val.stochasticIntegral
          (fun omega => (sigma omega : WithTop NNReal))) V.stochasticIntegral
      rw [hSigma]
      exact witness.stoppedGain_eq n
  have hCentered : ProcessIndistinguishable mu K.centeredMartingalePart
      V.centeredMartingalePart :=
    K.centeredMartingalePart_indistinguishable_of_gain
      schedule.usualConditions V hGain
  have hFiniteVariationCentered : ProcessIndistinguishable mu
      (fun t omega => K.finiteVariationPart t omega -
        K.finiteVariationPart 0 omega)
      (fun t omega => V.finiteVariationPart t omega -
        V.finiteVariationPart 0 omega) := by
    filter_upwards [K.integral_decomposition, V.integral_decomposition,
        hGain, hCentered]
        with omega hKDecomposition hVDecomposition hGainOmega
          hCenteredOmega
    intro t
    have hGainTime := hGainOmega t
    have hGainZero := hGainOmega 0
    have hKTime := hKDecomposition t
    have hKZero := hKDecomposition 0
    have hVTime := hVDecomposition t
    have hVZero := hVDecomposition 0
    have hMartingale := hCenteredOmega t
    change K.martingalePart t omega - K.martingalePart 0 omega =
      V.martingalePart t omega - V.martingalePart 0 omega at hMartingale
    linarith
  have hStopped : ProcessIndistinguishable mu K.finiteVariationPart
      (MeasureTheory.stoppedProcess H.val.finiteVariationPart tau) :=
    by
      change ProcessIndistinguishable mu
        (MeasureTheory.stoppedProcess H.val.finiteVariationPart
          (fun omega => (sigma omega : WithTop NNReal))) _
      rw [hSigma]
      exact ProcessIndistinguishable.refl mu _
  have hCompleted : ProcessIndistinguishable mu V.finiteVariationPart
      (finiteVariationIntegralProcess E c.integrand) :=
    finiteHorizonCompletedFiniteVariationPart_indistinguishable
      schedule.usualConditions E (schedule.quadraticKernel n) c
  filter_upwards [hFiniteVariationCentered, hStopped, hCompleted]
      with omega hCenteredOmega hStoppedOmega hCompletedOmega
  intro t
  have hTauZero : MeasureTheory.stoppedProcess H.val.finiteVariationPart
      tau 0 omega = H.val.finiteVariationPart 0 omega := by
    exact MeasureTheory.stoppedProcess_eq_of_le bot_le
  have hRawZero : finiteVariationIntegralProcess E c.integrand 0 omega = 0 := by
    simp [finiteVariationIntegralProcess, pathVariationMeasureUpTo]
  calc
    MeasureTheory.stoppedProcess H.val.finiteVariationPart tau t omega -
        H.val.finiteVariationPart 0 omega =
        K.finiteVariationPart t omega - K.finiteVariationPart 0 omega := by
      rw [hStoppedOmega t, hStoppedOmega 0, hTauZero]
    _ = V.finiteVariationPart t omega - V.finiteVariationPart 0 omega :=
      hCenteredOmega t
    _ = finiteVariationIntegralProcess E c.integrand t omega := by
      rw [hCompletedOmega t, hCompletedOmega 0, hRawZero, sub_zero]

/-- The local finite-variation coordinate has the signed Stieltjes measure
of the completed coefficient against its source-prefix bridge. -/
theorem actualCoordinate_finiteVariationPathDensity
    {G : LocallySIntegrableStrategy D}
    (H : ActualSIntegrableStrategy (realizationModel G))
    (n : Nat) :
    let witness := actualGraphWitness H
    ∀ᵐ omega ∂mu,
      let sigma := RightContinuousStoppedMartingale.boundedTime
        (witness.schedule.horizon n) (witness.schedule.localizer n) omega
      (FiniteVariationPath.signedMeasure
        ((witness.schedule.sourcePrefix n
          ).finiteVariationPart_isBoundedVariation omega)).totalVariation.withDensityᵥ
          (fun u => finiteVariationIntegralDensity
            (witness.schedule.variationBridge n)
              (witness.coefficient n).integrand (u, omega)) =
        FiniteVariationPath.signedMeasure
          (FiniteVariationStoppedPath.boundedVariationOn_stopAt
            (H.val.finiteVariationPart_isBoundedVariation omega) sigma) := by
  let witness := actualGraphWitness H
  let schedule := witness.schedule
  let tau := schedule.localizer n
  let T := schedule.horizon n
  let c := witness.coefficient n
  let E := schedule.variationBridge n
  obtain ⟨_, hSemantics⟩ :=
    actualCoordinate_finiteVariationSemantics H n
  have hIntegrable :=
    integrable_section_ae_of_memLp_one_canonicalVariation
      E c.integrand c.integrand_isStronglyPredictable
        c.integrand_memLp_variation
  filter_upwards [hIntegrable, hSemantics]
      with omega hIntegrableOmega hSemanticsOmega
  let sigma := RightContinuousStoppedMartingale.boundedTime T tau omega
  let B := FiniteVariationStoppedPath.stopAt
    (fun t => H.val.finiteVariationPart t omega) sigma
  let hB := FiniteVariationStoppedPath.boundedVariationOn_stopAt
    (H.val.finiteVariationPart_isBoundedVariation omega) sigma
  have hPath : (fun t => MeasureTheory.stoppedProcess
      H.val.finiteVariationPart tau t omega) = B := by
    exact RightContinuousStoppedMartingale.stoppedProcess_path_eq_stopAt_boundedTime
      H.val.finiteVariationPart tau T
        (schedule.localizer_le_horizon n) omega
  have hBIntegral : forall t,
      B t - B 0 = finiteVariationIntegralProcess E c.integrand t omega := by
    intro t
    rw [<- hPath]
    change MeasureTheory.stoppedProcess H.val.finiteVariationPart tau t omega -
      MeasureTheory.stoppedProcess H.val.finiteVariationPart tau 0 omega = _
    have hZero : MeasureTheory.stoppedProcess H.val.finiteVariationPart
        tau 0 omega = H.val.finiteVariationPart 0 omega :=
      MeasureTheory.stoppedProcess_eq_of_le bot_le
    rw [hZero]
    exact hSemanticsOmega t
  exact withDensity_finiteVariationIntegralDensity_eq_signedMeasure_of_eq
    E c.integrand_isStronglyPredictable omega hIntegrableOmega hB
      (fun t => FiniteVariationStoppedPath.rightContinuous_stopAt
        (fun u => H.val.finiteVariationPart u omega)
          (H.val.finiteVariationPart_isRightContinuous omega) sigma t)
      hBIntegral

end LocalCompletedM2A

end FTAPTheorem42
