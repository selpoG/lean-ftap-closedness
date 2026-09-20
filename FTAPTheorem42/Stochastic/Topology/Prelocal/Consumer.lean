/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Topology.Prelocal.Basic
import FTAPTheorem42.Stochastic.DS.Lemma47.RightContinuousLocalizer
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableStrategyAlgebra

/-!
# Decomposition witnesses and their prelocal H¹ costs

A witness records martingale and finite-variation components whose sum agrees
with the given process on a strict stochastic prefix, together with their
regularity and finite expected costs. The cost functions below extract the
running-supremum martingale cost, the strict-prefix variation cost, and their sum.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace SIntegrableFiniteVariationBridge

/-!
## Decomposition witness
-/

/-- A public one-layer decomposition witness for the running-supremum proxy.

The agreement is only on the strict stochastic prefix.  In particular, no
closed-stop equality or predictability of the finite-variation component is
part of this carrier.
-/
structure EmeryPrelocalH1SupWitness
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} (X : Process Omega) (tau : Omega → NNReal)
    (T : NNReal) where
  N : Process Omega
  A : Process Omega
  agrees_on_strict_prefix : ∀ t omega, t < tau omega →
    N t omega + A t omega = X t omega
  martingale_isLocalMartingale : LocalMartingale N F mu
  martingale_isStronglyAdapted : StronglyAdapted F N
  martingale_isRightContinuous : ∀ omega t,
    ContinuousWithinAt (N · omega) (Set.Ici t) t
  martingale_hasLeftLimits : ProcessHasLeftLimits N
  stoppingTime : IsStoppingTime F
    (fun omega => (tau omega : WithTop NNReal))
  stoppingTime_le_horizon : ∀ omega, tau omega ≤ T
  finiteVariation_isStronglyAdapted : StronglyAdapted F A
  finiteVariation_isRightContinuous : ∀ omega t,
    ContinuousWithinAt (A · omega) (Set.Ici t) t
  finiteVariation_hasLeftLimits : ProcessHasLeftLimits A
  finiteVariation_isBoundedVariation : ∀ omega,
    BoundedVariationOn (A · omega) Set.univ
  martingale_envelope_stronglyMeasurable :
    StronglyMeasurable
      (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
        (MeasureTheory.stoppedProcess N
          (fun omega => (tau omega : WithTop NNReal))) T)
  martingale_envelope_memLp_one :
    MemLp
      (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
        (MeasureTheory.stoppedProcess N
          (fun omega => (tau omega : WithTop NNReal))) T)
      (1 : ENNReal) mu
  martingale_envelope_eq_iSup :
    ∀ omega,
      ENNReal.ofReal
          (FactorialChronologicalGrid.finiteHorizonAbsoluteEnvelope
            (MeasureTheory.stoppedProcess N
              (fun omega => (tau omega : WithTop NNReal))) T omega) =
        ⨆ t : Set.Iic T, ENNReal.ofReal
          (|MeasureTheory.stoppedProcess N
            (fun omega => (tau omega : WithTop NNReal)) t.1 omega|)
  finiteVariation_measurable :
    Measurable (fun omega => eVariationOn
      (strictPrefixProcess A tau · omega) (Set.Icc 0 T))
  finiteVariation_integral_ne_top :
    prelocalH1SupFiniteVariationExpectedVariation
      (mu := mu) A tau T ≠ ∞

/-! ## Costs on the flattened carrier -/

noncomputable def prelocalH1SupWitnessMartingaleCost
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} {X : Process Omega} {tau : Omega → NNReal}
    {T : NNReal}
    (w : EmeryPrelocalH1SupWitness (F := F) (mu := mu) X tau T) : ENNReal :=
  prelocalH1SupMartingaleRunningSupExpectation
    (mu := mu) w.N tau T

noncomputable def prelocalH1SupWitnessVariationCost
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} {X : Process Omega} {tau : Omega → NNReal}
    {T : NNReal}
    (w : EmeryPrelocalH1SupWitness (F := F) (mu := mu) X tau T) : ENNReal :=
  prelocalH1SupFiniteVariationExpectedVariation
    (mu := mu) w.A tau T

noncomputable def prelocalH1SupWitnessCost
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} {X : Process Omega} {tau : Omega → NNReal}
    {T : NNReal}
    (w : EmeryPrelocalH1SupWitness (F := F) (mu := mu) X tau T) : ENNReal :=
  prelocalH1SupWitnessMartingaleCost (mu := mu) w +
    prelocalH1SupWitnessVariationCost (mu := mu) w

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
