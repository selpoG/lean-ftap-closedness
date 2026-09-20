/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Decomposition.Source.GlobalFixedStopOverlap
import FTAPTheorem42.Stochastic.Decomposition.Source.RegularizedSpecialSemimartingale

/-!
# Gluing the common-stop fixed-stop components

The common-stop exhaustion carries one pair of stopped component processes at
each coordinate of a single localizing schedule.  The overlap module proves
the exact minimum-stop compatibility required by the two generic gluing
primitives.  This module consumes those two compatibility statements on that
same schedule and retains the resulting component certificate.

Only the component processes are glued here.  In particular, no source
decomposition is asserted for the global pair; that is the next boundary.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

/-! ## The global component certificate -/

/-- The two global component processes obtained by gluing one common
localizing schedule.  The stopped agreements are retained explicitly for
the subsequent source-decomposition consumer. -/
structure CommonStopUncenteredFixedStopGlobalGluingData
    {S : Process Ω}
    (T : Nat → NNReal) (eta : Nat → Real)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    (family : CommonStopUncenteredFixedStopFamily T eta hUsual source)
    (tau : Nat → Ω → WithTop NNReal)
    (data : CommonStopUncenteredFixedStopExhaustionData
      T eta hUsual source family tau) where
  M : Process Ω
  A : Process Ω
  M_isStronglyAdapted : StronglyAdapted F M
  M_isLocalMartingale : LocalMartingale M F mu
  M_rightContinuous : ∀ omega t,
    ContinuousWithinAt (M · omega) (Ici t) t
  M_leftLimits : ProcessHasLeftLimits M
  A_isStronglyPredictable : IsStronglyPredictable F A
  A_isStronglyAdapted : StronglyAdapted F A
  A_rightContinuous : ∀ omega t,
    ContinuousWithinAt (A · omega) (Ici t) t
  A_leftLimits : ProcessHasLeftLimits A
  A_locallyBoundedVariation : ∀ omega,
    LocallyBoundedVariationOn (A · omega) Set.univ
  M_stopped : ∀ n, ProcessIndistinguishable mu
    (MeasureTheory.stoppedProcess M (tau n))
    (MeasureTheory.stoppedProcess (data.Mρ n) (tau n))
  A_stopped : ∀ n, ProcessIndistinguishable mu
    (MeasureTheory.stoppedProcess A (tau n))
    (MeasureTheory.stoppedProcess (data.Aρ n) (tau n))

/-! ## Consumption of both compatibility theorems -/

/-- The martingale and finite-variation coordinates of one common-stop
exhaustion glue to one càdlàg local martingale and one predictable,
right-continuous locally bounded-variation process.  Both gluing calls use
the `tau` schedule carried by the same exhaustion data. -/
theorem exists_commonStopUncenteredFixedStopGlobalGluingData
    {S : Process Ω}
    (T : Nat → NNReal) (eta : Nat → Real)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    (family : CommonStopUncenteredFixedStopFamily T eta hUsual source)
    (tau : Nat → Ω → WithTop NNReal)
    (data : CommonStopUncenteredFixedStopExhaustionData
      T eta hUsual source family tau) :
    Nonempty (CommonStopUncenteredFixedStopGlobalGluingData
      T eta hUsual source family tau data) := by
  have hMartingaleCompatibility :=
    commonStopUncenteredFixedStopExhaustionData_martingale_compatibility
      T eta hUsual source family tau data
  obtain ⟨M, hMAdapted, hMLocal, hMRight, hMLeft, hMStopped⟩ :=
    CompatibleLocalMartingaleGluing.exists_cadlag_localMartingale
      hUsual data.isLocalizingSequence
      (fun n => (data.restopped n).Mρ_martingale)
      (fun n => (data.restopped n).Mρ_rightContinuous)
      (fun n => (data.restopped n).Mρ_leftLimits)
      hMartingaleCompatibility
  have hFiniteVariationCompatibility :=
    commonStopUncenteredFixedStopExhaustionData_finiteVariation_compatibility
      T eta hUsual source family tau data
  obtain ⟨A, hAPredictable, hARight, hALocalVariation, hAStopped⟩ :=
    CompatibleLocalFiniteVariationGluing.exists_predictable_rightContinuous_locallyBoundedVariation
      hUsual data.isLocalizingSequence
      (fun n => (data.restopped n).Aρ_isStronglyPredictable)
      (fun n => (data.restopped n).Aρ_rightContinuous)
      (fun n => (data.restopped n).Aρ_boundedVariation)
      hFiniteVariationCompatibility
  have hALeft : ProcessHasLeftLimits A :=
    SpecialSemimartingaleDecomposition.finiteVariationPart_hasLeftLimits_of_localBoundedVariation
      hALocalVariation
  exact ⟨{
    M := M
    A := A
    M_isStronglyAdapted := hMAdapted
    M_isLocalMartingale := hMLocal
    M_rightContinuous := hMRight
    M_leftLimits := hMLeft
    A_isStronglyPredictable := hAPredictable
    A_isStronglyAdapted := hAPredictable.stronglyAdapted
    A_rightContinuous := hARight
    A_leftLimits := hALeft
    A_locallyBoundedVariation := hALocalVariation
    M_stopped := hMStopped
    A_stopped := hAStopped }⟩

end HorizonFactorialGrid

end FTAPTheorem42
