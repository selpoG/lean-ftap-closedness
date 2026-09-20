/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.StoppingLimsupEquality
import FTAPTheorem42.Stochastic.Decomposition.Compensator.ProcessBridgeCore
import FTAPTheorem42.Stochastic.Stopping.MonotoneCadlagRationalPassage

/-!
# Process bridge for the predictable compensator limsup

The stopping-time equality identifies the predictable limsup with the
regularized càdlàg candidate at every bounded stopping time.  This module
consumes that statement along the countable family of clamped positive
rational passages.  The passage family covers every non-zero left jump of the
candidate; at the remaining times right continuity and the left-limit
characterization give continuity.  Thus the two processes are identified on
one common almost-everywhere set, without intersecting over all deterministic
times.

The first theorem is deliberately a small consumer: it takes the bounded
stopping-time equality as an input.  The second theorem supplies that input
from the existing finite-grid optional-sampling and terminal-difference
certificates.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

open BoundedIncreasingProcessData
open FTAPTheorem42.MonotoneCadlagRationalPassage

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {V : Process Ω} {T C : NNReal}

/-! ## Generic process-level consumer -/

omit [SigmaFiniteFiltration mu F] in
theorem processIndistinguishable_of_boundedStoppingTime_ae_eq
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      FactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows r)
    (w : ∀ n, TailConvexWeights n)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu)
      (2 : ENNReal))
    (hCommon : FactorialGridPredictableCompensatorCommonHilbertConvexificationData
      hV hRows hControl hResidual w y)
    (cutoff : Nat → Nat)
    (hData : FactorialGridPredictableCompensatorCommonAESubsequenceData
      hV hRows hControl hResidual w y hCommon cutoff)
    (hRightContinuous : F.IsRightContinuous)
    {Z : Lp Real 2 mu} {M Pcad : Process Ω}
    (hCad : FactorialGridPredictableCompensatorCadlagCandidateData
      hV hRows hControl hResidual hCommon Z M Pcad)
    (bad : Set Ω) (Preg : Process Ω)
    (hReg : FactorialGridPredictableCompensatorCadlagMonotoneRegularizationData
      hCad bad Preg)
    (Ppred : Process Ω)
    (hLimsup : FactorialGridPredictableCompensatorPredictableLimsupData
      hV hRows hControl hResidual w y hCommon cutoff hData
        Z M Pcad hCad bad Preg hReg Ppred)
    (hStopping : ∀ (τ : Ω → NNReal),
      IsStoppingTime F (fun omega => (τ omega : WithTop NNReal)) →
      (∀ omega, τ omega ≤ T) →
      (fun omega => Ppred (τ omega) omega) =ᵐ[mu]
        (fun omega => Preg (τ omega) omega)) :
    ProcessIndistinguishable mu Ppred Preg := by
  apply processIndistinguishable_of_boundedStoppingTime_ae_eq_core
    (T := T) (hRightContinuous := hRightContinuous)
    (Preg := Preg) (Ppred := Ppred)
    (hPregStronglyAdapted := hReg.Preg_stronglyAdapted)
    (hPregRightContinuous := hReg.Preg_rightContinuous)
    (hPregLeftLimits := hReg.Preg_leftLimits)
    (hPregNonnegative := hReg.Preg_nonnegative)
    (hPregMonotone := hReg.Preg_monotone)
    (hPregZero := hReg.Preg_zero)
    (hPregConstantAfter := hReg.Preg_constant_after)
    (hPpredZero := hLimsup.Ppred_zero)
    (hPpredConstantAfter := hLimsup.Ppred_constant_after)
    (hPpredEqPregAtContinuity := hLimsup.Ppred_eq_Preg_at_continuity)
    hStopping

/-! ## Consumer for the existing terminal-difference equality -/

omit [SigmaFiniteFiltration mu F] in
theorem processIndistinguishable_of_factorialGridPredictableCompensatorData
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      FactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows r)
    (w : ∀ n, TailConvexWeights n)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu)
      (2 : ENNReal))
    (hCommon : FactorialGridPredictableCompensatorCommonHilbertConvexificationData
      hV hRows hControl hResidual w y)
    (cutoff : Nat → Nat)
    (hData : FactorialGridPredictableCompensatorCommonAESubsequenceData
      hV hRows hControl hResidual w y hCommon cutoff)
    (Z : Lp Real 2 mu) (M Pcad : Process Ω)
    (hCad : FactorialGridPredictableCompensatorCadlagCandidateData
      hV hRows hControl hResidual hCommon Z M Pcad)
    (bad : Set Ω) (Preg : Process Ω)
    (hReg : FactorialGridPredictableCompensatorCadlagMonotoneRegularizationData
      hCad bad Preg)
    (Ppred : Process Ω)
    (hLimsup : FactorialGridPredictableCompensatorPredictableLimsupData
      hV hRows hControl hResidual w y hCommon cutoff hData
        Z M Pcad hCad bad Preg hReg Ppred)
    (hUsual : Filtration.UsualConditions mu F) :
    ProcessIndistinguishable mu Ppred Preg := by
  refine processIndistinguishable_of_boundedStoppingTime_ae_eq
    (hV := hV) (hRows := hRows) (hControl := hControl)
    (hResidual := hResidual) (w := w) (y := y) (hCommon := hCommon)
    (cutoff := cutoff) (hData := hData)
    (hRightContinuous := hUsual.rightContinuous)
    (hCad := hCad) (bad := bad) (Preg := Preg) (hReg := hReg) (Ppred := Ppred)
    (hLimsup := hLimsup) ?_
  intro τ hτ hτT
  obtain ⟨hStop⟩ :=
    exists_factorialGridPredictableCompensatorStoppingConvexExpectation
      (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon cutoff hData
        τ hτ hτT
  obtain ⟨hCandidate⟩ :=
    exists_factorialGridPredictableCompensatorCandidateOptionalSampling
      (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon Z M Pcad
        hCad bad Preg hReg τ hτ hτT
  obtain hFoundation :=
    factorialGridPredictableCompensatorStoppingLimsupFoundation_producer
      (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon cutoff hData
        Z M Pcad hCad bad Preg hReg Ppred hLimsup τ hτ hτT
        hStop hCandidate
  exact (exists_factorialGridPredictableCompensatorStoppingLimsupEquality
    (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon cutoff hData
      Z M Pcad hCad bad Preg hReg Ppred hLimsup τ hτ hτT
      hStop hCandidate hFoundation).some.stopped_sample_ae_eq

/-! ## Direct consumer for a common-stop Jordan component -/

omit [SigmaFiniteFiltration mu F] in
theorem processIndistinguishable_of_commonAEJordanComponent
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      FactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows r)
    (w : ∀ n, TailConvexWeights n)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu)
      (2 : ENNReal))
    (hCommon : FactorialGridPredictableCompensatorCommonHilbertConvexificationData
      hV hRows hControl hResidual w y)
    {Z : Lp Real 2 mu} {M Pcad : Process Ω}
    (hCad : FactorialGridPredictableCompensatorCadlagCandidateData
      hV hRows hControl hResidual hCommon Z M Pcad)
    (bad : Set Ω) (Preg : Process Ω)
    (hReg : FactorialGridPredictableCompensatorCadlagMonotoneRegularizationData
      hCad bad Preg)
    (component : FactorialGridPredictableCompensatorCommonAEJordanComponentData
      hV hRows hControl hResidual w y hCommon Z M Pcad hCad bad Preg hReg)
    (hUsual : Filtration.UsualConditions mu F) :
    ProcessIndistinguishable mu
      (predictableCompensatorLimsup w component.cutoff V F mu T C) Preg := by
  let hLimsup := predictableCompensatorLimsup_of_commonAEJordanComponent component
  exact processIndistinguishable_of_factorialGridPredictableCompensatorData
    (hV := hV) (hRows := hRows) (hControl := hControl)
    (hResidual := hResidual) (w := w) (y := y) (hCommon := hCommon)
    (cutoff := component.cutoff)
    (hData := component.common_subsequence)
    (Z := Z) (M := M) (Pcad := Pcad) (hCad := hCad)
    (bad := bad) (Preg := Preg) (hReg := hReg)
    (Ppred := predictableCompensatorLimsup w component.cutoff V F mu T C)
    (hLimsup := hLimsup) hUsual

end HorizonFactorialGrid

end FTAPTheorem42
