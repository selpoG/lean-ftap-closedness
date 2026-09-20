/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.StoppingLimsupFoundationCore
import FTAPTheorem42.Stochastic.Decomposition.CompensatorL2.StoppingConvexExpectation
import FTAPTheorem42.Stochastic.Decomposition.CompensatorL2.CandidateOptionalSampling
import FTAPTheorem42.Stochastic.Decomposition.CompensatorL2.PredictableLimsup

/-!
# The square-integrable stopping-limsup foundation

This file is only the adapter from the square-integrable compensator rows to
the source-independent terminal-difference foundation.  All rows, weights,
cutoffs, candidates, and predictable limsups are supplied by the caller; no
new existential choice is made at a stopping time.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {V : Process Ω} {T : NNReal}

open SquareIntegrableIncreasingProcessData

/-! ## Adapters for the two preceding stopping-time certificates -/

omit [SigmaFiniteFiltration mu F] in
theorem squareIntegrableStoppingConvexExpectationCertificate
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      SquareIntegrableFactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows hControl r)
    (w : ∀ n, TailConvexWeights n)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal))
    (hCommon : SquareIntegrableIncreasingProcessCommonHilbertConvexificationData
      hV hRows hControl hResidual w y)
    (cutoff : Nat → Nat)
    (hData : SquareIntegrableIncreasingProcessCommonAESubsequenceData
      hV hRows hControl hResidual w y hCommon cutoff)
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T)
    (hStop : SquareIntegrableFactorialGridPredictableCompensatorStoppingConvexExpectationData
      hV hRows hControl hResidual w y hCommon cutoff hData τ hτ hτT) :
    CommonHilbertRowsData.StoppingConvexExpectationCertificate
      (squareIntegrableCommonHilbertRowsData hV hRows hControl hResidual)
      w cutoff V τ := by
  refine {
    row_integrable := ?_
    integral_tendsto := ?_ }
  · intro n
    change Integrable (fun omega =>
      squareIntegrableCompensatorConvexRow hV hRows hControl hResidual
        (w (cutoff n)) (τ omega) omega) mu
    exact hStop.compensator_integrable n
  · change Tendsto (fun n =>
      ∫ omega, squareIntegrableCompensatorConvexRow hV hRows hControl hResidual
        (w (cutoff n)) (τ omega) omega ∂mu) atTop
      (𝓝 (∫ omega, V (τ omega) omega ∂mu))
    exact hStop.integral_tendsto

/-! ## Public specialized certificate -/

abbrev SquareIntegrablePredictableCompensatorStoppingLimsupFoundationData
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      SquareIntegrableFactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows hControl r)
    (w : ∀ n, TailConvexWeights n)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal))
    (hCommon : SquareIntegrableIncreasingProcessCommonHilbertConvexificationData
      hV hRows hControl hResidual w y)
    (cutoff : Nat → Nat)
    (hData : SquareIntegrableIncreasingProcessCommonAESubsequenceData
      hV hRows hControl hResidual w y hCommon cutoff)
    (Z : Lp Real 2 mu) (M Pcad : Process Ω)
    (hCad : SquareIntegrableIncreasingProcessCadlagCandidateData
      hV hRows hControl hResidual w y hCommon Z M Pcad)
    (bad : Set Ω) (Preg : Process Ω)
    (hReg : SquareIntegrableIncreasingProcessCadlagMonotoneRegularizationData
      hV hRows hControl hResidual w y hCommon Z M Pcad hCad bad Preg)
    (Ppred : Process Ω)
    (hLimsup : SquareIntegrableIncreasingProcessPredictableLimsupData
      hV hRows hControl hResidual w y hCommon cutoff hData
        Z M Pcad hCad bad Preg hReg Ppred)
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T)
    (hStop : SquareIntegrableFactorialGridPredictableCompensatorStoppingConvexExpectationData
      hV hRows hControl hResidual w y hCommon cutoff hData τ hτ hτT)
    (hCandidate : SquareIntegrableIncreasingProcessCandidateOptionalSamplingData
      hV hRows hControl hResidual w y hCommon Z M Pcad hCad bad Preg hReg τ hτ hτT) : Prop :=
  CommonHilbertRowsData.StoppingLimsupFoundationData
    (h := squareIntegrableCommonHilbertRowsData hV hRows hControl hResidual)
    (w := w) (y := y) (hCommon := hCommon) (cutoff := cutoff)
    (hData := hData)
    (source_valueToLp := squareIntegrableCadlagCandidateSourceValueToLp
      (F := F) (mu := mu) hV)
    (X := V)
    (hSource := squareIntegrableCadlagCandidateSourceData
      (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon)
    (Z := Z) (M := M) (Pcad := Pcad) (hCad := hCad) (bad := bad) (Preg := Preg)
    (hReg := hReg) (Ppred := Ppred) (hLimsup := hLimsup)
    τ hτ hτT
    (squareIntegrableStoppingConvexExpectationCertificate
      (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon
      cutoff hData τ hτ hτT hStop)
    hCandidate

/-! ## L² producer -/

omit [SigmaFiniteFiltration mu F] in
theorem squareIntegrablePredictableCompensatorStoppingLimsupFoundation_producer
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      SquareIntegrableFactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows hControl r)
    (w : ∀ n, TailConvexWeights n)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal))
    (hCommon : SquareIntegrableIncreasingProcessCommonHilbertConvexificationData
      hV hRows hControl hResidual w y)
    (cutoff : Nat → Nat)
    (hData : SquareIntegrableIncreasingProcessCommonAESubsequenceData
      hV hRows hControl hResidual w y hCommon cutoff)
    (Z : Lp Real 2 mu) (M Pcad : Process Ω)
    (hCad : SquareIntegrableIncreasingProcessCadlagCandidateData
      hV hRows hControl hResidual w y hCommon Z M Pcad)
    (bad : Set Ω) (Preg : Process Ω)
    (hReg : SquareIntegrableIncreasingProcessCadlagMonotoneRegularizationData
      hV hRows hControl hResidual w y hCommon Z M Pcad hCad bad Preg)
    (Ppred : Process Ω)
    (hLimsup : SquareIntegrableIncreasingProcessPredictableLimsupData
      hV hRows hControl hResidual w y hCommon cutoff hData
        Z M Pcad hCad bad Preg hReg Ppred)
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T)
    (hStop : SquareIntegrableFactorialGridPredictableCompensatorStoppingConvexExpectationData
      hV hRows hControl hResidual w y hCommon cutoff hData τ hτ hτT)
    (hCandidate : SquareIntegrableIncreasingProcessCandidateOptionalSamplingData
      hV hRows hControl hResidual w y hCommon Z M Pcad hCad bad Preg hReg τ hτ hτT) :
    SquareIntegrablePredictableCompensatorStoppingLimsupFoundationData
      hV hRows hControl hResidual w y hCommon cutoff hData Z M Pcad hCad bad Preg hReg
      Ppred hLimsup τ hτ hτT hStop hCandidate := by
  exact CommonHilbertRowsData.stoppingLimsupFoundation_producer
    (h := squareIntegrableCommonHilbertRowsData hV hRows hControl hResidual)
    (w := w) (y := y) (hCommon := hCommon) (cutoff := cutoff)
    (hData := hData)
    (source_valueToLp := squareIntegrableCadlagCandidateSourceValueToLp
      (F := F) (mu := mu) hV)
    (X := V)
    (hSource := squareIntegrableCadlagCandidateSourceData
      (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon)
    (Z := Z) (M := M) (Pcad := Pcad) hCad (bad := bad) (Preg := Preg)
    hReg Ppred hLimsup τ hτ hτT
    (squareIntegrableStoppingConvexExpectationCertificate
      (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon
      cutoff hData τ hτ hτT hStop)
    hCandidate

end HorizonFactorialGrid

end FTAPTheorem42
