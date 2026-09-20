/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.CompensatorL2.StoppingLimsupFoundation
import FTAPTheorem42.Stochastic.Decomposition.Compensator.StoppingLimsupEqualityCore

/-!
# The square-integrable stopped limsup equality

This file adapts the source-independent terminal-difference consumer to the
square-integrable compensator package.  The terminal candidate certificate is
an explicit input, so the adapter introduces no new row, cutoff, or stopping
time selection.
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

/-! ## The specialized equality certificate -/

abbrev SquareIntegrablePredictableCompensatorStoppingLimsupEqualityData
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
      hV hRows hControl hResidual w y hCommon Z M Pcad hCad bad Preg hReg τ hτ hτT)
    (hFoundation : SquareIntegrablePredictableCompensatorStoppingLimsupFoundationData
      hV hRows hControl hResidual w y hCommon cutoff hData
        Z M Pcad hCad bad Preg hReg Ppred hLimsup τ hτ hτT hStop hCandidate) : Prop :=
  CommonHilbertRowsData.StoppingLimsupEqualityData
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
    hCandidate hFoundation

/-! ## The L² adapter -/

omit [SigmaFiniteFiltration mu F] in
theorem squareIntegrablePredictableCompensatorStoppingLimsupEquality_producer
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
      hV hRows hControl hResidual w y hCommon Z M Pcad hCad bad Preg hReg τ hτ hτT)
    (hTerminalCandidate : SquareIntegrableIncreasingProcessCandidateOptionalSamplingData
      hV hRows hControl hResidual w y hCommon Z M Pcad hCad bad Preg hReg
        (fun _ : Ω => T) (isStoppingTime_const F T) (fun _ => le_rfl))
    (hFoundation : SquareIntegrablePredictableCompensatorStoppingLimsupFoundationData
      hV hRows hControl hResidual w y hCommon cutoff hData
        Z M Pcad hCad bad Preg hReg Ppred hLimsup τ hτ hτT hStop hCandidate) :
    SquareIntegrablePredictableCompensatorStoppingLimsupEqualityData
      hV hRows hControl hResidual w y hCommon cutoff hData
        Z M Pcad hCad bad Preg hReg Ppred hLimsup τ hτ hτT hStop hCandidate
        hFoundation := by
  exact CommonHilbertRowsData.stoppingLimsupEquality_producer
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
    hCandidate hTerminalCandidate hFoundation

end HorizonFactorialGrid

end FTAPTheorem42
