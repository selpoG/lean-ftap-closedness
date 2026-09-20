/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.PredictableLimsupCore
import FTAPTheorem42.Stochastic.Decomposition.CompensatorL2.CadlagCandidate

/-!
# Predictable limsups for square-integrable compensator rows

This file is only the square-integrable adapter for the source-independent
predictable-limsup core.  The selected common-a.e. rows and a monotone
regularized càdlàg candidate are consumed directly.  No optional sampling,
process bridge, or dual predictable projection is asserted here.
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

/-! ## The square-integrable raw limsup -/

noncomputable def squareIntegrablePredictableCompensatorLimsup
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      SquareIntegrableFactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows hControl r)
    (w : ∀ n, TailConvexWeights n) (cutoff : Nat → Nat) : Process Ω :=
  CommonHilbertRowsData.predictableLimsup
    (squareIntegrableCommonHilbertRowsData hV hRows hControl hResidual)
    w cutoff

/-! The public certificate is an abbreviation for the generic core. -/

abbrev SquareIntegrableIncreasingProcessPredictableLimsupData
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
    (Ppred : Process Ω) : Prop :=
  CommonHilbertRowsData.PredictableLimsupData hCad hReg cutoff hData Ppred

omit [SigmaFiniteFiltration mu F] in
theorem exists_squareIntegrableIncreasingProcessPredictableLimsup
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
      hV hRows hControl hResidual w y hCommon Z M Pcad hCad bad Preg) :
    SquareIntegrableIncreasingProcessPredictableLimsupData
      hV hRows hControl hResidual w y hCommon cutoff hData
        Z M Pcad hCad bad Preg hReg
        (squareIntegrablePredictableCompensatorLimsup
          hV hRows hControl hResidual w cutoff) := by
  exact CommonHilbertRowsData.exists_predictableLimsup
    (h := squareIntegrableCommonHilbertRowsData hV hRows hControl hResidual)
    (w := w) (y := y) (hCommon := hCommon)
    (cutoff := cutoff) (hData := hData)
    (source_valueToLp := squareIntegrableCadlagCandidateSourceValueToLp
      (F := F) (mu := mu) hV)
    (X := V)
    (hSource := squareIntegrableCadlagCandidateSourceData
      (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon)
    (Z := Z) (M := M) (Pcad := Pcad) (hCad := hCad)
    (bad := bad) (Preg := Preg) (hReg := hReg)

/-! ## Direct consumers for the two regularized Jordan components -/

omit [SigmaFiniteFiltration mu F] in
theorem exists_squareIntegrablePredictableLimsups_of_monotoneRegularizedCadlagCandidates
    {VPlus VMinus : Process Ω} {T : NNReal}
    (hVPlus : SquareIntegrableIncreasingProcessData
      (F := F) (mu := mu) VPlus T)
    (hRowsPlus : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hVPlus)
    (hControlPlus : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hVPlus hRowsPlus)
    (hResidualPlus : ∀ r,
      SquareIntegrableFactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hVPlus hRowsPlus hControlPlus r)
    (wPlus : ∀ n, TailConvexWeights n)
    (yPlus : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal))
    (hCommonPlus : SquareIntegrableIncreasingProcessCommonHilbertConvexificationData
      hVPlus hRowsPlus hControlPlus hResidualPlus wPlus yPlus)
    (cutoffPlus : Nat → Nat)
    (hDataPlus : SquareIntegrableIncreasingProcessCommonAESubsequenceData
      hVPlus hRowsPlus hControlPlus hResidualPlus wPlus yPlus hCommonPlus cutoffPlus)
    (ZPlus : Lp Real 2 mu) (MPlus PcadPlus : Process Ω)
    (hCadPlus : SquareIntegrableIncreasingProcessCadlagCandidateData
      hVPlus hRowsPlus hControlPlus hResidualPlus wPlus yPlus hCommonPlus
        ZPlus MPlus PcadPlus)
    (badPlus : Set Ω) (PregPlus : Process Ω)
    (hRegPlus : SquareIntegrableIncreasingProcessCadlagMonotoneRegularizationData
      hVPlus hRowsPlus hControlPlus hResidualPlus wPlus yPlus hCommonPlus
        ZPlus MPlus PcadPlus hCadPlus badPlus PregPlus)
    (hVMinus : SquareIntegrableIncreasingProcessData
      (F := F) (mu := mu) VMinus T)
    (hRowsMinus : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hVMinus)
    (hControlMinus : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hVMinus hRowsMinus)
    (hResidualMinus : ∀ r,
      SquareIntegrableFactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hVMinus hRowsMinus hControlMinus r)
    (wMinus : ∀ n, TailConvexWeights n)
    (yMinus : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal))
    (hCommonMinus : SquareIntegrableIncreasingProcessCommonHilbertConvexificationData
      hVMinus hRowsMinus hControlMinus hResidualMinus wMinus yMinus)
    (cutoffMinus : Nat → Nat)
    (hDataMinus : SquareIntegrableIncreasingProcessCommonAESubsequenceData
      hVMinus hRowsMinus hControlMinus hResidualMinus wMinus yMinus hCommonMinus cutoffMinus)
    (ZMinus : Lp Real 2 mu) (MMinus PcadMinus : Process Ω)
    (hCadMinus : SquareIntegrableIncreasingProcessCadlagCandidateData
      hVMinus hRowsMinus hControlMinus hResidualMinus wMinus yMinus hCommonMinus
        ZMinus MMinus PcadMinus)
    (badMinus : Set Ω) (PregMinus : Process Ω)
    (hRegMinus : SquareIntegrableIncreasingProcessCadlagMonotoneRegularizationData
      hVMinus hRowsMinus hControlMinus hResidualMinus wMinus yMinus hCommonMinus
        ZMinus MMinus PcadMinus hCadMinus badMinus PregMinus) :
    ∃ PpredPlus : Process Ω,
      SquareIntegrableIncreasingProcessPredictableLimsupData
        hVPlus hRowsPlus hControlPlus hResidualPlus wPlus yPlus hCommonPlus
          cutoffPlus hDataPlus ZPlus MPlus PcadPlus hCadPlus badPlus PregPlus
            hRegPlus PpredPlus ∧
      ∃ PpredMinus : Process Ω,
        SquareIntegrableIncreasingProcessPredictableLimsupData
          hVMinus hRowsMinus hControlMinus hResidualMinus wMinus yMinus hCommonMinus
            cutoffMinus hDataMinus ZMinus MMinus PcadMinus hCadMinus badMinus PregMinus
              hRegMinus PpredMinus := by
  refine ⟨squareIntegrablePredictableCompensatorLimsup
      hVPlus hRowsPlus hControlPlus hResidualPlus wPlus cutoffPlus, ?_⟩
  refine ⟨exists_squareIntegrableIncreasingProcessPredictableLimsup
      hVPlus hRowsPlus hControlPlus hResidualPlus wPlus yPlus hCommonPlus
        cutoffPlus hDataPlus ZPlus MPlus PcadPlus hCadPlus badPlus PregPlus hRegPlus, ?_⟩
  refine ⟨squareIntegrablePredictableCompensatorLimsup
      hVMinus hRowsMinus hControlMinus hResidualMinus wMinus cutoffMinus, ?_⟩
  exact exists_squareIntegrableIncreasingProcessPredictableLimsup
    hVMinus hRowsMinus hControlMinus hResidualMinus wMinus yMinus hCommonMinus
      cutoffMinus hDataMinus ZMinus MMinus PcadMinus hCadMinus badMinus PregMinus hRegMinus

end HorizonFactorialGrid

end FTAPTheorem42
