/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.CommonAESubsequenceCore
import FTAPTheorem42.Stochastic.Decomposition.CompensatorL2.CommonHilbertConvexification

/-!
# A common almost-everywhere subsequence for square-integrable rows

This module is the square-integrable adapter for the source-independent
common diagonal certificate.  The same strictly increasing cutoff is used
for the terminal residual and every coordinate on the stopped right-dense
skeleton.  The Jordan consumer below stops at this finite-grid certificate;
it does not construct a càdlàg candidate or a predictable process.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  {V : Process Ω} {T : NNReal}

open SquareIntegrableIncreasingProcessData

/-! The public square-integrable certificate is an abbreviation for the
source-independent one.  In particular, all selected-row laws are retained
from the common Hilbert certificate. -/

abbrev SquareIntegrableIncreasingProcessCommonAESubsequenceData
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
    (cutoff : Nat → Nat) : Prop :=
  CommonHilbertRowsData.CommonAESubsequenceData
    (squareIntegrableCommonHilbertRowsData hV hRows hControl hResidual)
    w y hCommon cutoff

theorem squareIntegrableIncreasingProcessCommonAESubsequence_producer
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
      hV hRows hControl hResidual w y) :
    ∃ cutoff : Nat → Nat,
      SquareIntegrableIncreasingProcessCommonAESubsequenceData
        hV hRows hControl hResidual w y hCommon cutoff := by
  exact CommonHilbertRowsData.commonAESubsequence_producer
    (h := squareIntegrableCommonHilbertRowsData hV hRows hControl hResidual)
    w y hCommon

/-! ## The two-Jordan direct consumer

The existential package is written directly so that the source endpoint
added with the L² rows remains the actual consumer. -/

theorem exists_squareIntegrableCommonAESubsequences_of_commonStopJordanComponents
    {S : Process Ω}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {T : NNReal} {alpha : Ω → WithTop NNReal}
    {hAlphaStop : IsStoppingTime F alpha}
    {selection : Nat → Nat} {N B : Nat → Process Ω}
    {Vbound : Ω → Real} {L : Real}
    {hUsual : Filtration.UsualConditions mu F}
    {data : CommonStoppedRowsUniformAnalyticData (S := S) T alpha hAlphaStop
      selection N B Vbound L hUsual}
    {v : ∀ n, TailConvexWeights n} {Z : Lp Real 2 mu}
    {Nbar Bbar Xbar : Nat → Process Ω} {M : Process Ω} {cutoff : Nat → Nat}
    {A : Process Ω}
    (hNested : CommonStoppedRowsUniformAnalyticNestedGridVariationData
      data v Z Nbar Bbar Xbar M cutoff)
    (bad : Set Ω) (Atilde Aplus Aminus cumulativeVariation : Process Ω)
    (hReg : CommonStoppedRowsUniformAnalyticRegularizedRawFiniteVariationData
      hNested A bad Atilde Aplus Aminus cumulativeVariation) :
    ∃ hPlus : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) Aplus T,
      ∃ hRowsPlus : SquareIntegrableIncreasingProcessCompensatorRowsData
          (F := F) (mu := mu) hPlus,
        ∃ hControlPlus : SquareIntegrableIncreasingProcessCompensatorRowControlData
            (F := F) (mu := mu) hPlus hRowsPlus,
          ∃ hResidualPlus : ∀ r,
              SquareIntegrableFactorialGridSampledResidualMartingaleData
                (F := F) (mu := mu) hPlus hRowsPlus hControlPlus r,
            ∃ wPlus yPlus hCommonPlus cutoffPlus,
              SquareIntegrableIncreasingProcessCommonAESubsequenceData
                hPlus hRowsPlus hControlPlus hResidualPlus wPlus yPlus hCommonPlus
                  cutoffPlus ∧
      ∃ hMinus : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) Aminus T,
        ∃ hRowsMinus : SquareIntegrableIncreasingProcessCompensatorRowsData
            (F := F) (mu := mu) hMinus,
          ∃ hControlMinus : SquareIntegrableIncreasingProcessCompensatorRowControlData
              (F := F) (mu := mu) hMinus hRowsMinus,
            ∃ hResidualMinus : ∀ r,
                SquareIntegrableFactorialGridSampledResidualMartingaleData
                  (F := F) (mu := mu) hMinus hRowsMinus hControlMinus r,
              ∃ wMinus yMinus hCommonMinus cutoffMinus,
                SquareIntegrableIncreasingProcessCommonAESubsequenceData
                  hMinus hRowsMinus hControlMinus hResidualMinus wMinus yMinus hCommonMinus
                    cutoffMinus := by
  obtain ⟨hPlus, hRowsPlus, hControlPlus, hResidualPlus, wPlus, yPlus,
      hCommonPlus, hMinus, hRowsMinus, hControlMinus, hResidualMinus,
      wMinus, yMinus, hCommonMinus⟩ :=
    exists_squareIntegrableCommonHilbertConvexifications_of_commonStopJordanComponents
      (F := F) (mu := mu) hNested bad Atilde Aplus Aminus cumulativeVariation hReg
  obtain ⟨cutoffPlus, hDataPlus⟩ :=
    squareIntegrableIncreasingProcessCommonAESubsequence_producer
      (F := F) (mu := mu) hPlus hRowsPlus hControlPlus hResidualPlus
        wPlus yPlus hCommonPlus
  obtain ⟨cutoffMinus, hDataMinus⟩ :=
    squareIntegrableIncreasingProcessCommonAESubsequence_producer
      (F := F) (mu := mu) hMinus hRowsMinus hControlMinus hResidualMinus
        wMinus yMinus hCommonMinus
  exact ⟨hPlus, hRowsPlus, hControlPlus, hResidualPlus, wPlus, yPlus,
    hCommonPlus, cutoffPlus, hDataPlus, hMinus, hRowsMinus, hControlMinus,
    hResidualMinus, wMinus, yMinus, hCommonMinus, cutoffMinus, hDataMinus⟩

end HorizonFactorialGrid

end FTAPTheorem42
