/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.CompensatorL2.DualProjection

/-!
# Coherent packages for one square-integrable increasing process

This module is the generic producer for the one-component package.  All
choices made by the finite-grid construction are threaded through the
subsequent consumers: rows, row control, residual martingales, Hilbert
convexification, the common a.e. cutoff, the càdlàg candidate, its monotone
regularization, and the predictable limsup are selected once.  In
particular, later stopping-time or projection consumers do not make a new
existential choice.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]

open SquareIntegrableIncreasingProcessData

/-! The producer is deliberately stated for an arbitrary
square-integrable increasing process.  No bounded-source wrapper is used. -/

omit [SigmaFiniteFiltration mu F] in
theorem exists_squareIntegrablePredictableCompensatorComponentPackage
    {V : Process Ω} {T : NNReal}
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hUsual : Filtration.UsualConditions mu F) :
    Nonempty
      (SquareIntegrablePredictableCompensatorComponentPackage
        (F := F) (mu := mu) V T) := by
  obtain ⟨hRows⟩ :=
    exists_factorialGridSquareIntegrableIncreasingCompensatorRows
      (F := F) (mu := mu) hV
  obtain ⟨hControl⟩ :=
    exists_squareIntegrableIncreasingProcessCompensatorRowControl
      (F := F) (mu := mu) hV hRows
  let hResidual : ∀ r,
      SquareIntegrableFactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows hControl r := fun r =>
    Classical.choice
      (exists_squareIntegrableFactorialGridSampledResidualMartingale
        (F := F) (mu := mu) hV hRows hControl r)
  obtain ⟨w, y, hCommon⟩ :=
    squareIntegrableIncreasingProcessCommonHilbertConvexification_producer
      (F := F) (mu := mu) hV hRows hControl hResidual
  obtain ⟨cutoff, hData⟩ :=
    squareIntegrableIncreasingProcessCommonAESubsequence_producer
      (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon
  obtain ⟨Z, M, Pcad, hCad⟩ :=
    exists_squareIntegrableIncreasingProcessCadlagCandidate
      (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon hUsual
  obtain ⟨bad, Preg, hReg⟩ :=
    exists_squareIntegrableIncreasingProcessCadlagMonotoneRegularization
      (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon
        cutoff hData Z M Pcad hCad hUsual
  let Ppred : Process Ω :=
    squareIntegrablePredictableCompensatorLimsup
      hV hRows hControl hResidual w cutoff
  have hLimsup :
      SquareIntegrableIncreasingProcessPredictableLimsupData
        hV hRows hControl hResidual w y hCommon cutoff hData
          Z M Pcad hCad bad Preg hReg Ppred := by
    exact exists_squareIntegrableIncreasingProcessPredictableLimsup
      (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon
        cutoff hData Z M Pcad hCad bad Preg hReg
  exact ⟨{
    hV := hV
    hRows := hRows
    hControl := hControl
    hResidual := hResidual
    w := w
    y := y
    hCommon := hCommon
    cutoff := cutoff
    hData := hData
    Z := Z
    M := M
    Pcad := Pcad
    hCad := hCad
    bad := bad
    Preg := Preg
    hReg := hReg
    Ppred := Ppred
    hLimsup := hLimsup }⟩

/-! The generic producer is immediately consumed by the projection endpoint.
The returned projection data still contains the fixed package, so its
terminal and residual assertions refer to the same rows and candidate. -/

omit [SigmaFiniteFiltration mu F] in
theorem exists_squareIntegrablePredictableCompensatorDualProjection
    {V : Process Ω} {T : NNReal}
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hUsual : Filtration.UsualConditions mu F) :
    ∃ pkg : SquareIntegrablePredictableCompensatorComponentPackage
        (F := F) (mu := mu) V T,
      ∃ badPred : Set Ω, ∃ Vp : Process Ω,
        SquareIntegrablePredictableCompensatorDualProjectionData
          pkg badPred Vp := by
  obtain ⟨pkg⟩ :=
    exists_squareIntegrablePredictableCompensatorComponentPackage
      (F := F) (mu := mu) hV hUsual
  obtain ⟨badPred, Vp, hProjection⟩ := pkg.dualProjection hUsual
  exact ⟨pkg, badPred, Vp, hProjection⟩

end HorizonFactorialGrid

end FTAPTheorem42
