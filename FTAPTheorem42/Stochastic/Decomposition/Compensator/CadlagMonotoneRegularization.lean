/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.CadlagCandidate
import FTAPTheorem42.Stochastic.Decomposition.Compensator.CadlagMonotoneRegularizationCore
import FTAPTheorem42.Stochastic.Decomposition.Compensator.CommonAESubsequenceCore
import FTAPTheorem42.Stochastic.Process.NullSetProcessRegularization
import FTAPTheorem42.Foundations.ProcessIndistinguishable
import FTAPTheorem42.Stochastic.Martingale.Basic.RightContinuousStoppedMartingale

/-!
# Monotone regularization of the càdlàg compensator candidate

The common Hilbert convexification supplies nonnegative increasing rows.  This
file transfers those order properties to the càdlàg candidate on one common
full-measure set.  Right density of the canonical skeleton and right
continuity then give the order properties at every time.  The final version
is obtained by zeroing the exceptional time-zero event; no predictability is
asserted here.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

open BoundedIncreasingProcessData

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {V : Process Ω} {T C : NNReal}

/-! ## The bounded data-level certificate -/

structure FactorialGridPredictableCompensatorCadlagMonotoneRegularizationData
    {hV : BoundedIncreasingProcessData (F := F) V T C}
    {hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV}
    {hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows}
    {hResidual : ∀ r,
      FactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows r}
    {w : ∀ n, TailConvexWeights n}
    {y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu)
      (2 : ENNReal)}
    {hCommon : FactorialGridPredictableCompensatorCommonHilbertConvexificationData
      hV hRows hControl hResidual w y}
    {Z : Lp Real 2 mu} {M Pcad : Process Ω}
    (hCad : FactorialGridPredictableCompensatorCadlagCandidateData
      (F := F) (mu := mu) (T := T) (C := C)
      hV hRows hControl hResidual hCommon Z M Pcad)
    (bad : Set Ω) (Preg : Process Ω) : Prop where
  bad_null : mu bad = 0
  bad_measurable : MeasurableSet[F 0] bad
  Preg_eq_zeroOn : Preg = ProcessNullSetRegularization.zeroOn bad Pcad
  Preg_stronglyAdapted : StronglyAdapted F Preg
  Preg_adapted : Adapted F Preg
  Preg_rightContinuous : ∀ omega t,
    ContinuousWithinAt (Preg · omega) (Ici t) t
  Preg_leftLimits : ProcessHasLeftLimits Preg
  Preg_nonnegative : ∀ omega t, 0 ≤ Preg t omega
  Preg_monotone : ∀ omega, Monotone (Preg · omega)
  Preg_zero : Preg 0 = 0
  Preg_constant_after : ∀ omega t, T ≤ t →
    Preg t omega = Preg T omega
  Preg_indistinguishable : ProcessIndistinguishable mu Preg Pcad

/-! ## Candidate regularization adapter -/

omit [SigmaFiniteFiltration mu F] in
theorem exists_factorialGridPredictableCompensatorCadlagMonotoneRegularization
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
    (Z : Lp Real 2 mu) (M Pcad : Process Ω)
    (hCad : FactorialGridPredictableCompensatorCadlagCandidateData
      (T := T) (C := C) hV hRows hControl hResidual hCommon Z M Pcad)
    (hUsual : Filtration.UsualConditions mu F) :
    ∃ (bad : Set Ω) (Preg : Process Ω),
      FactorialGridPredictableCompensatorCadlagMonotoneRegularizationData
        (T := T) (C := C) hCad bad Preg := by
  let h := boundedCommonHilbertRowsData (F := F) (mu := mu)
    hV hRows hControl
  let hCore := boundedCommonHilbertConvexificationCoreData
    hV hRows hControl hResidual w y hCommon
  let hSource := boundedCadlagCandidateSourceData
    hV hRows hControl hResidual w y hCommon
  let source_valueToLp := boundedCadlagCandidateSourceValueToLp
    (F := F) (mu := mu) hV
  have hCadCore :
      CommonHilbertRowsData.CadlagCandidateData h w y hCore
        source_valueToLp V
        (boundedCadlagCandidateSourceData hV hRows hControl hResidual w y hCommon)
        Z M Pcad := by
    refine {
      terminalLimit_eq := ?_
      terminal_residual_tendsto := ?_
      M_martingale := hCad.M_martingale
      M_rightContinuous := hCad.M_rightContinuous
      M_leftLimits := hCad.M_leftLimits
      M_condExp := hCad.M_condExp
      Pcad_definition := hCad.Pcad_definition
      Pcad_stronglyAdapted := hCad.Pcad_stronglyAdapted
      Pcad_rightContinuous := hCad.Pcad_rightContinuous
      Pcad_leftLimits := hCad.Pcad_leftLimits
      Pcad_zero := hCad.Pcad_zero
      Pcad_constant_after := hCad.Pcad_constant_after
      Pcad_skeleton := ?_ }
    · exact hCad.terminalLimit_eq
    · exact hCad.terminal_residual_tendsto
    · exact hCad.Pcad_skeleton
  obtain ⟨cutoff, hData⟩ :=
    CommonHilbertRowsData.commonAESubsequence_producer h w y hCore
  obtain ⟨bad, Preg, hReg⟩ :=
    CommonHilbertRowsData.exists_cadlagMonotoneRegularization
      h w y hCore source_valueToLp V
      (boundedCadlagCandidateSourceData
        hV hRows hControl hResidual w y hCommon)
      Z M Pcad hCadCore cutoff hData hUsual
  refine ⟨bad, Preg, ?_⟩
  refine {
    bad_null := hReg.bad_null
    bad_measurable := hReg.bad_measurable
    Preg_eq_zeroOn := hReg.Preg_eq_zeroOn
    Preg_stronglyAdapted := hReg.Preg_stronglyAdapted
    Preg_adapted := hReg.Preg_adapted
    Preg_rightContinuous := hReg.Preg_rightContinuous
    Preg_leftLimits := hReg.Preg_leftLimits
    Preg_nonnegative := hReg.Preg_nonnegative
    Preg_monotone := hReg.Preg_monotone
    Preg_zero := hReg.Preg_zero
    Preg_constant_after := hReg.Preg_constant_after
    Preg_indistinguishable := hReg.Preg_indistinguishable }

/-! ## The common-stop Jordan consumer -/

theorem exists_monotoneRegularizedCadlagCandidates_of_commonStopJordanComponents
    {S : Process Ω}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {eta : Real}
    {u : ∀ n, TailConvexWeights n} {selection : Nat → Nat}
    {a : Real} {T : NNReal}
    {alphaSeq : Nat → Ω → WithTop NNReal}
    {alpha : Ω → WithTop NNReal} {R : Ω → Real}
    {hUsual : Filtration.UsualConditions mu F}
    {source : BoundedSemimartingaleSource S F mu}
    (endpoint : CommonStoppedRowsEndpoint
      (S := S) (F := F) (mu := mu) (eta := eta) u selection a T alphaSeq alpha R
      hUsual source)
    {v : ∀ n, TailConvexWeights n} {Z : Lp Real 2 mu}
    {Nbar Bbar Xbar : Nat → Process Ω} {M : Process Ω}
    {cutoff : Nat → Nat}
    {A : Process Ω}
    (bad : Set Ω) (Atilde Aplus Aminus cumulativeVariation : Process Ω)
    (hReg : CommonStopRegularizedRawDecompositionData
      (S := S) (F := F) (mu := mu) (eta := eta)
      (u := u) (selection := selection) (a := a) (T := T)
      (alphaSeq := alphaSeq) (alpha := alpha) (R := R)
      (hUsual := hUsual) (source := source)
      (v := v) (Z := Z) (Nbar := Nbar) (Bbar := Bbar)
      (Xbar := Xbar) (M := M) (cutoff := cutoff) (A := A)
      endpoint bad Atilde Aplus Aminus cumulativeVariation) :
    ∃ hPlus : BoundedIncreasingProcessData (F := F) Aplus T
        (commonStoppedRowsResidualVariationBound a source.bound).toNNReal,
      ∃ hRowsPlus : FactorialGridPredictableCompensatorRowsData
          (F := F) (mu := mu) hPlus,
        ∃ hControlPlus : FactorialGridPredictableCompensatorRowControlData
            (F := F) (mu := mu) hPlus hRowsPlus,
          ∃ hResidualPlus : ∀ r,
              FactorialGridSampledResidualMartingaleData
                (F := F) (mu := mu) hPlus hRowsPlus r,
            ∃ (wPlus : ∀ n, TailConvexWeights n)
              (yPlus : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu)
                (2 : ENNReal)),
              ∃ hCommonPlus :
                FactorialGridPredictableCompensatorCommonHilbertConvexificationData
                  hPlus hRowsPlus hControlPlus hResidualPlus wPlus yPlus,
                ∃ (ZPlus : Lp Real 2 mu) (MPlus PcadPlus : Process Ω),
                  ∃ hCadPlus : FactorialGridPredictableCompensatorCadlagCandidateData
                    hPlus hRowsPlus hControlPlus hResidualPlus
                      hCommonPlus ZPlus MPlus PcadPlus,
                    ∃ (badPlus : Set Ω) (PregPlus : Process Ω),
                      FactorialGridPredictableCompensatorCadlagMonotoneRegularizationData
                        hCadPlus badPlus PregPlus ∧
    ∃ hMinus : BoundedIncreasingProcessData (F := F) Aminus T
        (commonStoppedRowsResidualVariationBound a source.bound).toNNReal,
      ∃ hRowsMinus : FactorialGridPredictableCompensatorRowsData
          (F := F) (mu := mu) hMinus,
        ∃ hControlMinus : FactorialGridPredictableCompensatorRowControlData
            (F := F) (mu := mu) hMinus hRowsMinus,
          ∃ hResidualMinus : ∀ r,
              FactorialGridSampledResidualMartingaleData
                (F := F) (mu := mu) hMinus hRowsMinus r,
            ∃ (wMinus : ∀ n, TailConvexWeights n)
              (yMinus : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu)
                (2 : ENNReal)),
              ∃ hCommonMinus :
                FactorialGridPredictableCompensatorCommonHilbertConvexificationData
                  hMinus hRowsMinus hControlMinus hResidualMinus wMinus yMinus,
                ∃ (ZMinus : Lp Real 2 mu) (MMinus PcadMinus : Process Ω),
                  ∃ hCadMinus : FactorialGridPredictableCompensatorCadlagCandidateData
                    hMinus hRowsMinus hControlMinus hResidualMinus
                      hCommonMinus ZMinus MMinus PcadMinus,
                    ∃ (badMinus : Set Ω) (PregMinus : Process Ω),
                      FactorialGridPredictableCompensatorCadlagMonotoneRegularizationData
                        hCadMinus badMinus PregMinus := by
  obtain ⟨hPlus, hRowsPlus, hControlPlus, hResidualPlus, wPlus, yPlus,
      hCommonPlus, ZPlus, MPlus, PcadPlus, hCadPlus,
      hMinus, hRowsMinus, hControlMinus, hResidualMinus, wMinus, yMinus,
      hCommonMinus, ZMinus, MMinus, PcadMinus, hCadMinus⟩ :=
    exists_cadlagCandidates_of_commonStopJordanComponents
      (F := F) (mu := mu) endpoint bad Atilde Aplus Aminus
        cumulativeVariation hReg
  obtain ⟨badPlus, PregPlus, hRegPlus⟩ :=
    exists_factorialGridPredictableCompensatorCadlagMonotoneRegularization
      hPlus hRowsPlus hControlPlus hResidualPlus wPlus yPlus hCommonPlus
        ZPlus MPlus PcadPlus hCadPlus hUsual
  obtain ⟨badMinus, PregMinus, hRegMinus⟩ :=
    exists_factorialGridPredictableCompensatorCadlagMonotoneRegularization
      hMinus hRowsMinus hControlMinus hResidualMinus wMinus yMinus hCommonMinus
        ZMinus MMinus PcadMinus hCadMinus hUsual
  exact ⟨hPlus, hRowsPlus, hControlPlus, hResidualPlus, wPlus, yPlus,
    hCommonPlus, ZPlus, MPlus, PcadPlus, hCadPlus, badPlus, PregPlus,
    hRegPlus, hMinus, hRowsMinus, hControlMinus, hResidualMinus, wMinus,
    yMinus, hCommonMinus, ZMinus, MMinus, PcadMinus, hCadMinus, badMinus,
    PregMinus, hRegMinus⟩

end HorizonFactorialGrid

end FTAPTheorem42
