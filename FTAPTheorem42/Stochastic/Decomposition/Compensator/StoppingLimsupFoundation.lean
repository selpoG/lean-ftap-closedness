/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.PredictableLimsup
import FTAPTheorem42.Stochastic.Decomposition.Compensator.StoppingConvexExpectation
import FTAPTheorem42.Stochastic.Decomposition.Compensator.CandidateOptionalSampling
import FTAPTheorem42.Stochastic.Predictable.PredictableStoppingGraph

/-!
# Foundation for the stopping-time predictable-limsup argument

This module records the data needed immediately before the terminal-difference
Fatou argument.  It does not identify the predictable limsup with the
regularized càdlàg candidate and it does not construct a jump cover.

The only pathwise order fact added here is nonnegativity of the raw limsup.
The sequence is bounded above at each time by moving to a right-dense skeleton
point where the common subsequence converges to the regularized candidate.
Thus the lower limsup inequality is not hidden in an unproved path-regularity
claim.
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

/-! ## The terminal difference used by Fatou -/

/-- Difference between a terminal convex compensator row and the same row
sampled at a bounded stopping time. -/
noncomputable def predictableCompensatorTerminalDifference
    (w : ∀ n, TailConvexWeights n) (τ : Ω → NNReal)
    (cutoff : Nat → Nat) (n : Nat) : Ω → Real :=
  fun omega =>
    compensatorConvexRow (V := V) (F := F) (mu := mu)
      (T := T) (C := C) (w (cutoff n)) T omega -
      compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w (cutoff n)) (τ omega) omega

/-! ## Dense-skeleton lower bound for the raw limsup -/

omit [SigmaFiniteFiltration mu F] in
private theorem predictableCompensatorLimsup_nonnegative_of_commonSubsequence
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
      hCad bad Preg) :
    ∀ᵐ omega ∂mu, ∀ t,
      0 ≤ predictableCompensatorLimsup w cutoff V F mu T C t omega := by
  have hPregSkeleton (j : Nat) :
      Preg (stoppedLimitSkeleton T j).1 =ᵐ[mu]
        (commonCoordinateLimit C y (j + 1) : Ω → Real) := by
    exact (hReg.Preg_indistinguishable.eventuallyEq_at
      (stoppedLimitSkeleton T j).1).trans (hCad.Pcad_skeleton j)
  have hSkeletonToPreg : ∀ᵐ omega ∂mu, ∀ j,
      Tendsto (fun n => compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w (cutoff n))
          (stoppedLimitSkeleton T j).1 omega) atTop
        (𝓝 (Preg (stoppedLimitSkeleton T j).1 omega)) := by
    rw [ae_all_iff]
    intro j
    filter_upwards [hData.skeleton_tendstoAE j, hPregSkeleton j]
      with omega hConv hTarget
    simpa only [hTarget] using hConv
  exact limsup_nonnegative_of_monotone_skeleton_convergence
    hCommon.skeleton_rightDense hData.row_mono hData.row_constant_after
    hData.row_nonnegative hSkeletonToPreg

/-! ## Public foundation certificate -/

structure FactorialGridPredictableCompensatorStoppingLimsupFoundationData
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
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T)
    (hStop : FactorialGridPredictableCompensatorStoppingConvexExpectationData
      hV hRows hControl hResidual w y hCommon cutoff hData τ hτ hτT)
    (hCandidate : FactorialGridPredictableCompensatorCandidateOptionalSamplingData
      hV hRows hControl hResidual w y hCommon Z M Pcad hCad bad Preg hReg τ hτ hτT) : Prop where
  Ppred_nonnegative : ∀ᵐ omega ∂mu, ∀ t, 0 ≤ Ppred t omega
  Ppred_sample_stronglyMeasurable :
    StronglyMeasurable[predictableGraphMeasurableSpace F τ]
      (fun omega => Ppred (τ omega) omega)
  Ppred_sample_aestronglyMeasurable :
    AEStronglyMeasurable (fun omega => Ppred (τ omega) omega) mu
  Ppred_sample_integrable :
    Integrable (fun omega => Ppred (τ omega) omega) mu
  terminal_row_integrable : ∀ n, Integrable
    (fun omega => compensatorConvexRow (V := V) (F := F) (mu := mu)
      (T := T) (C := C) (w (cutoff n)) T omega) mu
  terminal_row_tendstoAE : TendstoAE mu
    (fun n => compensatorConvexRow (V := V) (F := F) (mu := mu)
      (T := T) (C := C) (w (cutoff n)) T)
    (Preg T)
  Preg_terminal_memLp_two : MemLp (Preg T) (2 : ENNReal) mu
  Preg_terminal_integrable : Integrable (Preg T) mu
  terminal_row_L2_bound : ∀ n,
    (∫ omega, (compensatorConvexRow (V := V) (F := F) (mu := mu)
      (T := T) (C := C) (w (cutoff n)) T omega) ^ 2 ∂mu) ≤
      8 * (C : Real) ^ 2
  terminal_difference_nonnegative : ∀ n omega,
    0 ≤ predictableCompensatorTerminalDifference
      (V := V) (F := F) (mu := mu) (T := T) (C := C) (w := w) τ cutoff n omega
  terminal_difference_integrable : ∀ n,
    Integrable (predictableCompensatorTerminalDifference
      (V := V) (F := F) (mu := mu) (T := T) (C := C) (w := w) τ cutoff n) mu

omit [SigmaFiniteFiltration mu F] in
theorem factorialGridPredictableCompensatorStoppingLimsupFoundation_producer
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
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun omega =>
      (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T)
    (hStop : FactorialGridPredictableCompensatorStoppingConvexExpectationData
      hV hRows hControl hResidual w y hCommon cutoff hData τ hτ hτT)
    (hCandidate : FactorialGridPredictableCompensatorCandidateOptionalSamplingData
      hV hRows hControl hResidual w y hCommon Z M Pcad hCad bad Preg hReg τ hτ hτT) :
    FactorialGridPredictableCompensatorStoppingLimsupFoundationData
      hV hRows hControl hResidual w y hCommon cutoff hData
        Z M Pcad hCad bad Preg hReg Ppred hLimsup τ hτ hτT hStop hCandidate := by
  have hPredNonnegative : ∀ᵐ omega ∂mu, ∀ t, 0 ≤ Ppred t omega := by
    rw [hLimsup.Ppred_definition]
    exact predictableCompensatorLimsup_nonnegative_of_commonSubsequence
      (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon cutoff hData
        Z M Pcad hCad bad Preg hReg
  have hSampleStrong :
      StronglyMeasurable[predictableGraphMeasurableSpace F τ]
        (fun omega => Ppred (τ omega) omega) :=
    IsStronglyPredictable.stronglyMeasurable_sampledGraph
      hLimsup.Ppred_isStronglyPredictable τ
  have hSampleAEStrong :
      AEStronglyMeasurable (fun omega => Ppred (τ omega) omega) mu :=
    (hSampleStrong.mono
      (IsStoppingTime.predictableGraphMeasurableSpace_le hτ)).aestronglyMeasurable
  have hSampleNonnegative : ∀ᵐ omega ∂mu, 0 ≤ Ppred (τ omega) omega := by
    filter_upwards [hPredNonnegative] with omega hω
    exact hω (τ omega)
  have hSampleLe : ∀ᵐ omega ∂mu,
      Ppred (τ omega) omega ≤ Preg (τ omega) omega := by
    filter_upwards [hLimsup.Ppred_le_Preg] with omega hω
    exact hω (τ omega)
  have hSampleIntegrable :
      Integrable (fun omega => Ppred (τ omega) omega) mu :=
    hCandidate.candidate_sample_integrable.mono_nonneg
      hSampleAEStrong hSampleNonnegative hSampleLe
  have hTerminalPreg : Preg T =ᵐ[mu]
      (commonCoordinateLimit C y (stoppedLimitTerminalIndex T + 1) : Ω → Real) := by
    exact (hReg.Preg_indistinguishable.eventuallyEq_at T).trans
      (by simpa only [stoppedLimitSkeleton_terminalIndex] using
        hCad.Pcad_skeleton (stoppedLimitTerminalIndex T))
  have hTerminalRows : ∀ᵐ omega ∂mu, Tendsto
      (fun n => compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w (cutoff n)) T omega) atTop
      (𝓝 (Preg T omega)) := by
    filter_upwards [hData.skeleton_tendstoAE (stoppedLimitTerminalIndex T),
      hTerminalPreg] with omega hω hTarget
    simpa only [stoppedLimitSkeleton_terminalIndex, hTarget] using hω
  have hPregTerminalMem : MemLp (Preg T) (2 : ENNReal) mu :=
    preg_terminal_memLp_two_of_commonCadlagRegularization
      (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon
        Z M Pcad hCad bad Preg hReg
  have hTerminalIntegrable : ∀ n, Integrable
      (fun omega => compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w (cutoff n)) T omega) mu := by
    intro n
    exact (hData.row_terminal_memLp_two n).integrable (by norm_num)
  have hDifferenceNonnegative : ∀ n omega,
      0 ≤ predictableCompensatorTerminalDifference
        (V := V) (F := F) (mu := mu) (T := T) (C := C) (w := w) τ cutoff n omega := by
    intro n omega
    exact sub_nonneg.mpr (hData.row_mono n omega (hτT omega))
  have hDifferenceIntegrable : ∀ n,
      Integrable (predictableCompensatorTerminalDifference
        (V := V) (F := F) (mu := mu) (T := T) (C := C) (w := w) τ cutoff n) mu := by
    intro n
    exact (hTerminalIntegrable n).sub (hStop.compensator_integrable n)
  exact {
    Ppred_nonnegative := hPredNonnegative
    Ppred_sample_stronglyMeasurable := hSampleStrong
    Ppred_sample_aestronglyMeasurable := hSampleAEStrong
    Ppred_sample_integrable := hSampleIntegrable
    terminal_row_integrable := hTerminalIntegrable
    terminal_row_tendstoAE := hTerminalRows
    Preg_terminal_memLp_two := hPregTerminalMem
    Preg_terminal_integrable := hPregTerminalMem.integrable (by norm_num)
    terminal_row_L2_bound := hData.row_terminal_L2_bound
    terminal_difference_nonnegative := hDifferenceNonnegative
    terminal_difference_integrable := hDifferenceIntegrable }

end HorizonFactorialGrid

end FTAPTheorem42
