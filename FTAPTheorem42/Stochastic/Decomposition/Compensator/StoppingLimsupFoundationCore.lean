/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.PredictableLimsupCore
import FTAPTheorem42.Stochastic.Decomposition.Compensator.CandidateOptionalSamplingCore
import FTAPTheorem42.Stochastic.Decomposition.Compensator.StoppingConvexExpectationCore
import FTAPTheorem42.Stochastic.Predictable.PredictableStoppingGraph

/-!
# Source-independent preparation for the stopping-time limsup passage

This module contains the data-level preparation immediately before the
terminal-difference Fatou argument.  It only sees a `CommonHilbertRowsData`
instance, the common diagonal/càdlàg/regularization certificates, and the two
explicit stopping-time expectation certificates.  In particular, no
deterministic source bound, optional-sampling theorem, stopped limsup equality,
or jump-passage argument is used here.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {T : NNReal}
  {source : Ω → Real} {row : Nat → Process Ω}
  {residual : Nat → Ω → Real} {sourceBound rowBound : Real}

namespace CommonHilbertRowsData

/-! ## The terminal difference -/

/-- Difference between a terminal convex row and the same row sampled at a
bounded stopping time. -/
noncomputable def terminalDifference
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : ∀ n, TailConvexWeights n) (τ : Ω → NNReal)
    (cutoff : Nat → Nat) (n : Nat) : Ω → Real :=
  fun omega => h.convexRow (w (cutoff n)) T omega -
    h.convexRow (w (cutoff n)) (τ omega) omega

/-! ## Explicit stopping-time expectation data -/

/-- The part of the stopping-time convex-expectation certificate needed by the
terminal-difference preparation.  The finite-row construction and its source
specific optional-sampling certificates are retained by the adapters, while
this interface exposes the actual row integrability and limiting expectation
used below. -/
structure StoppingConvexExpectationCertificate
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : ∀ n, TailConvexWeights n) (cutoff : Nat → Nat)
    (X : Process Ω) (τ : Ω → NNReal) : Prop where
  row_integrable : ∀ n, Integrable
    (fun omega => h.convexRow (w (cutoff n)) (τ omega) omega) mu
  integral_tendsto : Tendsto
    (fun n => ∫ omega, h.convexRow (w (cutoff n)) (τ omega) omega ∂mu)
    atTop (𝓝 (∫ omega, X (τ omega) omega ∂mu))

/-! ## The terminal `L²` bridge -/

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
theorem preg_terminal_memLp_two_of_cadlagMonotoneRegularization
    {h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound}
    {w : ∀ n, TailConvexWeights n}
    {y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal)}
    {hCommon : CommonHilbertConvexificationData h w y}
    {source_valueToLp : NNReal → Lp Real (2 : ENNReal) mu}
    {X : Process Ω}
    {hSource : CadlagCandidateSourceData h w y hCommon source_valueToLp X}
    {Z : Lp Real 2 mu} {M Pcad : Process Ω}
    (hCad : CadlagCandidateData h w y hCommon source_valueToLp X hSource Z M Pcad)
    {bad : Set Ω} {Preg : Process Ω}
    (hReg : CadlagMonotoneRegularizationData hCad bad Preg) :
    MemLp (Preg T) (2 : ENNReal) mu := by
  let terminal := stoppedLimitTerminalIndex T
  let L : Lp Real 2 mu := h.coordinateLimit y (terminal + 1)
  have hPcad : Pcad T =ᵐ[mu] (L : Ω → Real) := by
    simpa only [terminal, L, stoppedLimitSkeleton_terminalIndex] using
      hCad.Pcad_skeleton terminal
  have hPcadMem : MemLp (Pcad T) (2 : ENNReal) mu :=
    (memLp_congr_ae hPcad).mpr (Lp.memLp L)
  exact (memLp_congr_ae (hReg.Preg_indistinguishable.eventuallyEq_at T)).mpr
    hPcadMem

/-! ## Nonnegativity of the raw predictable limsup -/

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
private theorem predictableLimsup_nonnegative_of_commonSubsequence
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : ∀ n, TailConvexWeights n)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal))
    (hCommon : CommonHilbertConvexificationData h w y)
    (cutoff : Nat → Nat)
    (hData : CommonAESubsequenceData h w y hCommon cutoff)
    {source_valueToLp : NNReal → Lp Real (2 : ENNReal) mu}
    {X : Process Ω}
    {hSource : CadlagCandidateSourceData h w y hCommon source_valueToLp X}
    {Z : Lp Real 2 mu} {M Pcad : Process Ω}
    (hCad : CadlagCandidateData h w y hCommon source_valueToLp X hSource Z M Pcad)
    {bad : Set Ω} {Preg : Process Ω}
    (hReg : CadlagMonotoneRegularizationData hCad bad Preg) :
    ∀ᵐ omega ∂mu, ∀ t,
      0 ≤ predictableLimsup h w cutoff t omega := by
  have hPregSkeleton (j : Nat) :
      Preg (stoppedLimitSkeleton T j).1 =ᵐ[mu]
        (h.coordinateLimit y (j + 1) : Ω → Real) := by
    exact (hReg.Preg_indistinguishable.eventuallyEq_at
      (stoppedLimitSkeleton T j).1).trans (hCad.Pcad_skeleton j)
  have hSkeletonToPreg : ∀ᵐ omega ∂mu, ∀ j,
      Tendsto (fun n => h.convexRow (w (cutoff n))
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

/-! ## The source-independent foundation certificate -/

structure StoppingLimsupFoundationData
    {h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound}
    {w : ∀ n, TailConvexWeights n}
    {y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal)}
    {hCommon : CommonHilbertConvexificationData h w y}
    {cutoff : Nat → Nat}
    {hData : CommonAESubsequenceData h w y hCommon cutoff}
    {source_valueToLp : NNReal → Lp Real (2 : ENNReal) mu}
    {X : Process Ω}
    {hSource : CadlagCandidateSourceData h w y hCommon source_valueToLp X}
    {Z : Lp Real 2 mu} {M Pcad : Process Ω}
    (hCad : CadlagCandidateData h w y hCommon source_valueToLp X hSource Z M Pcad)
    {bad : Set Ω} {Preg : Process Ω}
    (hReg : CadlagMonotoneRegularizationData hCad bad Preg)
    (Ppred : Process Ω)
    (hLimsup : PredictableLimsupData hCad hReg cutoff hData Ppred)
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun omega => (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T)
    (hStop : StoppingConvexExpectationCertificate h w cutoff X τ)
    (hCandidate : CandidateOptionalSamplingData (F := F) (mu := mu)
      X M Preg τ hτ hτT) : Prop where
  stopping_expectation : StoppingConvexExpectationCertificate h w cutoff X τ
  candidate_optional_sampling : CandidateOptionalSamplingData (F := F) (mu := mu)
    X M Preg τ hτ hτT
  Ppred_nonnegative : ∀ᵐ omega ∂mu, ∀ t, 0 ≤ Ppred t omega
  Ppred_sample_stronglyMeasurable :
    StronglyMeasurable[predictableGraphMeasurableSpace F τ]
      (fun omega => Ppred (τ omega) omega)
  Ppred_sample_aestronglyMeasurable :
    AEStronglyMeasurable (fun omega => Ppred (τ omega) omega) mu
  Ppred_sample_nonnegative : ∀ᵐ omega ∂mu,
    0 ≤ Ppred (τ omega) omega
  Ppred_sample_le_Preg : ∀ᵐ omega ∂mu,
    Ppred (τ omega) omega ≤ Preg (τ omega) omega
  Ppred_sample_integrable :
    Integrable (fun omega => Ppred (τ omega) omega) mu
  terminal_row_integrable : ∀ n, Integrable
    (fun omega => h.convexRow (w (cutoff n)) T omega) mu
  terminal_row_tendstoAE : TendstoAE mu
    (fun n => h.convexRow (w (cutoff n)) T) (Preg T)
  Preg_terminal_memLp_two : MemLp (Preg T) (2 : ENNReal) mu
  Preg_terminal_integrable : Integrable (Preg T) mu
  terminal_row_L2_bound : ∀ n,
    (∫ omega, (h.convexRow (w (cutoff n)) T omega) ^ 2 ∂mu) ≤
      rowBound ^ 2
  terminal_difference_nonnegative : ∀ n omega,
    0 ≤ terminalDifference h w τ cutoff n omega
  terminal_difference_integrable : ∀ n,
    Integrable (terminalDifference h w τ cutoff n) mu

/-! ## Producer -/

omit [SigmaFiniteFiltration mu F] in
theorem stoppingLimsupFoundation_producer
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : ∀ n, TailConvexWeights n)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal))
    (hCommon : CommonHilbertConvexificationData h w y)
    (cutoff : Nat → Nat)
    (hData : CommonAESubsequenceData h w y hCommon cutoff)
    (source_valueToLp : NNReal → Lp Real (2 : ENNReal) mu)
    (X : Process Ω)
    (hSource : CadlagCandidateSourceData h w y hCommon source_valueToLp X)
    (Z : Lp Real 2 mu) (M Pcad : Process Ω)
    (hCad : CadlagCandidateData h w y hCommon source_valueToLp X hSource Z M Pcad)
    (bad : Set Ω) (Preg : Process Ω)
    (hReg : CadlagMonotoneRegularizationData hCad bad Preg)
    (Ppred : Process Ω)
    (hLimsup : PredictableLimsupData hCad hReg cutoff hData Ppred)
    (τ : Ω → NNReal)
    (hτ : IsStoppingTime F (fun omega => (τ omega : WithTop NNReal)))
    (hτT : ∀ omega, τ omega ≤ T)
    (hStop : StoppingConvexExpectationCertificate h w cutoff X τ)
    (hCandidate : CandidateOptionalSamplingData (F := F) (mu := mu)
      X M Preg τ hτ hτT) :
    StoppingLimsupFoundationData hCad hReg Ppred hLimsup τ hτ hτT
      hStop hCandidate := by
  have hPredNonnegative : ∀ᵐ omega ∂mu, ∀ t, 0 ≤ Ppred t omega := by
    rw [hLimsup.Ppred_definition]
    exact predictableLimsup_nonnegative_of_commonSubsequence
      h w y hCommon cutoff hData hCad hReg
  have hSampleStrong :
      StronglyMeasurable[predictableGraphMeasurableSpace F τ]
        (fun omega => Ppred (τ omega) omega) :=
    IsStronglyPredictable.stronglyMeasurable_sampledGraph
      hLimsup.Ppred_isStronglyPredictable τ
  have hSampleAEStrong :
      AEStronglyMeasurable (fun omega => Ppred (τ omega) omega) mu :=
    (hSampleStrong.mono
      (IsStoppingTime.predictableGraphMeasurableSpace_le hτ)).aestronglyMeasurable
  have hSampleNonnegative : ∀ᵐ omega ∂mu,
      0 ≤ Ppred (τ omega) omega := by
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
      (h.coordinateLimit y (stoppedLimitTerminalIndex T + 1) : Ω → Real) := by
    exact (hReg.Preg_indistinguishable.eventuallyEq_at T).trans
      (by simpa only [stoppedLimitSkeleton_terminalIndex] using
        hCad.Pcad_skeleton (stoppedLimitTerminalIndex T))
  have hTerminalRows : ∀ᵐ omega ∂mu, Tendsto
      (fun n => h.convexRow (w (cutoff n)) T omega) atTop
      (𝓝 (Preg T omega)) := by
    filter_upwards [hData.skeleton_tendstoAE (stoppedLimitTerminalIndex T),
      hTerminalPreg] with omega hω hTarget
    simpa only [stoppedLimitSkeleton_terminalIndex, hTarget] using hω
  have hPregTerminalMem : MemLp (Preg T) (2 : ENNReal) mu :=
    preg_terminal_memLp_two_of_cadlagMonotoneRegularization hCad hReg
  have hTerminalIntegrable : ∀ n, Integrable
      (fun omega => h.convexRow (w (cutoff n)) T omega) mu := by
    intro n
    exact (hData.row_terminal_memLp_two n).integrable (by norm_num)
  have hDifferenceNonnegative : ∀ n omega,
      0 ≤ terminalDifference h w τ cutoff n omega := by
    intro n omega
    exact sub_nonneg.mpr (hData.row_mono n omega (hτT omega))
  have hDifferenceIntegrable : ∀ n,
      Integrable (terminalDifference h w τ cutoff n) mu := by
    intro n
    exact (hTerminalIntegrable n).sub (hStop.row_integrable n)
  exact {
    stopping_expectation := hStop
    candidate_optional_sampling := hCandidate
    Ppred_nonnegative := hPredNonnegative
    Ppred_sample_stronglyMeasurable := hSampleStrong
    Ppred_sample_aestronglyMeasurable := hSampleAEStrong
    Ppred_sample_nonnegative := hSampleNonnegative
    Ppred_sample_le_Preg := hSampleLe
    Ppred_sample_integrable := hSampleIntegrable
    terminal_row_integrable := hTerminalIntegrable
    terminal_row_tendstoAE := hTerminalRows
    Preg_terminal_memLp_two := hPregTerminalMem
    Preg_terminal_integrable := hPregTerminalMem.integrable (by norm_num)
    terminal_row_L2_bound := hData.row_terminal_L2_bound
    terminal_difference_nonnegative := hDifferenceNonnegative
    terminal_difference_integrable := hDifferenceIntegrable }

end CommonHilbertRowsData

end HorizonFactorialGrid

end FTAPTheorem42
