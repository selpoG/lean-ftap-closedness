/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.StoppingLimsupFoundation
import FTAPTheorem42.Stochastic.Decomposition.Compensator.StoppingLimsupEqualityCore

/-!
# Stopped equality for the predictable compensator limsup

This module is the terminal-difference Fatou consumer.  It specializes the
scalar liminf calculation to the common compensator rows and uses Fatou only
for the nonnegative terminal differences.  No general reverse-Fatou theorem,
section theorem, or process-level indistinguishability is introduced here.
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

/-! ## Data retained by the stopped equality consumer -/

structure FactorialGridPredictableCompensatorStoppingLimsupEqualityData
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
      hV hRows hControl hResidual w y hCommon Z M Pcad hCad bad Preg hReg τ hτ hτT)
    (hFoundation : FactorialGridPredictableCompensatorStoppingLimsupFoundationData
      hV hRows hControl hResidual w y hCommon cutoff hData
        Z M Pcad hCad bad Preg hReg Ppred hLimsup τ hτ hτT
        hStop hCandidate) : Prop where
  terminal_difference_liminf_eq : ∀ᵐ omega ∂mu,
    liminf (fun n => predictableCompensatorTerminalDifference
      (V := V) (F := F) (mu := mu) (T := T) (C := C) (w := w) τ cutoff n omega)
      atTop = Preg T omega - Ppred (τ omega) omega
  terminal_difference_integral_le :
    (∫ omega, liminf (fun n => predictableCompensatorTerminalDifference
      (V := V) (F := F) (mu := mu) (T := T) (C := C) (w := w) τ cutoff n omega)
      atTop ∂mu) ≤
      (∫ omega, Preg T omega ∂mu) -
        ∫ omega, Preg (τ omega) omega ∂mu
  stopped_sample_ae_eq :
    (fun omega => Ppred (τ omega) omega) =ᵐ[mu]
      (fun omega => Preg (τ omega) omega)

/-! ## The bounded adapter for the source-independent consumer -/

omit [SigmaFiniteFiltration mu F] in
private theorem bounded_stoppingLimsupEquality_core
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
      hV hRows hControl hResidual w y hCommon Z M Pcad hCad bad Preg hReg τ hτ hτT)
    (hFoundation : FactorialGridPredictableCompensatorStoppingLimsupFoundationData
      hV hRows hControl hResidual w y hCommon cutoff hData
        Z M Pcad hCad bad Preg hReg Ppred hLimsup τ hτ hτT hStop hCandidate) :
    FactorialGridPredictableCompensatorStoppingLimsupEqualityData
      hV hRows hControl hResidual w y hCommon cutoff hData
        Z M Pcad hCad bad Preg hReg Ppred hLimsup τ hτ hτT hStop hCandidate
        hFoundation := by
  let h := boundedCommonHilbertRowsData (F := F) (mu := mu)
    hV hRows hControl
  let hCore := boundedCommonHilbertConvexificationCoreData
    hV hRows hControl hResidual w y hCommon
  let source_valueToLp := boundedCadlagCandidateSourceValueToLp
    (F := F) (mu := mu) hV
  let hSource := boundedCadlagCandidateSourceData
    hV hRows hControl hResidual w y hCommon
  have hCommonCore :
      CommonHilbertRowsData.CommonHilbertConvexificationData h w y :=
    boundedCommonHilbertConvexificationCoreData
      (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon
  have hCadCore :
      CommonHilbertRowsData.CadlagCandidateData h w y hCore
        source_valueToLp V hSource Z M Pcad := by
    exact {
      terminalLimit_eq := hCad.terminalLimit_eq
      terminal_residual_tendsto := hCad.terminal_residual_tendsto
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
      Pcad_skeleton := hCad.Pcad_skeleton }
  have hRegCore :
      CommonHilbertRowsData.CadlagMonotoneRegularizationData
        hCadCore bad Preg := by
    exact {
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
  have hConvexRowEq : ∀ {n : Nat} (ww : TailConvexWeights n),
      h.convexRow ww = compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) ww := by
    intro n ww
    rfl
  have hResidualConvexRowEq : ∀ {n : Nat} (ww : TailConvexWeights n),
      h.residualConvexRow ww = residualConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) ww := by
    intro n ww
    rfl
  have hLimitEq (i : Nat) : h.coordinateLimit y i =
      commonCoordinateLimit C y i := by
    rfl
  have hDataCore : CommonHilbertRowsData.CommonAESubsequenceData
      h w y hCommonCore cutoff := by
    refine {
      cutoff_strictMono := hData.cutoff_strictMono
      coordinate_tendstoAE := ?_
      residual_tendstoAE := ?_
      skeleton_tendstoAE := ?_
      weights_tail := hData.weights_tail
      weights_nonnegative := hData.weights_nonnegative
      weights_sum_eq_one := hData.weights_sum_eq_one
      row_isStronglyPredictable := ?_
      row_zero := ?_
      row_nonnegative := ?_
      row_mono := ?_
      row_leftContinuous := ?_
      row_constant_after := ?_
      row_terminal_memLp_two := ?_
      row_terminal_L2_bound := ?_
      row_terminal_expectation := ?_
      residual_row_memLp_two := ?_
      residual_row_eq_source_sub_compensator := ?_ }
    · intro i
      cases i with
      | zero =>
          change TendstoAE mu
            (fun n => h.residualConvexRow (w (cutoff n)))
            (h.coordinateLimit y 0 : Ω → Real)
          convert hData.residual_tendstoAE using 1
          · funext n
            exact hResidualConvexRowEq (w (cutoff n))
          · exact congrArg (fun z : Lp Real (2 : ENNReal) mu =>
              (z : Ω → Real)) (hLimitEq 0)
      | succ j =>
          change TendstoAE mu
            (fun n => h.convexRow (w (cutoff n))
              (stoppedLimitSkeleton T j).1)
            (h.coordinateLimit y (j + 1) : Ω → Real)
          convert hData.skeleton_tendstoAE j using 1
          · funext n
            exact congrFun (hConvexRowEq (w (cutoff n)))
              (stoppedLimitSkeleton T j).1
          · exact congrArg (fun z : Lp Real (2 : ENNReal) mu =>
              (z : Ω → Real)) (hLimitEq (j + 1))
    · convert hData.residual_tendstoAE using 1
      · funext n
        rfl
      · exact congrArg (fun z : Lp Real (2 : ENNReal) mu =>
          (z : Ω → Real)) (hLimitEq 0)
    · intro j
      convert hData.skeleton_tendstoAE j using 1
      · funext n
        exact congrFun (hConvexRowEq (w (cutoff n)))
          (stoppedLimitSkeleton T j).1
      · exact congrArg (fun z : Lp Real (2 : ENNReal) mu =>
          (z : Ω → Real)) (hLimitEq (j + 1))
    · intro n
      rw [hConvexRowEq]
      exact hData.row_isStronglyPredictable n
    · intro n
      rw [hConvexRowEq]
      exact hData.row_zero n
    · intro n t omega
      rw [hConvexRowEq]
      exact hData.row_nonnegative n t omega
    · intro n omega
      rw [hConvexRowEq]
      exact hData.row_mono n omega
    · intro n omega t
      rw [hConvexRowEq]
      exact hData.row_leftContinuous n omega t
    · intro n omega t ht
      rw [hConvexRowEq]
      exact hData.row_constant_after n omega t ht
    · intro n
      rw [hConvexRowEq]
      exact hData.row_terminal_memLp_two n
    · intro n
      rw [hConvexRowEq]
      change (∫ omega, h.convexRow (w (cutoff n)) T omega ^ 2 ∂mu) ≤
        (Real.sqrt (8 * (C : Real) ^ 2)) ^ 2
      rw [Real.sq_sqrt (by positivity)]
      exact hData.row_terminal_L2_bound n
    · intro n
      exact hCore.row_terminal_expectation (cutoff n)
    · intro n
      rw [hResidualConvexRowEq]
      exact hData.residual_row_memLp_two n
    · intro n
      rw [hResidualConvexRowEq, hConvexRowEq]
      exact hData.residual_row_eq_source_sub_compensator n
  have hStopCore : CommonHilbertRowsData.StoppingConvexExpectationCertificate
      h w cutoff V τ := by
    refine {
      row_integrable := ?_
      integral_tendsto := hStop.integral_tendsto }
    intro n
    exact hStop.compensator_integrable n
  have hCandidateCore : CandidateOptionalSamplingData (F := F) (mu := mu)
      V M Preg τ hτ hτT := {
    source_sample_integrable := hCandidate.source_sample_integrable
    martingale_sample_integrable := hCandidate.martingale_sample_integrable
    candidate_sample_integrable := hCandidate.candidate_sample_integrable
    martingale_sample_integral_eq_zero := hCandidate.martingale_sample_integral_eq_zero
    candidate_sample_integral_eq_source := hCandidate.candidate_sample_integral_eq_source }
  have hTerminalCandidateSpec :=
    (factorialGridPredictableCompensatorCandidateOptionalSampling_producer
      (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon Z M Pcad
      hCad bad Preg hReg (fun _ : Ω => T) (isStoppingTime_const F T)
        (fun _ => le_rfl)).some
  have hTerminalCandidateCore : CandidateOptionalSamplingData (F := F) (mu := mu)
      V M Preg (fun _ : Ω => T) (isStoppingTime_const F T) (fun _ => le_rfl) := {
    source_sample_integrable := hTerminalCandidateSpec.source_sample_integrable
    martingale_sample_integrable := hTerminalCandidateSpec.martingale_sample_integrable
    candidate_sample_integrable := hTerminalCandidateSpec.candidate_sample_integrable
    martingale_sample_integral_eq_zero :=
      hTerminalCandidateSpec.martingale_sample_integral_eq_zero
    candidate_sample_integral_eq_source :=
      hTerminalCandidateSpec.candidate_sample_integral_eq_source }
  have hPpredEq : Ppred = CommonHilbertRowsData.predictableLimsup h w cutoff := by
    rw [hLimsup.Ppred_definition]
    funext t omega
    dsimp [predictableCompensatorLimsup,
      CommonHilbertRowsData.predictableLimsup]
    apply limsup_congr
    exact Filter.Eventually.of_forall fun n =>
      congrFun (congrFun (hConvexRowEq (w (cutoff n))) t) omega |>.symm
  have hLimsupCore : CommonHilbertRowsData.PredictableLimsupData
      hCadCore hRegCore cutoff hDataCore Ppred := {
    Ppred_definition := hPpredEq
    Ppred_isStronglyPredictable := hLimsup.Ppred_isStronglyPredictable
    Ppred_le_Preg := hLimsup.Ppred_le_Preg
    Ppred_eq_Preg_at_continuity := hLimsup.Ppred_eq_Preg_at_continuity
    Ppred_zero := hLimsup.Ppred_zero
    Ppred_constant_after := hLimsup.Ppred_constant_after }
  have hDifferenceEq (n : Nat) :
      CommonHilbertRowsData.terminalDifference h w τ cutoff n =
        predictableCompensatorTerminalDifference
          (V := V) (F := F) (mu := mu) (T := T) (C := C)
          (w := w) τ cutoff n := by
    funext omega
    dsimp [CommonHilbertRowsData.terminalDifference,
      predictableCompensatorTerminalDifference]
    rw [congrFun (hConvexRowEq (w (cutoff n))) T,
      congrFun (hConvexRowEq (w (cutoff n))) (τ omega)]
  have hLiminfEq :
      (fun omega => liminf (fun n =>
        CommonHilbertRowsData.terminalDifference h w τ cutoff n omega) atTop) =
        (fun omega => liminf (fun n =>
          predictableCompensatorTerminalDifference
            (V := V) (F := F) (mu := mu) (T := T) (C := C)
            (w := w) τ cutoff n omega) atTop) := by
    funext omega
    apply liminf_congr
    exact Filter.Eventually.of_forall fun n =>
      congrFun (hDifferenceEq n) omega
  have hFoundationCore : CommonHilbertRowsData.StoppingLimsupFoundationData
      hCadCore hRegCore Ppred hLimsupCore τ hτ hτT hStopCore hCandidateCore := by
    refine {
      stopping_expectation := hStopCore
      candidate_optional_sampling := hCandidateCore
      Ppred_nonnegative := hFoundation.Ppred_nonnegative
      Ppred_sample_stronglyMeasurable := hFoundation.Ppred_sample_stronglyMeasurable
      Ppred_sample_aestronglyMeasurable := hFoundation.Ppred_sample_aestronglyMeasurable
      Ppred_sample_nonnegative := ?_
      Ppred_sample_le_Preg := ?_
      Ppred_sample_integrable := hFoundation.Ppred_sample_integrable
      terminal_row_integrable := ?_
      terminal_row_tendstoAE := ?_
      Preg_terminal_memLp_two := hFoundation.Preg_terminal_memLp_two
      Preg_terminal_integrable := hFoundation.Preg_terminal_integrable
      terminal_row_L2_bound := ?_
      terminal_difference_nonnegative := ?_
      terminal_difference_integrable := ?_ }
    · filter_upwards [hFoundation.Ppred_nonnegative] with omega hω
      exact hω (τ omega)
    · filter_upwards [hLimsup.Ppred_le_Preg] with omega hω
      exact hω (τ omega)
    · intro n
      rw [hConvexRowEq]
      exact hFoundation.terminal_row_integrable n
    · convert hFoundation.terminal_row_tendstoAE using 1
      funext n
      exact congrFun (hConvexRowEq (w (cutoff n))) T
    · intro n
      rw [hConvexRowEq]
      change (∫ omega, h.convexRow (w (cutoff n)) T omega ^ 2 ∂mu) ≤
        (Real.sqrt (8 * (C : Real) ^ 2)) ^ 2
      rw [Real.sq_sqrt (by positivity)]
      exact hFoundation.terminal_row_L2_bound n
    · intro n omega
      rw [hDifferenceEq]
      exact hFoundation.terminal_difference_nonnegative n omega
    · intro n
      rw [hDifferenceEq]
      exact hFoundation.terminal_difference_integrable n
  have hEqualityCore := CommonHilbertRowsData.stoppingLimsupEquality_producer
    (h := h) (w := w) (y := y) (hCommon := hCommonCore)
    (cutoff := cutoff) (hData := hDataCore)
    (source_valueToLp := source_valueToLp) (X := V) (hSource := hSource)
    (Z := Z) (M := M) (Pcad := Pcad) hCadCore (bad := bad) (Preg := Preg)
    hRegCore Ppred hLimsupCore τ hτ hτT hStopCore hCandidateCore
    hTerminalCandidateCore hFoundationCore
  refine {
    terminal_difference_liminf_eq := ?_
    terminal_difference_integral_le := ?_
    stopped_sample_ae_eq := ?_ }
  · filter_upwards [hEqualityCore.terminal_difference_liminf_eq]
      with omega hEq
    rw [← congrFun hLiminfEq omega]
    exact hEq
  · rw [← hLiminfEq]
    exact hEqualityCore.terminal_difference_integral_le
  · simpa only [hPpredEq] using hEqualityCore.stopped_sample_ae_eq

/-! ## The terminal-difference consumer -/

omit [SigmaFiniteFiltration mu F] in
theorem factorialGridPredictableCompensatorStoppingLimsupEquality_producer
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
      hV hRows hControl hResidual w y hCommon Z M Pcad hCad bad Preg hReg τ hτ hτT)
    (hFoundation : FactorialGridPredictableCompensatorStoppingLimsupFoundationData
      hV hRows hControl hResidual w y hCommon cutoff hData
        Z M Pcad hCad bad Preg hReg Ppred hLimsup τ hτ hτT hStop hCandidate) :
    FactorialGridPredictableCompensatorStoppingLimsupEqualityData
      hV hRows hControl hResidual w y hCommon cutoff hData
        Z M Pcad hCad bad Preg hReg Ppred hLimsup τ hτ hτT hStop hCandidate
        hFoundation := by
  exact bounded_stoppingLimsupEquality_core
    (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon cutoff hData
      Z M Pcad hCad bad Preg hReg Ppred hLimsup τ hτ hτT hStop hCandidate
      hFoundation

omit [SigmaFiniteFiltration mu F] in
theorem exists_factorialGridPredictableCompensatorStoppingLimsupEquality
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
      hV hRows hControl hResidual w y hCommon Z M Pcad hCad bad Preg hReg τ hτ hτT)
    (hFoundation : FactorialGridPredictableCompensatorStoppingLimsupFoundationData
      hV hRows hControl hResidual w y hCommon cutoff hData
        Z M Pcad hCad bad Preg hReg Ppred hLimsup τ hτ hτT hStop hCandidate) :
    Nonempty (FactorialGridPredictableCompensatorStoppingLimsupEqualityData
      hV hRows hControl hResidual w y hCommon cutoff hData
        Z M Pcad hCad bad Preg hReg Ppred hLimsup τ hτ hτT hStop hCandidate
        hFoundation) := by
  exact ⟨factorialGridPredictableCompensatorStoppingLimsupEquality_producer
    (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon cutoff hData
      Z M Pcad hCad bad Preg hReg Ppred hLimsup τ hτ hτT hStop hCandidate
      hFoundation⟩

end HorizonFactorialGrid

end FTAPTheorem42
