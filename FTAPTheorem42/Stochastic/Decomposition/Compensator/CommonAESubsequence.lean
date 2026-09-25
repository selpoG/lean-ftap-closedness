/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.CommonHilbertConvexification
import FTAPTheorem42.Stochastic.Decomposition.Compensator.CommonAESubsequenceCore
import FTAPTheorem42.Stochastic.Compactness.CountableInMeasureDiagonal
import FTAPTheorem42.Stochastic.Decomposition.Compensator.CadlagCandidate
import FTAPTheorem42.Stochastic.Decomposition.Compensator.CadlagMonotoneRegularization

/-!
# One almost-everywhere subsequence for all compensator coordinates

The common Hilbert convexification has one `L²` limit for the terminal
residual and one for every point of the canonical skeleton.  This file makes
the measure-theoretic diagonal step explicit: one strictly increasing
subsequence is chosen once, and that same subsequence converges almost
everywhere in every one of those coordinates.  The rows themselves are not
reconstructed here; all algebraic and pathwise properties are inherited from
the common convexification.

No process-level equality with a càdlàg candidate is asserted in this module.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

open BoundedIncreasingProcessData

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [hSigma : SigmaFiniteFiltration mu F]
  {V : Process Ω} {T C : NNReal}

/-! The bounded API below is an adapter for the source-independent
common-a.e. diagonal certificate. -/

/-! ## The countable family of raw coordinates -/

noncomputable def commonAECoordinateRaw
    (w : ∀ n, TailConvexWeights n)
    (i n : Nat) : Ω → Real :=
  match i with
  | 0 => residualConvexRow (V := V) (F := F) (mu := mu)
      (T := T) (C := C) (w n)
  | j + 1 => compensatorConvexRow (V := V) (F := F) (mu := mu)
      (T := T) (C := C) (w n) (stoppedLimitSkeleton T j).1

noncomputable def commonAECoordinateLimitRaw
    (C : NNReal)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu)
      (2 : ENNReal)) (i : Nat) : Ω → Real :=
  (commonCoordinateLimit C y i : Ω → Real)

omit [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F] in
theorem compensatorConvexRowValueToLp_terminal_eq_coordinate
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (w : TailConvexWeights n) :
    compensatorConvexRowValueToLp hV hRows hControl w T =
      compensatorConvexCoordinateToLp hV hRows hControl w
        (stoppedLimitTerminalIndex T) := by
  apply Lp.ext
  have hLeft := (compensatorConvexRow_value_memLp_two
    (F := F) (mu := mu) hV hRows hControl w T).coeFn_toLp
  have hRight := (compensatorConvexCoordinateToLp_coeFn_ae
    (F := F) (mu := mu) hV hRows hControl w
      (stoppedLimitTerminalIndex T))
  filter_upwards [hLeft, hRight] with omega hLeft hRight
  calc
    ⇑(compensatorConvexRowValueToLp hV hRows hControl w T) omega =
        compensatorConvexRow (V := V) (F := F) (mu := mu)
          (T := T) (C := C) w T omega := by
      simpa only [compensatorConvexRowValueToLp] using hLeft
    _ = compensatorConvexRow (V := V) (F := F) (mu := mu)
          (T := T) (C := C) w
          (stoppedLimitSkeleton T (stoppedLimitTerminalIndex T)).1 omega := by
      rw [stoppedLimitSkeleton_terminalIndex]
    _ = ⇑(compensatorConvexCoordinateToLp hV hRows hControl w
          (stoppedLimitTerminalIndex T)) omega := hRight.symm

omit hSigma in
theorem compensatorConvexRowValueToLp_terminal_tendsto_commonCoordinate
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (w : ∀ n, TailConvexWeights n)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu)
      (2 : ENNReal))
    (hResidual : ∀ r,
      FactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows r)
    (hCommon : FactorialGridPredictableCompensatorCommonHilbertConvexificationData
      hV hRows hControl hResidual w y)
    {cutoff : Nat → Nat} (hCutoff : StrictMono cutoff) :
    Tendsto
      (fun n => compensatorConvexRowValueToLp hV hRows hControl
        (w (cutoff n)) T) atTop
      (𝓝 (commonCoordinateLimit C y
        (stoppedLimitTerminalIndex T + 1))) := by
  have hCoordinate := (hCommon.skeleton_coordinate_tendsto
    (stoppedLimitTerminalIndex T)).comp hCutoff.tendsto_atTop
  apply hCoordinate.congr'
  exact Filter.Eventually.of_forall fun n =>
    (compensatorConvexRowValueToLp_terminal_eq_coordinate
      (F := F) (mu := mu) hV hRows hControl (w (cutoff n))).symm

/-! ## Public certificate -/

structure FactorialGridPredictableCompensatorCommonAESubsequenceData
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
    (cutoff : Nat → Nat) : Prop where
  cutoff_strictMono : StrictMono cutoff
  coordinate_tendstoAE : ∀ i, TendstoAE mu
    (fun n => commonAECoordinateRaw (V := V) (F := F) (mu := mu)
      (T := T) (C := C) w i (cutoff n))
    (commonAECoordinateLimitRaw C y i)
  residual_tendstoAE : TendstoAE mu
    (fun n => residualConvexRow (V := V) (F := F) (mu := mu)
      (T := T) (C := C) (w (cutoff n)))
    (commonCoordinateLimit C y 0 : Ω → Real)
  skeleton_tendstoAE : ∀ j, TendstoAE mu
    (fun n => compensatorConvexRow (V := V) (F := F) (mu := mu)
      (T := T) (C := C) (w (cutoff n)) (stoppedLimitSkeleton T j).1)
    (commonCoordinateLimit C y (j + 1) : Ω → Real)
  weights_tail : ∀ n i, i ∈ (w (cutoff n)).support → cutoff n ≤ i
  weights_nonnegative : ∀ n i, i ∈ (w (cutoff n)).support →
    0 ≤ (w (cutoff n)).weight i
  weights_sum_eq_one : ∀ n,
    ∑ i ∈ (w (cutoff n)).support, (w (cutoff n)).weight i = 1
  row_isStronglyPredictable : ∀ n,
    IsStronglyPredictable F
      (compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w (cutoff n)))
  row_zero : ∀ n,
    compensatorConvexRow (V := V) (F := F) (mu := mu)
      (T := T) (C := C) (w (cutoff n)) 0 = 0
  row_nonnegative : ∀ n t omega,
    0 ≤ compensatorConvexRow (V := V) (F := F) (mu := mu)
      (T := T) (C := C) (w (cutoff n)) t omega
  row_mono : ∀ n omega,
    Monotone
      (compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w (cutoff n)) · omega)
  row_leftContinuous : ∀ n omega t,
    ContinuousWithinAt
      (compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w (cutoff n)) · omega)
      (Iic t) t
  row_constant_after : ∀ n omega t, T ≤ t →
    compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w (cutoff n)) t omega =
      compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w (cutoff n)) T omega
  row_terminal_memLp_two : ∀ n,
    MemLp
      (compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w (cutoff n)) T)
      (2 : ENNReal) mu
  row_terminal_L2_bound : ∀ n,
    (∫ omega,
      (compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w (cutoff n)) T omega) ^ 2 ∂mu) ≤
      8 * (C : Real) ^ 2
  residual_row_memLp_two : ∀ n,
    MemLp
      (residualConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w (cutoff n))) (2 : ENNReal) mu
  residual_row_eq_source_sub_compensator : ∀ n,
    residualConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w (cutoff n)) =
      fun omega => V T omega -
        compensatorConvexRow (V := V) (F := F) (mu := mu)
          (T := T) (C := C) (w (cutoff n)) T omega

/-! ## The terminal row bridge -/

omit hSigma in
theorem preg_terminal_memLp_two_of_commonCadlagRegularization
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
      hV hRows hControl hResidual hCommon Z M Pcad)
    (bad : Set Ω) (Preg : Process Ω)
    (hReg : FactorialGridPredictableCompensatorCadlagMonotoneRegularizationData
      hCad bad Preg) :
    MemLp (Preg T) (2 : ENNReal) mu := by
  let terminal := stoppedLimitTerminalIndex T
  let L : Lp Real 2 mu := commonCoordinateLimit C y (terminal + 1)
  have hPcad : Pcad T =ᵐ[mu] (L : Ω → Real) := by
    simpa only [terminal, L, stoppedLimitSkeleton_terminalIndex] using
      hCad.Pcad_skeleton terminal
  have hPcadMem : MemLp (Pcad T) (2 : ENNReal) mu :=
    (memLp_congr_ae hPcad).mpr (Lp.memLp L)
  exact (memLp_congr_ae (hReg.Preg_indistinguishable.eventuallyEq_at T)).mpr
    hPcadMem

structure FactorialGridPredictableCompensatorCommonAESubsequenceRegularizedData
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
      hCad bad Preg) : Prop where
  common_subsequence :
    FactorialGridPredictableCompensatorCommonAESubsequenceData
      hV hRows hControl hResidual w y hCommon cutoff
  cadlag_candidate :
    FactorialGridPredictableCompensatorCadlagCandidateData
      hV hRows hControl hResidual hCommon Z M Pcad
  regularization :
    FactorialGridPredictableCompensatorCadlagMonotoneRegularizationData
      hCad bad Preg
  preg_terminal_memLp_two : MemLp (Preg T) (2 : ENNReal) mu
  residual_tendstoAE_Z : TendstoAE mu
    (fun n => residualConvexRow (V := V) (F := F) (mu := mu)
      (T := T) (C := C) (w (cutoff n)))
    (Z : Ω → Real)
  terminal_compensator_tendstoAE : TendstoAE mu
    (fun n => compensatorConvexRow (V := V) (F := F) (mu := mu)
      (T := T) (C := C) (w (cutoff n)) T)
    (Preg T)
  terminal_compensator_tendsto_Lp : Tendsto
    (fun n => compensatorConvexRowValueToLp hV hRows hControl
      (w (cutoff n)) T) atTop
    (𝓝 (preg_terminal_memLp_two.toLp (Preg T)))
  terminal_compensator_tendsto_eLpNorm : Tendsto
    (fun n => eLpNorm
      (compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w (cutoff n)) T - Preg T)
      (2 : ENNReal) mu) atTop (𝓝 0)
  weights_tail : ∀ n i, i ∈ (w (cutoff n)).support → cutoff n ≤ i
  weights_nonnegative : ∀ n i, i ∈ (w (cutoff n)).support →
    0 ≤ (w (cutoff n)).weight i
  weights_sum_eq_one : ∀ n,
    ∑ i ∈ (w (cutoff n)).support, (w (cutoff n)).weight i = 1
  row_isStronglyPredictable : ∀ n,
    IsStronglyPredictable F
      (compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w (cutoff n)))
  row_nonnegative : ∀ n t omega,
    0 ≤ compensatorConvexRow (V := V) (F := F) (mu := mu)
      (T := T) (C := C) (w (cutoff n)) t omega
  row_mono : ∀ n omega,
    Monotone
      (compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w (cutoff n)) · omega)
  row_leftContinuous : ∀ n omega t,
    ContinuousWithinAt
      (compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w (cutoff n)) · omega)
      (Iic t) t
  row_zero : ∀ n,
    compensatorConvexRow (V := V) (F := F) (mu := mu)
      (T := T) (C := C) (w (cutoff n)) 0 = 0
  row_constant_after : ∀ n omega t, T ≤ t →
    compensatorConvexRow (V := V) (F := F) (mu := mu)
      (T := T) (C := C) (w (cutoff n)) t omega =
      compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w (cutoff n)) T omega
  row_terminal_L2_bound : ∀ n,
    (∫ omega,
      (compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w (cutoff n)) T omega) ^ 2 ∂mu) ≤
      8 * (C : Real) ^ 2
  residual_row_memLp_two : ∀ n,
    MemLp
      (residualConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w (cutoff n))) (2 : ENNReal) mu

omit hSigma in
theorem factorialGridPredictableCompensatorCommonAESubsequenceRegularized_producer
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
    FactorialGridPredictableCompensatorCommonAESubsequenceRegularizedData
      hV hRows hControl hResidual w y hCommon cutoff hData
        Z M Pcad hCad bad Preg hReg := by
  let terminal := stoppedLimitTerminalIndex T
  let L : Lp Real 2 mu := commonCoordinateLimit C y (terminal + 1)
  have hPcad : Pcad T =ᵐ[mu] (L : Ω → Real) := by
    simpa only [terminal, L, stoppedLimitSkeleton_terminalIndex] using
      hCad.Pcad_skeleton terminal
  have hPreg : Preg T =ᵐ[mu] (L : Ω → Real) :=
    (hReg.Preg_indistinguishable.eventuallyEq_at T).trans hPcad
  have hPregMem : MemLp (Preg T) (2 : ENNReal) mu :=
    preg_terminal_memLp_two_of_commonCadlagRegularization
      (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon Z M Pcad
        hCad bad Preg hReg
  have hResidualAE : TendstoAE mu
      (fun n => residualConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w (cutoff n))) (Z : Ω → Real) := by
    have hTarget := congrArg (fun z : Lp Real 2 mu => (z : Ω → Real))
      hCad.terminalLimit_eq
    filter_upwards [hData.residual_tendstoAE] with omega hω
    simpa only [hTarget] using hω
  have hTerminalAE : TendstoAE mu
      (fun n => compensatorConvexRow (V := V) (F := F) (mu := mu)
        (T := T) (C := C) (w (cutoff n)) T) (Preg T) := by
    have hRaw := hData.skeleton_tendstoAE terminal
    have hRaw' : TendstoAE mu
        (fun n => compensatorConvexRow (V := V) (F := F) (mu := mu)
          (T := T) (C := C) (w (cutoff n)) T)
        (L : Ω → Real) := by
      simpa only [terminal, stoppedLimitSkeleton_terminalIndex] using hRaw
    filter_upwards [hRaw', hPreg] with omega hω hTarget
    simpa only [hTarget] using hω
  have hPregLpEq :
      hPregMem.toLp (Preg T) = commonCoordinateLimit C y (terminal + 1) := by
    have hEq := MemLp.toLp_congr hPregMem (Lp.memLp L) hPreg
    exact hEq.trans (Lp.toLp_coeFn L (Lp.memLp L))
  have hTerminalLp : Tendsto
      (fun n => compensatorConvexRowValueToLp hV hRows hControl
        (w (cutoff n)) T) atTop
      (𝓝 (hPregMem.toLp (Preg T))) := by
    have hCommonT := compensatorConvexRowValueToLp_terminal_tendsto_commonCoordinate
      (F := F) (mu := mu) hV hRows hControl w y hResidual hCommon
        hData.cutoff_strictMono
    rw [hPregLpEq] at ⊢
    exact hCommonT
  have hTerminalNorm : Tendsto
      (fun n => eLpNorm
        (compensatorConvexRow (V := V) (F := F) (mu := mu)
          (T := T) (C := C) (w (cutoff n)) T - Preg T)
        (2 : ENNReal) mu) atTop (𝓝 0) := by
    have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
      (fun n => compensatorConvexRowValueToLp hV hRows hControl
        (w (cutoff n)) T) (hPregMem.toLp (Preg T))).mp hTerminalLp
    apply hLp.congr'
    exact Filter.Eventually.of_forall fun n => by
      apply eLpNorm_congr_ae
      have hRaw := (compensatorConvexRow_value_memLp_two
        (F := F) (mu := mu) hV hRows hControl (w (cutoff n)) T).coeFn_toLp
      filter_upwards [hRaw, hPregMem.coeFn_toLp] with omega hRaw hω
      simpa only [compensatorConvexRowValueToLp, Pi.sub_apply] using
        (congrArg (fun x : Real =>
          x - (hPregMem.toLp (Preg T) : Ω → Real) omega) hRaw).trans
          (congrArg (fun x : Real =>
            compensatorConvexRow (V := V) (F := F) (mu := mu)
              (T := T) (C := C) (w (cutoff n)) T omega - x) hω)
  refine {
    common_subsequence := hData
    cadlag_candidate := hCad
    regularization := hReg
    preg_terminal_memLp_two := hPregMem
    residual_tendstoAE_Z := hResidualAE
    terminal_compensator_tendstoAE := hTerminalAE
    terminal_compensator_tendsto_Lp := hTerminalLp
    terminal_compensator_tendsto_eLpNorm := hTerminalNorm
    weights_tail := hData.weights_tail
    weights_nonnegative := hData.weights_nonnegative
    weights_sum_eq_one := hData.weights_sum_eq_one
    row_isStronglyPredictable := hData.row_isStronglyPredictable
    row_nonnegative := hData.row_nonnegative
    row_mono := hData.row_mono
    row_leftContinuous := hData.row_leftContinuous
    row_zero := hData.row_zero
    row_constant_after := hData.row_constant_after
    row_terminal_L2_bound := hData.row_terminal_L2_bound
    residual_row_memLp_two := hData.residual_row_memLp_two }

/-! ## The common diagonal producer -/

omit [SigmaFiniteFiltration mu F] in
theorem factorialGridPredictableCompensatorCommonAESubsequence_producer
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
      hV hRows hControl hResidual w y) :
    ∃ cutoff : Nat → Nat,
      FactorialGridPredictableCompensatorCommonAESubsequenceData
        hV hRows hControl hResidual w y hCommon cutoff := by
  let h := boundedCommonHilbertRowsData (F := F) (mu := mu) hV hRows hControl
  have hCore := boundedCommonHilbertConvexificationCoreData
    (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon
  obtain ⟨cutoff, hData⟩ :=
    CommonHilbertRowsData.commonAESubsequence_producer
      (h := h) w y hCore
  have hRawEq : ∀ (i n : Nat),
      CommonHilbertRowsData.commonAECoordinateRaw h w i n =
        commonAECoordinateRaw (V := V) (F := F) (mu := mu)
          (T := T) (C := C) w i n := by
    intro i n
    cases i <;> rfl
  have hLimitEq : ∀ (i : Nat),
      CommonHilbertRowsData.commonAECoordinateLimitRaw h y i =
        commonAECoordinateLimitRaw C y i := by
    intro i
    rfl
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
  refine ⟨cutoff, ?_⟩
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
    residual_row_memLp_two := ?_
    residual_row_eq_source_sub_compensator := ?_ }
  · intro i
    filter_upwards [hData.coordinate_tendstoAE i] with omega hω
    simpa only [hRawEq i, hLimitEq i] using hω
  · have hResidualAE : TendstoAE mu
        (fun n => residualConvexRow (V := V) (F := F) (mu := mu)
          (T := T) (C := C) (w (cutoff n)))
        (commonCoordinateLimit C y 0 : Ω → Real) := by
      convert hData.residual_tendstoAE using 1
      · funext n
        exact hResidualConvexRowEq (w (cutoff n))
      · exact hLimitEq 0
    exact hResidualAE
  · intro j
    have hSkeletonAE : TendstoAE mu
        (fun n => compensatorConvexRow (V := V) (F := F) (mu := mu)
          (T := T) (C := C) (w (cutoff n))
            (stoppedLimitSkeleton T j).1)
        (commonCoordinateLimit C y (j + 1) : Ω → Real) := by
      convert hData.skeleton_tendstoAE j using 1
      · funext n
        exact congrFun (hConvexRowEq (w (cutoff n))).symm
          (stoppedLimitSkeleton T j).1
      · exact hLimitEq (j + 1)
    exact hSkeletonAE
  · intro n
    rw [← hConvexRowEq (w (cutoff n))]
    exact hData.row_isStronglyPredictable n
  · intro n
    rw [← hConvexRowEq (w (cutoff n))]
    exact hData.row_zero n
  · intro n t omega
    rw [← hConvexRowEq (w (cutoff n))]
    exact hData.row_nonnegative n t omega
  · intro n omega
    rw [← hConvexRowEq (w (cutoff n))]
    exact hData.row_mono n omega
  · intro n omega t
    rw [← hConvexRowEq (w (cutoff n))]
    exact hData.row_leftContinuous n omega t
  · intro n omega t ht
    rw [← hConvexRowEq (w (cutoff n))]
    exact hData.row_constant_after n omega t ht
  · intro n
    rw [← hConvexRowEq (w (cutoff n))]
    exact hData.row_terminal_memLp_two n
  · intro n
    rw [← hConvexRowEq (w (cutoff n))]
    have hBound := hData.row_terminal_L2_bound n
    change (∫ omega,
      h.convexRow (w (cutoff n)) T omega ^ 2 ∂mu) ≤
      (Real.sqrt (8 * (C : Real) ^ 2)) ^ 2 at hBound
    rw [Real.sq_sqrt (by positivity)] at hBound
    exact hBound
  · intro n
    rw [← hResidualConvexRowEq (w (cutoff n))]
    exact hData.residual_row_memLp_two n
  · intro n
    rw [← hResidualConvexRowEq (w (cutoff n)), ← hConvexRowEq (w (cutoff n))]
    exact hData.residual_row_eq_source_sub_compensator n

/-! A component package used by the subsequent predictable-version
construction.  It keeps the diagonal subsequence together with the
regularized càdlàg candidate, while deliberately making no process-level
claim about a predictable limit. -/

structure FactorialGridPredictableCompensatorCommonAEJordanComponentData
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
      hV hRows hControl hResidual hCommon Z M Pcad)
    (bad : Set Ω) (Preg : Process Ω)
    (hReg : FactorialGridPredictableCompensatorCadlagMonotoneRegularizationData
      hCad bad Preg) : Type _ where
  cutoff : Nat → Nat
  common_subsequence :
    FactorialGridPredictableCompensatorCommonAESubsequenceData
      hV hRows hControl hResidual w y hCommon cutoff
  regularized :
    FactorialGridPredictableCompensatorCommonAESubsequenceRegularizedData
      hV hRows hControl hResidual w y hCommon cutoff common_subsequence
        Z M Pcad hCad bad Preg hReg

omit hSigma in
theorem factorialGridPredictableCompensatorCommonAEJordanComponentData_producer
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
      hV hRows hControl hResidual hCommon Z M Pcad)
    (bad : Set Ω) (Preg : Process Ω)
    (hReg : FactorialGridPredictableCompensatorCadlagMonotoneRegularizationData
      hCad bad Preg) :
    Nonempty (FactorialGridPredictableCompensatorCommonAEJordanComponentData
      hV hRows hControl hResidual w y hCommon Z M Pcad hCad bad Preg hReg) := by
  obtain ⟨cutoff, hData⟩ :=
    factorialGridPredictableCompensatorCommonAESubsequence_producer
      (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon
  obtain hRegularized :=
    factorialGridPredictableCompensatorCommonAESubsequenceRegularized_producer
      (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon cutoff hData
        Z M Pcad hCad bad Preg hReg
  exact ⟨{
    cutoff := cutoff
    common_subsequence := hData
    regularized := hRegularized }⟩

/-! Concrete common-stop Jordan consumer.  It reuses the already constructed
regularized positive and negative candidates and adds one common AE diagonal
package for each component.  The two diagonal cutoffs remain independent. -/

theorem exists_commonAEJordanComponents_of_commonStopJordanComponents
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
                      ∃ hRegPlus :
                        FactorialGridPredictableCompensatorCadlagMonotoneRegularizationData
                        hCadPlus badPlus PregPlus,
                        Nonempty (FactorialGridPredictableCompensatorCommonAEJordanComponentData
                          hPlus hRowsPlus hControlPlus hResidualPlus wPlus yPlus
                            hCommonPlus ZPlus MPlus PcadPlus hCadPlus badPlus PregPlus hRegPlus) ∧
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
                      ∃ hRegMinus :
                        FactorialGridPredictableCompensatorCadlagMonotoneRegularizationData
                        hCadMinus badMinus PregMinus,
                        Nonempty (FactorialGridPredictableCompensatorCommonAEJordanComponentData
                          hMinus hRowsMinus hControlMinus hResidualMinus wMinus yMinus
                            hCommonMinus ZMinus MMinus PcadMinus hCadMinus badMinus PregMinus
                              hRegMinus) := by
  obtain ⟨hPlus, hRowsPlus, hControlPlus, hResidualPlus, wPlus, yPlus,
      hCommonPlus, ZPlus, MPlus, PcadPlus, hCadPlus,
      badPlus, PregPlus, hRegPlus,
      hMinus, hRowsMinus, hControlMinus, hResidualMinus, wMinus, yMinus,
      hCommonMinus, ZMinus, MMinus, PcadMinus, hCadMinus,
      badMinus, PregMinus, hRegMinus⟩ :=
    exists_monotoneRegularizedCadlagCandidates_of_commonStopJordanComponents
      (F := F) (mu := mu) endpoint bad Atilde Aplus Aminus
        cumulativeVariation hReg
  obtain hPlusPackage :=
    factorialGridPredictableCompensatorCommonAEJordanComponentData_producer
      (F := F) (mu := mu) hPlus hRowsPlus hControlPlus hResidualPlus wPlus yPlus
        hCommonPlus ZPlus MPlus PcadPlus hCadPlus badPlus PregPlus hRegPlus
  obtain hMinusPackage :=
    factorialGridPredictableCompensatorCommonAEJordanComponentData_producer
      (F := F) (mu := mu) hMinus hRowsMinus hControlMinus hResidualMinus wMinus yMinus
        hCommonMinus ZMinus MMinus PcadMinus hCadMinus badMinus PregMinus hRegMinus
  exact ⟨hPlus, hRowsPlus, hControlPlus, hResidualPlus, wPlus, yPlus,
    hCommonPlus, ZPlus, MPlus, PcadPlus, hCadPlus, badPlus, PregPlus, hRegPlus,
    hPlusPackage, hMinus, hRowsMinus, hControlMinus, hResidualMinus, wMinus,
    yMinus, hCommonMinus, ZMinus, MMinus, PcadMinus, hCadMinus, badMinus,
    PregMinus, hRegMinus, hMinusPackage⟩

end HorizonFactorialGrid

end FTAPTheorem42
