/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.CommonAESubsequence
import FTAPTheorem42.Stochastic.Decomposition.Compensator.PredictableLimsupCore

/-!
# The predictable limsup of the common compensator rows

The common diagonal subsequence supplies one family of left-continuous
predictable compensator rows.  This file forms their pointwise `limsup` and
records the part of the dense-path argument which is already available before
any stopping-time identification is attempted.

The deterministic lemmas below are deliberately pathwise.  A right-dense
set gives the upper inequality at every time for a right-continuous increasing
limit.  Equality at a continuity point additionally uses approximation from
the left; it is therefore stated with the corresponding left-density input.
No process-level indistinguishability is asserted here.
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

/-! ## The raw predictable limsup -/

/-- Pointwise limsup of the common tail-convex compensator rows. -/
noncomputable def predictableCompensatorLimsup
    (w : ∀ n, TailConvexWeights n) (cutoff : Nat → Nat)
    (V : Process Ω) (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (mu : Measure Ω) (T C : NNReal) : Process Ω :=
  fun t omega => limsup (fun n =>
    compensatorConvexRow (V := V) (F := F) (mu := mu)
      (T := T) (C := C) (w (cutoff n)) t omega) atTop

/-! ## The common diagonal limsup certificate -/

/-- The data retained for the predictable limsup.  The inequalities are
stated outside one common null set, while the process itself is the raw
pointwise limsup.  Thus this certificate does not silently replace a
predictable process by a càdlàg modification. -/
structure FactorialGridPredictableCompensatorPredictableLimsupData
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
    (Ppred : Process Ω) : Prop where
  Ppred_definition : Ppred =
    predictableCompensatorLimsup w cutoff V F mu T C
  Ppred_isStronglyPredictable : IsStronglyPredictable F Ppred
  Ppred_le_Preg : ∀ᵐ omega ∂mu, ∀ t,
    Ppred t omega ≤ Preg t omega
  Ppred_eq_Preg_at_continuity : ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
    ContinuousAt (Preg · omega) t → Ppred t omega = Preg t omega
  Ppred_zero : Ppred 0 = 0
  Ppred_constant_after : ∀ᵐ omega ∂mu, ∀ t, T ≤ t →
    Ppred t omega = Ppred T omega

omit [SigmaFiniteFiltration mu F] in
theorem exists_factorialGridPredictableCompensatorPredictableLimsup
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
    FactorialGridPredictableCompensatorPredictableLimsupData
      hV hRows hControl hResidual w y hCommon cutoff hData
        Z M Pcad hCad bad Preg hReg
        (predictableCompensatorLimsup w cutoff V F mu T C) := by
  let h := boundedCommonHilbertRowsData (F := F) (mu := mu)
    hV hRows hControl
  let hCore := boundedCommonHilbertConvexificationCoreData
    hV hRows hControl hResidual w y hCommon
  let source_valueToLp := boundedCadlagCandidateSourceValueToLp
    (F := F) (mu := mu) hV
  let hSource := boundedCadlagCandidateSourceData
    hV hRows hControl hResidual w y hCommon
  have hCadCore :
      CommonHilbertRowsData.CadlagCandidateData h w y hCore
        source_valueToLp V hSource Z M Pcad := by
    refine {
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
      h w y hCore cutoff := by
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
        exact hResidualConvexRowEq (w (cutoff n))
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
      have hBound := hData.row_terminal_L2_bound n
      change (∫ omega, h.convexRow (w (cutoff n)) T omega ^ 2 ∂mu) ≤
        (Real.sqrt (8 * (C : Real) ^ 2)) ^ 2
      rw [Real.sq_sqrt (by positivity)]
      exact hBound
    · intro n
      exact hCore.row_terminal_expectation (cutoff n)
    · intro n
      rw [hResidualConvexRowEq]
      exact hData.residual_row_memLp_two n
    · intro n
      rw [hResidualConvexRowEq, hConvexRowEq]
      exact hData.residual_row_eq_source_sub_compensator n
  have hLimsup := CommonHilbertRowsData.exists_predictableLimsup
    (h := h) (w := w) (y := y) (hCommon := hCore)
    (cutoff := cutoff) (hData := hDataCore)
    (source_valueToLp := source_valueToLp) (X := V)
    (hSource := hSource) (Z := Z) (M := M) (Pcad := Pcad)
    (hCad := hCadCore) (bad := bad) (Preg := Preg) (hReg := hRegCore)
  have hPredictableLimsupEq :
      predictableCompensatorLimsup w cutoff V F mu T C =
        CommonHilbertRowsData.predictableLimsup h w cutoff := by
    funext t omega
    dsimp [predictableCompensatorLimsup,
      CommonHilbertRowsData.predictableLimsup]
    apply limsup_congr
    exact Filter.Eventually.of_forall fun n =>
      congrFun (congrFun (hConvexRowEq (w (cutoff n))) t) omega |>.symm
  refine {
    Ppred_definition := ?_
    Ppred_isStronglyPredictable := ?_
    Ppred_le_Preg := ?_
    Ppred_eq_Preg_at_continuity := ?_
    Ppred_zero := ?_
    Ppred_constant_after := ?_ }
  · rw [hPredictableLimsupEq]
  · rw [hPredictableLimsupEq]
    exact hLimsup.Ppred_isStronglyPredictable
  · rw [hPredictableLimsupEq]
    exact hLimsup.Ppred_le_Preg
  · rw [hPredictableLimsupEq]
    exact hLimsup.Ppred_eq_Preg_at_continuity
  · rw [hPredictableLimsupEq]
    exact hLimsup.Ppred_zero
  · rw [hPredictableLimsupEq]
    exact hLimsup.Ppred_constant_after

/-! ## Jordan-component consumer -/

omit [SigmaFiniteFiltration mu F] in
/-- The limsup certificate consumes the common AE/Jordan package without
changing its diagonal subsequence.  The positive and negative Jordan
components are deliberately handled by the same generic consumer, so no
additional projection or process-level identification is hidden in this
endpoint. -/
theorem predictableCompensatorLimsup_of_commonAEJordanComponent
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
    {hCad : FactorialGridPredictableCompensatorCadlagCandidateData
      hV hRows hControl hResidual hCommon Z M Pcad}
    {bad : Set Ω} {Preg : Process Ω}
    {hReg : FactorialGridPredictableCompensatorCadlagMonotoneRegularizationData
      hCad bad Preg}
    (hComponent : FactorialGridPredictableCompensatorCommonAEJordanComponentData
      hV hRows hControl hResidual w y hCommon Z M Pcad hCad bad Preg hReg) :
    FactorialGridPredictableCompensatorPredictableLimsupData
      hV hRows hControl hResidual w y hCommon hComponent.cutoff
        hComponent.common_subsequence
        Z M Pcad hCad bad Preg hReg
        (predictableCompensatorLimsup w hComponent.cutoff V F mu T C) := by
  exact exists_factorialGridPredictableCompensatorPredictableLimsup
    (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon
      hComponent.cutoff hComponent.common_subsequence Z M Pcad hCad bad Preg hReg

end HorizonFactorialGrid

end FTAPTheorem42
