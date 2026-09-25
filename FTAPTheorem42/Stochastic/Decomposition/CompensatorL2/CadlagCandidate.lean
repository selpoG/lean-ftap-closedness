/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.CadlagCandidateCore
import FTAPTheorem42.Stochastic.Decomposition.CompensatorL2.CommonAESubsequence
import FTAPTheorem42.Stochastic.Decomposition.Compensator.CadlagMonotoneRegularizationCore

/-!
# Càdlàg candidates for square-integrable compensator rows

This is the `L²` adapter for the source-independent càdlàg candidate.  The
finite-grid residual certificate supplies the conditional-expectation law on
the stopped skeleton; all process regularization is performed by the generic
core.
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

noncomputable def squareIntegrableCadlagCandidateSourceValueToLp
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T) :
    NNReal → Lp Real (2 : ENNReal) mu :=
  fun t => (hV.value_memLp_two (min_le_right t T)).toLp (V (min t T))

omit [SigmaFiniteFiltration mu F] in
theorem squareIntegrableCadlagCandidateSourceValueToLp_coeFn_ae
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (t : NNReal) :
    ⇑(squareIntegrableCadlagCandidateSourceValueToLp
      (F := F) (mu := mu) hV t) =ᵐ[mu] V t := by
  by_cases ht : t ≤ T
  · have hmin : min t T = t := min_eq_left ht
    simpa only [squareIntegrableCadlagCandidateSourceValueToLp, hmin] using
      (MemLp.coeFn_toLp (hV.value_memLp_two ht))
  · have hTt : T ≤ t := le_of_not_ge ht
    have hmin : min t T = T := min_eq_right hTt
    have hconst : V t = V T := by
      funext omega
      exact hV.constant_after omega t hTt
    filter_upwards [MemLp.coeFn_toLp
      (hV.value_memLp_two (t := min t T) (min_le_right t T))] with omega hminValue
    calc
      ((squareIntegrableCadlagCandidateSourceValueToLp
        (F := F) (mu := mu) hV t : Ω → Real) omega) =
          V (min t T) omega := hminValue
      _ = V T omega := by rw [hmin]
      _ = V t omega := (congrFun hconst omega).symm

omit [SigmaFiniteFiltration mu F] in
private theorem squareIntegrableSkeletonCoordinate_condExp_eq
    (hV : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) V T)
    (hRows : SquareIntegrableIncreasingProcessCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : SquareIntegrableIncreasingProcessCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      SquareIntegrableFactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows hControl r)
    (w : ∀ n, TailConvexWeights n) (j n : Nat)
    (hjn : (Nat.unpair j).1 ≤ n) :
    ((lpMeas Real Real
        (F (stoppedLimitSkeleton T j).1) 2 mu).subtypeL.comp
      (condExpL2 Real Real
        (F.le (stoppedLimitSkeleton T j).1)))
        (squareIntegrableResidualConvexCoordinateToLp
          hV hRows hControl hResidual (w n)) =
      ((hV.value_memLp_two (stoppedLimitSkeleton T j).2).sub
        (CommonHilbertRowsData.convexRow_value_memLp_two
          (squareIntegrableCommonHilbertRowsData hV hRows hControl hResidual)
          (w n) (stoppedLimitSkeleton T j).1)).toLp
        (V (stoppedLimitSkeleton T j).1 -
          squareIntegrableCompensatorConvexRow hV hRows hControl
            hResidual (w n) (stoppedLimitSkeleton T j).1) := by
  classical
  let s : NNReal := (stoppedLimitSkeleton T j).1
  let hs : s ≤ T := (stoppedLimitSkeleton T j).2
  let CE : Lp Real 2 mu →L[Real] Lp Real 2 mu :=
    (lpMeas Real Real (F s) 2 mu).subtypeL.comp
      (condExpL2 Real Real (F.le s))
  have hComponent (r : Nat) (hr : (Nat.unpair j).1 ≤ r) :
      CE (squareIntegrableTerminalResidualToLp hV hRows hControl r) =
        ((hV.value_memLp_two (mu := mu) (t := s) hs).sub
          (hControl.value_memLp_two r s)).toLp
          (V s - squareIntegrablePredictableCompensatorProcess
            V F mu T r s) := by
    let k : Fin (size T r + 1) := approxIndex T s hs r
    have hk_le : k.1 ≤ size T r := Nat.lt_succ_iff.mp k.isLt
    have htime : (grid T r).sampledTime k.1 = s := by
      rw [(grid T r).sampledTime_fin_eq k]
      exact grid_time_approxIndex_stoppedLimitSkeleton_eq T j hr
    have hRaw := (hResidual r).terminal_condExp k.1 hk_le
    have hRaw' : squareIntegrableFactorialGridSampledResidual V F mu T r k.1 =ᵐ[mu]
        mu[squareIntegrableFactorialGridSampledResidual V F mu T r (size T r) |
          F s] := by
      simpa only [ChronologicalGrid.sampledFiltration_apply, htime] using hRaw
    have hMem : MemLp
        (squareIntegrableTerminalResidualToLp hV hRows hControl r : Ω → Real)
        (2 : ENNReal) mu :=
      Lp.memLp (squareIntegrableTerminalResidualToLp hV hRows hControl r)
    have hBridge := hMem.condExpL2_ae_eq_condExp (𝕜 := Real)
      (F.le s)
    rw [Lp.toLp_coeFn
      (squareIntegrableTerminalResidualToLp hV hRows hControl r) hMem]
      at hBridge
    have hTerminal := squareIntegrableTerminalResidualToLp_coeFn_ae
      (F := F) (mu := mu) hV hRows hControl hResidual r
    have hCond : mu[
        (squareIntegrableTerminalResidualToLp hV hRows hControl r : Ω → Real) | F s] =ᵐ[mu]
        mu[squareIntegrableFactorialGridSampledResidual V F mu T r (size T r) | F s] :=
      condExp_congr_ae hTerminal
    have hTargetMem := (hV.value_memLp_two (mu := mu) (t := s) hs).sub
      (hControl.value_memLp_two r s)
    have hTargetRaw := hTargetMem.coeFn_toLp
    apply Lp.ext
    filter_upwards [hBridge, hCond, hRaw', hTargetRaw] with omega
        hBridgeOmega hCondOmega hRawOmega hTargetOmega
    change ((condExpL2 Real Real (F.le s)
      (squareIntegrableTerminalResidualToLp hV hRows hControl r) :
        lpMeas Real Real (F s) 2 mu) : Ω → Real) omega = _
    rw [hBridgeOmega, hCondOmega, ← hRawOmega]
    change V ((grid T r).sampledTime k.1) omega -
        squareIntegrablePredictableCompensatorProcess V F mu T r
          ((grid T r).sampledTime k.1) omega = _
    rw [htime]
    exact hTargetOmega.symm
  let Pn : Lp Real 2 mu :=
    squareIntegrableResidualConvexCoordinateToLp hV hRows hControl hResidual (w n)
  have hCEsum : CE Pn =
      ((hV.value_memLp_two (mu := mu) (t := s) hs).sub
        (CommonHilbertRowsData.convexRow_value_memLp_two
          (squareIntegrableCommonHilbertRowsData hV hRows hControl hResidual)
          (w n) s)).toLp
        (V s - squareIntegrableCompensatorConvexRow hV hRows hControl
          hResidual (w n) s) := by
    have hTargetRaw :=
      ((hV.value_memLp_two (mu := mu) (t := s) hs).sub
        (CommonHilbertRowsData.convexRow_value_memLp_two
          (squareIntegrableCommonHilbertRowsData hV hRows hControl hResidual)
          (w n) s)).coeFn_toLp
    have hVec :
        ((∑ r ∈ (w n).support, (w n).weight r •
          CE (squareIntegrableTerminalResidualToLp hV hRows hControl r) :
          Lp Real 2 mu) : Ω → Real) =ᵐ[mu]
          (w n).apply (fun r => fun omega =>
            V s omega - squareIntegrablePredictableCompensatorProcess
              V F mu T r s omega) := by
      apply finset_smul_coeFn_ae_of_mem
      intro r hr
      have hComp := congrArg (fun z : Lp Real 2 mu => (z : Ω → Real))
        (hComponent r (hjn.trans ((w n).tail r hr)))
      have hRaw := ((hV.value_memLp_two (mu := mu) (t := s) hs).sub
        (hControl.value_memLp_two r s)).coeFn_toLp
      filter_upwards [hRaw] with omega hRawOmega
      exact (congrFun hComp omega).trans (by
        simpa only [Pi.sub_apply] using hRawOmega)
    have hApply :
        (w n).apply (fun r => fun omega =>
            V s omega - squareIntegrablePredictableCompensatorProcess
              V F mu T r s omega) =
          (V s - squareIntegrableCompensatorConvexRow hV hRows hControl
            hResidual (w n) s) := by
      funext omega
      simp only [TailConvexWeights.apply]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, (w n).sum_eq_one,
        one_mul]
      rfl
    have hCEPn : CE Pn =
        ∑ r ∈ (w n).support, (w n).weight r •
          CE (squareIntegrableTerminalResidualToLp hV hRows hControl r) := by
      change CE ((w n).applyVector (fun r =>
        squareIntegrableTerminalResidualToLp hV hRows hControl r)) = _
      unfold TailConvexWeights.applyVector
      rw [map_sum]
      simp only [map_smul]
    have hLeft :
        (⇑(CE Pn) =ᵐ[mu]
          (V s - squareIntegrableCompensatorConvexRow hV hRows hControl
            hResidual (w n) s)) := by
      rw [hCEPn]
      simpa only using hVec.trans
          (Eventually.of_forall (fun omega => congrFun hApply omega))
    apply Lp.ext
    exact hLeft.trans hTargetRaw.symm
  exact hCEsum

/-! The square-integrable source adapter. -/

omit [SigmaFiniteFiltration mu F] in
theorem squareIntegrableCadlagCandidateSourceData
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
    CommonHilbertRowsData.CadlagCandidateSourceData
      (squareIntegrableCommonHilbertRowsData hV hRows hControl hResidual) w y
      hCommon
      (squareIntegrableCadlagCandidateSourceValueToLp
        (F := F) (mu := mu) hV) V := by
  let h := squareIntegrableCommonHilbertRowsData hV hRows hControl hResidual
  let q := squareIntegrableCadlagCandidateSourceValueToLp
    (F := F) (mu := mu) hV
  refine {
    source_valueToLp_coeFn_ae := squareIntegrableCadlagCandidateSourceValueToLp_coeFn_ae
      (F := F) (mu := mu) hV
    source_terminal_ae := Filter.Eventually.of_forall (fun _ => rfl)
    source_stronglyAdapted := hV.stronglyAdapted
    source_rightContinuous := hV.rightContinuous
    source_leftLimits := by
      intro omega t
      exact (hV.monotone omega).tendsto_leftLim t
    source_constant_after := hV.constant_after
    skeleton_condExp := ?_ }
  intro j
  filter_upwards [eventually_ge_atTop (Nat.unpair j).1] with n hn
  have hOld := squareIntegrableSkeletonCoordinate_condExp_eq
    (F := F) (mu := mu) hV hRows hControl hResidual w j n hn
  have hs : (stoppedLimitSkeleton T j).1 ≤ T :=
    (stoppedLimitSkeleton T j).2
  have hq : q (stoppedLimitSkeleton T j).1 =
      (hV.value_memLp_two (stoppedLimitSkeleton T j).2).toLp
        (V (stoppedLimitSkeleton T j).1) := by
    have htime : V (min (stoppedLimitSkeleton T j).1 T) =
        V (stoppedLimitSkeleton T j).1 := by
      rw [min_eq_left hs]
    simpa only [q, squareIntegrableCadlagCandidateSourceValueToLp] using
      (MemLp.toLp_congr
        (hV.value_memLp_two (min_le_right (stoppedLimitSkeleton T j).1 T))
        (hV.value_memLp_two (stoppedLimitSkeleton T j).2)
        (Filter.Eventually.of_forall (fun omega =>
          congrFun htime omega)))
  change CommonHilbertRowsData.skeletonConditionalExpectation
      (F := F) (mu := mu) (stoppedLimitSkeleton T j).1
        (h.residualConvexCoordinateToLp (w n)) =
      q (stoppedLimitSkeleton T j).1 - h.convexCoordinateToLp (w n) j
  rw [hq]
  have hRhsEq :
      (hV.value_memLp_two (stoppedLimitSkeleton T j).2).toLp
          (V (stoppedLimitSkeleton T j).1) -
        squareIntegrableCompensatorConvexCoordinateToLp
          hV hRows hControl hResidual (w n) j =
      ((hV.value_memLp_two (stoppedLimitSkeleton T j).2).sub
        (CommonHilbertRowsData.convexRow_value_memLp_two h (w n)
          (stoppedLimitSkeleton T j).1)).toLp
        (V (stoppedLimitSkeleton T j).1 -
          squareIntegrableCompensatorConvexRow hV hRows hControl
            hResidual (w n) (stoppedLimitSkeleton T j).1) := by
    apply Lp.ext
    have hSub := Lp.coeFn_sub
      ((hV.value_memLp_two (stoppedLimitSkeleton T j).2).toLp
        (V (stoppedLimitSkeleton T j).1))
      (squareIntegrableCompensatorConvexCoordinateToLp
        hV hRows hControl hResidual (w n) j)
    have hTarget := ((hV.value_memLp_two (stoppedLimitSkeleton T j).2).sub
        (CommonHilbertRowsData.convexRow_value_memLp_two h (w n)
          (stoppedLimitSkeleton T j).1)).coeFn_toLp
    have hVRaw := (hV.value_memLp_two
      (stoppedLimitSkeleton T j).2).coeFn_toLp
    have hCoord := squareIntegrableCompensatorConvexCoordinateToLp_coeFn_ae
      (F := F) (mu := mu) hV hRows hControl hResidual (w n) j
    filter_upwards [hSub, hTarget, hVRaw, hCoord] with omega
        hSubOmega hTargetOmega hVOmega hCoordOmega
    calc
      ((↑((hV.value_memLp_two (stoppedLimitSkeleton T j).2).toLp
        (V (stoppedLimitSkeleton T j).1) -
        squareIntegrableCompensatorConvexCoordinateToLp
          hV hRows hControl hResidual (w n) j) : Ω → Real) omega) =
          ((↑((hV.value_memLp_two (stoppedLimitSkeleton T j).2).toLp
            (V (stoppedLimitSkeleton T j).1)) : Ω → Real) omega) -
            ((↑(squareIntegrableCompensatorConvexCoordinateToLp
              hV hRows hControl hResidual (w n) j) : Ω → Real) omega) :=
        hSubOmega
      _ = V (stoppedLimitSkeleton T j).1 omega -
          squareIntegrableCompensatorConvexRow hV hRows hControl
            hResidual (w n) (stoppedLimitSkeleton T j).1 omega := by
        rw [hVOmega, hCoordOmega]
      _ = ((↑(((hV.value_memLp_two (stoppedLimitSkeleton T j).2).sub
        (CommonHilbertRowsData.convexRow_value_memLp_two h (w n)
          (stoppedLimitSkeleton T j).1)).toLp
        (V (stoppedLimitSkeleton T j).1 -
          squareIntegrableCompensatorConvexRow hV hRows hControl
            hResidual (w n) (stoppedLimitSkeleton T j).1)) : Ω → Real) omega) :=
        hTargetOmega.symm
  exact hOld.trans hRhsEq.symm

/-! The public `L²` càdlàg candidate endpoint. -/

abbrev SquareIntegrableIncreasingProcessCadlagCandidateData
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
    (Z : Lp Real 2 mu) (M Pcad : Process Ω) : Prop :=
  CommonHilbertRowsData.CadlagCandidateData
    (squareIntegrableCommonHilbertRowsData hV hRows hControl hResidual) w y
    hCommon (squareIntegrableCadlagCandidateSourceValueToLp
      (F := F) (mu := mu) hV) V
    (squareIntegrableCadlagCandidateSourceData
      (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon)
    Z M Pcad

theorem exists_squareIntegrableIncreasingProcessCadlagCandidate
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
    (hUsual : Filtration.UsualConditions mu F) :
    ∃ (Z : Lp Real 2 mu) (M Pcad : Process Ω),
      SquareIntegrableIncreasingProcessCadlagCandidateData
        hV hRows hControl hResidual w y hCommon Z M Pcad := by
  obtain ⟨Z, M, Pcad, hCad⟩ :=
    CommonHilbertRowsData.exists_cadlagCandidate
      (squareIntegrableCommonHilbertRowsData hV hRows hControl hResidual)
      w y hCommon
      (squareIntegrableCadlagCandidateSourceValueToLp
        (F := F) (mu := mu) hV) V
      (squareIntegrableCadlagCandidateSourceData
        (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon)
      hUsual
  exact ⟨Z, M, Pcad, hCad⟩

/-! The `L²` monotone-regularization endpoint is an adapter for the
source-independent pathwise core.  The common-a.e. selected-row laws are
passed explicitly, so no final projection is hidden in the candidate data. -/

abbrev SquareIntegrableIncreasingProcessCadlagMonotoneRegularizationData
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
    (Z : Lp Real 2 mu) (M Pcad : Process Ω)
    (hCad : SquareIntegrableIncreasingProcessCadlagCandidateData
      hV hRows hControl hResidual w y hCommon Z M Pcad)
    (bad : Set Ω) (Preg : Process Ω) : Prop :=
  CommonHilbertRowsData.CadlagMonotoneRegularizationData hCad bad Preg

omit [SigmaFiniteFiltration mu F] in
theorem exists_squareIntegrableIncreasingProcessCadlagMonotoneRegularization
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
    (hUsual : Filtration.UsualConditions mu F) :
    ∃ (bad : Set Ω) (Preg : Process Ω),
      SquareIntegrableIncreasingProcessCadlagMonotoneRegularizationData
        hV hRows hControl hResidual w y hCommon Z M Pcad hCad bad Preg := by
  exact CommonHilbertRowsData.exists_cadlagMonotoneRegularization
    (h := squareIntegrableCommonHilbertRowsData
      hV hRows hControl hResidual)
    (w := w) (y := y) hCommon
    (squareIntegrableCadlagCandidateSourceValueToLp
      (F := F) (mu := mu) hV)
    V
    (squareIntegrableCadlagCandidateSourceData
      (F := F) (mu := mu) hV hRows hControl hResidual w y hCommon)
    Z M Pcad hCad cutoff hData hUsual

/-! The two Jordan components are fed directly to the `L²` candidate
endpoint.  The common-a.e. cutoff is retained in the package for consumers
which need it, although the càdlàg construction itself only uses the common
Hilbert data. -/

theorem exists_squareIntegrableCadlagCandidates_of_commonStopJordanComponents
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
            ∃ (wPlus : ∀ n, TailConvexWeights n)
              (yPlus : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu)
                (2 : ENNReal)),
              ∃ hCommonPlus :
                SquareIntegrableIncreasingProcessCommonHilbertConvexificationData
                  hPlus hRowsPlus hControlPlus hResidualPlus wPlus yPlus,
                ∃ cutoffPlus,
                  SquareIntegrableIncreasingProcessCommonAESubsequenceData
                    hPlus hRowsPlus hControlPlus hResidualPlus wPlus yPlus
                      hCommonPlus cutoffPlus ∧
                  ∃ (ZPlus : Lp Real 2 mu) (MPlus PcadPlus : Process Ω),
                    SquareIntegrableIncreasingProcessCadlagCandidateData
                      hPlus hRowsPlus hControlPlus hResidualPlus wPlus yPlus
                        hCommonPlus ZPlus MPlus PcadPlus ∧
      ∃ hMinus : SquareIntegrableIncreasingProcessData (F := F) (mu := mu) Aminus T,
        ∃ hRowsMinus : SquareIntegrableIncreasingProcessCompensatorRowsData
            (F := F) (mu := mu) hMinus,
          ∃ hControlMinus : SquareIntegrableIncreasingProcessCompensatorRowControlData
              (F := F) (mu := mu) hMinus hRowsMinus,
            ∃ hResidualMinus : ∀ r,
                SquareIntegrableFactorialGridSampledResidualMartingaleData
                  (F := F) (mu := mu) hMinus hRowsMinus hControlMinus r,
              ∃ (wMinus : ∀ n, TailConvexWeights n)
                (yMinus : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu)
                  (2 : ENNReal)),
                ∃ hCommonMinus :
                  SquareIntegrableIncreasingProcessCommonHilbertConvexificationData
                    hMinus hRowsMinus hControlMinus hResidualMinus wMinus yMinus,
                  ∃ cutoffMinus,
                    SquareIntegrableIncreasingProcessCommonAESubsequenceData
                      hMinus hRowsMinus hControlMinus hResidualMinus wMinus yMinus
                        hCommonMinus cutoffMinus ∧
                    ∃ (ZMinus : Lp Real 2 mu) (MMinus PcadMinus : Process Ω),
                      SquareIntegrableIncreasingProcessCadlagCandidateData
                        hMinus hRowsMinus hControlMinus hResidualMinus wMinus yMinus
                          hCommonMinus ZMinus MMinus PcadMinus := by
  obtain ⟨hPlus, hRowsPlus, hControlPlus, hResidualPlus, wPlus, yPlus,
      hCommonPlus, cutoffPlus, hDataPlus, hMinus, hRowsMinus, hControlMinus,
      hResidualMinus, wMinus, yMinus, hCommonMinus, cutoffMinus, hDataMinus⟩ :=
    exists_squareIntegrableCommonAESubsequences_of_commonStopJordanComponents
      (F := F) (mu := mu) hNested bad Atilde Aplus Aminus cumulativeVariation hReg
  obtain ⟨ZPlus, MPlus, PcadPlus, hCadPlus⟩ :=
    exists_squareIntegrableIncreasingProcessCadlagCandidate
      (F := F) (mu := mu) hPlus hRowsPlus hControlPlus hResidualPlus
        wPlus yPlus hCommonPlus hUsual
  obtain ⟨ZMinus, MMinus, PcadMinus, hCadMinus⟩ :=
    exists_squareIntegrableIncreasingProcessCadlagCandidate
      (F := F) (mu := mu) hMinus hRowsMinus hControlMinus hResidualMinus
        wMinus yMinus hCommonMinus hUsual
  exact ⟨hPlus, hRowsPlus, hControlPlus, hResidualPlus, wPlus, yPlus,
    hCommonPlus, cutoffPlus, hDataPlus, ZPlus, MPlus, PcadPlus, hCadPlus,
    hMinus, hRowsMinus, hControlMinus, hResidualMinus, wMinus, yMinus,
    hCommonMinus, cutoffMinus, hDataMinus, ZMinus, MMinus, PcadMinus,
    hCadMinus⟩

/-! The Jordan components are now passed through the monotone
regularization endpoint.  In particular, the preceding candidate consumer is
the actual source of both common-a.e. packages used below. -/

theorem exists_squareIntegrableMonotoneRegularizedCadlagCandidates_of_commonStopJordanComponents
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
                ∃ (ZPlus : Lp Real 2 mu) (MPlus PcadPlus : Process Ω),
                  ∃ hCadPlus : SquareIntegrableIncreasingProcessCadlagCandidateData
                    hPlus hRowsPlus hControlPlus hResidualPlus wPlus yPlus
                      hCommonPlus ZPlus MPlus PcadPlus,
                    ∃ (badPlus : Set Ω) (PregPlus : Process Ω),
                      SquareIntegrableIncreasingProcessCadlagMonotoneRegularizationData
                        hPlus hRowsPlus hControlPlus hResidualPlus wPlus yPlus
                          hCommonPlus ZPlus MPlus PcadPlus
                            hCadPlus badPlus PregPlus ∧
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
                    cutoffMinus ∧
                  ∃ (ZMinus : Lp Real 2 mu) (MMinus PcadMinus : Process Ω),
                    ∃ hCadMinus : SquareIntegrableIncreasingProcessCadlagCandidateData
                      hMinus hRowsMinus hControlMinus hResidualMinus wMinus yMinus
                        hCommonMinus ZMinus MMinus PcadMinus,
                      ∃ (badMinus : Set Ω) (PregMinus : Process Ω),
                        SquareIntegrableIncreasingProcessCadlagMonotoneRegularizationData
                          hMinus hRowsMinus hControlMinus hResidualMinus wMinus yMinus
                            hCommonMinus ZMinus MMinus PcadMinus
                              hCadMinus badMinus PregMinus := by
  obtain ⟨hPlus, hRowsPlus, hControlPlus, hResidualPlus, wPlus, yPlus,
      hCommonPlus, cutoffPlus, hDataPlus, ZPlus, MPlus, PcadPlus, hCadPlus,
      hMinus, hRowsMinus, hControlMinus, hResidualMinus, wMinus, yMinus,
      hCommonMinus, cutoffMinus, hDataMinus, ZMinus, MMinus, PcadMinus,
      hCadMinus⟩ :=
    exists_squareIntegrableCadlagCandidates_of_commonStopJordanComponents
      hNested bad Atilde Aplus Aminus cumulativeVariation hReg
  obtain ⟨badPlus, PregPlus, hRegPlus⟩ :=
    exists_squareIntegrableIncreasingProcessCadlagMonotoneRegularization
      hPlus hRowsPlus hControlPlus hResidualPlus wPlus yPlus hCommonPlus
        cutoffPlus hDataPlus ZPlus MPlus PcadPlus hCadPlus hUsual
  obtain ⟨badMinus, PregMinus, hRegMinus⟩ :=
    exists_squareIntegrableIncreasingProcessCadlagMonotoneRegularization
      hMinus hRowsMinus hControlMinus hResidualMinus wMinus yMinus hCommonMinus
        cutoffMinus hDataMinus ZMinus MMinus PcadMinus hCadMinus hUsual
  exact ⟨hPlus, hRowsPlus, hControlPlus, hResidualPlus, wPlus, yPlus,
    hCommonPlus, cutoffPlus, hDataPlus, ZPlus, MPlus, PcadPlus, hCadPlus,
    badPlus, PregPlus, hRegPlus, hMinus, hRowsMinus, hControlMinus,
    hResidualMinus, wMinus, yMinus, hCommonMinus, cutoffMinus, hDataMinus,
    ZMinus, MMinus, PcadMinus, hCadMinus, badMinus, PregMinus, hRegMinus⟩

end HorizonFactorialGrid

end FTAPTheorem42
