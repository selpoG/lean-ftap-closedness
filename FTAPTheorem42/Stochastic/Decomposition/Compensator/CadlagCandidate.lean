/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.CommonHilbertConvexification
import FTAPTheorem42.Stochastic.Decomposition.Compensator.CadlagCandidateCore
import FTAPTheorem42.Stochastic.Martingale.Regularization.ConditionalExpectationCadlagRegularization
import FTAPTheorem42.Stochastic.Process.ProcessLeftJump

/-!
# The càdlàg compensator candidate from the common terminal residual

This module is the first feasibility slice of the process-level compensator
boundary.  The terminal residual coordinate of the common Hilbert
convexification is used as an `L²` terminal variable.  Conditional-expectation
regularization then gives one everywhere càdlàg true martingale `M`, and the
candidate `Pcad := V - M` is formed from that same process.

Only the properties available at this stage are recorded here.  In
particular, no predictability, monotonicity, ucp convergence, or
process-indistinguishability with a raw predictable limit is asserted.
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

omit [SigmaFiniteFiltration mu F] in
private theorem skeleton_coordinate_condExp_eq
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      FactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows r)
    (w : ∀ n, TailConvexWeights n) (j n : Nat)
    (hjn : (Nat.unpair j).1 ≤ n) :
    ((lpMeas Real Real
        (F (stoppedLimitSkeleton T j).1) 2 mu).subtypeL.comp
      (condExpL2 Real Real
        (F.le (stoppedLimitSkeleton T j).1)))
        (residualConvexCoordinateToLp hV hRows hControl (w n)) =
      ((hV.value_memLp_two (mu := mu)
        (t := (stoppedLimitSkeleton T j).1)
        (stoppedLimitSkeleton T j).2).sub
        (compensatorConvexRow_value_memLp_two
          (F := F) (mu := mu) hV hRows hControl (w n)
          (stoppedLimitSkeleton T j).1)).toLp
        (V (stoppedLimitSkeleton T j).1 -
          compensatorConvexRow (V := V) (F := F) (mu := mu)
            (T := T) (C := C) (w n) (stoppedLimitSkeleton T j).1) := by
  classical
  let s : NNReal := (stoppedLimitSkeleton T j).1
  let hs : s ≤ T := (stoppedLimitSkeleton T j).2
  let CE : Lp Real 2 mu →L[Real] Lp Real 2 mu :=
    (lpMeas Real Real (F s) 2 mu).subtypeL.comp
      (condExpL2 Real Real (F.le s))
  have hComponent (r : Nat) (hr : (Nat.unpair j).1 ≤ r) :
      CE (terminalResidualToLp hV hRows hControl r) =
        ((hV.value_memLp_two (mu := mu) (t := s) hs).sub
          (hControl.value_memLp_two r s)).toLp
          (V s - predictableCompensatorProcess V F mu T C r s) := by
    let k : Fin (size T r + 1) :=
      approxIndex T s hs r
    have hk_le : k.1 ≤ size T r := Nat.lt_succ_iff.mp k.isLt
    have htime : (grid T r).sampledTime k.1 = s := by
      rw [(grid T r).sampledTime_fin_eq k]
      exact grid_time_approxIndex_stoppedLimitSkeleton_eq T j hr
    have hRaw := (hResidual r).terminal_condExp k.1 hk_le
    have hRaw' : factorialGridSampledResidual V F mu T C r k.1 =ᵐ[mu]
        mu[factorialGridSampledResidual V F mu T C r (size T r) |
          F s] := by
      simpa only [ChronologicalGrid.sampledFiltration_apply, htime] using hRaw
    have hMem : MemLp
        (terminalResidualToLp hV hRows hControl r : Ω → Real)
        (2 : ENNReal) mu :=
      Lp.memLp (terminalResidualToLp hV hRows hControl r)
    have hBridge := hMem.condExpL2_ae_eq_condExp (𝕜 := Real)
      (F.le s)
    rw [Lp.toLp_coeFn (terminalResidualToLp hV hRows hControl r) hMem]
      at hBridge
    have hTerminal := terminalResidualToLp_coeFn_ae
      (F := F) (mu := mu) hV hRows hControl hResidual r
    have hCond : mu[
        (terminalResidualToLp hV hRows hControl r : Ω → Real) | F s] =ᵐ[mu]
        mu[factorialGridSampledResidual V F mu T C r (size T r) | F s] :=
      condExp_congr_ae hTerminal
    have hTargetMem := (hV.value_memLp_two (mu := mu) (t := s) hs).sub
      (hControl.value_memLp_two r s)
    have hTargetRaw := hTargetMem.coeFn_toLp
    apply Lp.ext
    filter_upwards [hBridge, hCond, hRaw', hTargetRaw] with omega
        hBridgeOmega hCondOmega hRawOmega hTargetOmega
    change ((condExpL2 Real Real (F.le s)
      (terminalResidualToLp hV hRows hControl r) :
        lpMeas Real Real (F s) 2 mu) : Ω → Real) omega = _
    rw [hBridgeOmega, hCondOmega, ← hRawOmega]
    change V ((grid T r).sampledTime k.1) omega -
        predictableCompensatorProcess V F mu T C r
          ((grid T r).sampledTime k.1) omega = _
    rw [htime]
    exact hTargetOmega.symm
  let Pn : Lp Real 2 mu :=
    residualConvexCoordinateToLp hV hRows hControl (w n)
  have hCEsum : CE Pn =
      ((hV.value_memLp_two (mu := mu) (t := s) hs).sub
        (compensatorConvexRow_value_memLp_two
          (F := F) (mu := mu) hV hRows hControl (w n) s)).toLp
        (V s - compensatorConvexRow (V := V) (F := F) (mu := mu)
          (T := T) (C := C) (w n) s) := by
    have hTargetRaw :=
      ((hV.value_memLp_two (mu := mu) (t := s) hs).sub
        (compensatorConvexRow_value_memLp_two
          (F := F) (mu := mu) hV hRows hControl (w n) s)).coeFn_toLp
    have hVec :
        ((∑ r ∈ (w n).support, (w n).weight r •
          CE (terminalResidualToLp hV hRows hControl r) :
          Lp Real 2 mu) : Ω → Real) =ᵐ[mu]
          (w n).apply (fun r => fun omega =>
            V s omega - predictableCompensatorProcess V F mu T C r s omega) := by
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
            V s omega - predictableCompensatorProcess V F mu T C r s omega) =
          (V s - compensatorConvexRow (V := V) (F := F) (mu := mu)
            (T := T) (C := C) (w n) s) := by
      funext omega
      simp only [TailConvexWeights.apply]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, (w n).sum_eq_one,
        one_mul]
      rfl
    have hCEPn : CE Pn =
        ∑ r ∈ (w n).support, (w n).weight r •
          CE (terminalResidualToLp hV hRows hControl r) := by
      unfold Pn residualConvexCoordinateToLp
      unfold TailConvexWeights.applyVector
      rw [map_sum]
      simp only [map_smul]
    have hLeft :
        (⇑(CE Pn) =ᵐ[mu]
          (V s - compensatorConvexRow (V := V) (F := F) (mu := mu)
            (T := T) (C := C) (w n) s)) := by
      rw [hCEPn]
      simpa only using hVec.trans
          (Eventually.of_forall (fun omega => congrFun hApply omega))
    apply Lp.ext
    exact hLeft.trans hTargetRaw.symm
  exact hCEsum

/-! ## The bounded source adapter -/

noncomputable def boundedCadlagCandidateSourceValueToLp
    (hV : BoundedIncreasingProcessData (F := F) V T C) :
    NNReal → Lp Real (2 : ENNReal) mu :=
  fun t => (hV.value_memLp_two (mu := mu) (t := min t T)
      (min_le_right t T)).toLp (V (min t T))

omit [SigmaFiniteFiltration mu F] in
theorem boundedCadlagCandidateSourceValueToLp_coeFn_ae
    (hV : BoundedIncreasingProcessData (F := F) V T C) (t : NNReal) :
    ⇑(boundedCadlagCandidateSourceValueToLp (F := F) (mu := mu) hV t) =ᵐ[mu]
      V t := by
  by_cases ht : t ≤ T
  · have hmin : min t T = t := min_eq_left ht
    simpa only [boundedCadlagCandidateSourceValueToLp, hmin] using
      (MemLp.coeFn_toLp (hV.value_memLp_two (mu := mu) (t := t) ht))
  · have hTt : T ≤ t := le_of_not_ge ht
    have hmin : min t T = T := min_eq_right hTt
    have hconst : V t = V T := by
      funext omega
      exact hV.constant_after omega t hTt
    filter_upwards [MemLp.coeFn_toLp
      (hV.value_memLp_two (mu := mu) (t := min t T)
        (min_le_right t T))] with omega hminValue
    calc
      ((boundedCadlagCandidateSourceValueToLp
        (F := F) (mu := mu) hV t : Ω → Real) omega) =
          V (min t T) omega := by
            exact hminValue
      _ = V T omega := by rw [hmin]
      _ = V t omega := (congrFun hconst omega).symm

omit [SigmaFiniteFiltration mu F] in
theorem boundedCadlagCandidateSourceData
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      FactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows r)
    (w : ∀ n, TailConvexWeights n)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal))
    (hCommon : FactorialGridPredictableCompensatorCommonHilbertConvexificationData
      hV hRows hControl hResidual w y) :
    CommonHilbertRowsData.CadlagCandidateSourceData
      (boundedCommonHilbertRowsData hV hRows hControl) w y
      (boundedCommonHilbertConvexificationCoreData
        hV hRows hControl hResidual w y hCommon)
      (boundedCadlagCandidateSourceValueToLp (F := F) (mu := mu) hV) V := by
  let h := boundedCommonHilbertRowsData (F := F) (mu := mu) hV hRows hControl
  let q := boundedCadlagCandidateSourceValueToLp (F := F) (mu := mu) hV
  refine {
    source_valueToLp_coeFn_ae := boundedCadlagCandidateSourceValueToLp_coeFn_ae
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
  have hOld := skeleton_coordinate_condExp_eq hV hRows hControl hResidual w j n hn
  have hs : (stoppedLimitSkeleton T j).1 ≤ T :=
    (stoppedLimitSkeleton T j).2
  have hq : q (stoppedLimitSkeleton T j).1 =
      (hV.value_memLp_two (mu := mu)
        (t := (stoppedLimitSkeleton T j).1) hs).toLp
        (V (stoppedLimitSkeleton T j).1) := by
    have htime : V (min (stoppedLimitSkeleton T j).1 T) =
        V (stoppedLimitSkeleton T j).1 := by
      rw [min_eq_left hs]
    simpa only [q, boundedCadlagCandidateSourceValueToLp] using
      (MemLp.toLp_congr
        (hV.value_memLp_two (mu := mu)
          (t := min (stoppedLimitSkeleton T j).1 T)
          (min_le_right _ _))
        (hV.value_memLp_two (mu := mu)
          (t := (stoppedLimitSkeleton T j).1) hs)
        (Filter.Eventually.of_forall (fun omega =>
          congrFun htime omega)))
  change CommonHilbertRowsData.skeletonConditionalExpectation
      (F := F) (mu := mu) (stoppedLimitSkeleton T j).1
        ((boundedCommonHilbertRowsData hV hRows hControl).residualConvexCoordinateToLp
          (w n)) =
      q (stoppedLimitSkeleton T j).1 -
        (boundedCommonHilbertRowsData hV hRows hControl).convexCoordinateToLp
          (w n) j
  rw [hq]
  have hRhsEq :
      (hV.value_memLp_two (mu := mu)
          (t := (stoppedLimitSkeleton T j).1) hs).toLp
          (V (stoppedLimitSkeleton T j).1) -
        compensatorConvexCoordinateToLp hV hRows hControl (w n) j =
      ((hV.value_memLp_two (mu := mu)
          (t := (stoppedLimitSkeleton T j).1) hs).sub
        (compensatorConvexRow_value_memLp_two
          (F := F) (mu := mu) hV hRows hControl (w n)
          (stoppedLimitSkeleton T j).1)).toLp
        (V (stoppedLimitSkeleton T j).1 -
          compensatorConvexRow (V := V) (F := F) (mu := mu)
            (T := T) (C := C) (w n) (stoppedLimitSkeleton T j).1) := by
    apply Lp.ext
    have hSub := Lp.coeFn_sub
      ((hV.value_memLp_two (mu := mu)
        (t := (stoppedLimitSkeleton T j).1) hs).toLp
        (V (stoppedLimitSkeleton T j).1))
      (compensatorConvexCoordinateToLp hV hRows hControl (w n) j)
    have hTarget := ((hV.value_memLp_two (mu := mu)
          (t := (stoppedLimitSkeleton T j).1) hs).sub
        (compensatorConvexRow_value_memLp_two
          (F := F) (mu := mu) hV hRows hControl (w n)
          (stoppedLimitSkeleton T j).1)).coeFn_toLp
    have hVRaw := (hV.value_memLp_two (mu := mu)
      (t := (stoppedLimitSkeleton T j).1) hs).coeFn_toLp
    have hCoord := compensatorConvexCoordinateToLp_coeFn_ae
      (F := F) (mu := mu) hV hRows hControl (w n) j
    filter_upwards [hSub, hTarget, hVRaw, hCoord] with omega
        hSubOmega hTargetOmega hVOmega hCoordOmega
    calc
      ((↑((hV.value_memLp_two (mu := mu)
        (t := (stoppedLimitSkeleton T j).1) hs).toLp
        (V (stoppedLimitSkeleton T j).1) -
        compensatorConvexCoordinateToLp hV hRows hControl (w n) j) :
          Ω → Real) omega) =
          ((↑((hV.value_memLp_two (mu := mu)
            (t := (stoppedLimitSkeleton T j).1) hs).toLp
            (V (stoppedLimitSkeleton T j).1)) : Ω → Real) omega) -
            ((↑(compensatorConvexCoordinateToLp hV hRows hControl
              (w n) j) : Ω → Real) omega) := by
              exact hSubOmega
      _ = V (stoppedLimitSkeleton T j).1 omega -
          compensatorConvexRow (V := V) (F := F) (mu := mu)
            (T := T) (C := C) (w n)
              (stoppedLimitSkeleton T j).1 omega := by
            rw [hVOmega, hCoordOmega]
      _ = ((↑(((hV.value_memLp_two (mu := mu)
          (t := (stoppedLimitSkeleton T j).1) hs).sub
        (compensatorConvexRow_value_memLp_two
          (F := F) (mu := mu) hV hRows hControl (w n)
          (stoppedLimitSkeleton T j).1)).toLp
        (V (stoppedLimitSkeleton T j).1 -
          compensatorConvexRow (V := V) (F := F) (mu := mu)
            (T := T) (C := C) (w n) (stoppedLimitSkeleton T j).1)) :
          Ω → Real) omega) := hTargetOmega.symm
  exact hOld.trans hRhsEq.symm

structure FactorialGridPredictableCompensatorCadlagCandidateData
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      FactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows r)
    (hCommon : FactorialGridPredictableCompensatorCommonHilbertConvexificationData
      hV hRows hControl hResidual w y)
    (Z : Lp Real 2 mu) (M Pcad : Process Ω) : Prop where
  terminalLimit_eq : Z = commonCoordinateLimit C y 0
  terminal_residual_tendsto : Tendsto
    (fun n => residualConvexCoordinateToLp hV hRows hControl (w n))
    atTop (𝓝 Z)
  M_martingale : Martingale M F mu
  M_rightContinuous : ∀ omega t,
    ContinuousWithinAt (M · omega) (Ici t) t
  M_leftLimits : ProcessHasLeftLimits M
  M_condExp : ∀ t, M t =ᵐ[mu]
    condExpMartingaleProcess mu F Z t
  Pcad_definition : Pcad = fun t omega => V t omega - M t omega
  Pcad_stronglyAdapted : StronglyAdapted F Pcad
  Pcad_rightContinuous : ∀ omega t,
    ContinuousWithinAt (Pcad · omega) (Ici t) t
  Pcad_leftLimits : ProcessHasLeftLimits Pcad
  Pcad_zero : Pcad 0 =ᵐ[mu] 0
  Pcad_constant_after : ∀ t, T ≤ t → Pcad t =ᵐ[mu] Pcad T
  Pcad_skeleton : ∀ j,
    Pcad (stoppedLimitSkeleton T j).1 =ᵐ[mu]
      (commonCoordinateLimit C y (j + 1) : Ω → Real)

/-! The bounded declaration is an adapter for the source-independent
candidate core.  Its signature is kept unchanged for the downstream bounded
regularization files. -/

theorem exists_factorialGridPredictableCompensatorCadlagCandidate
    (hV : BoundedIncreasingProcessData (F := F) V T C)
    (hRows : FactorialGridPredictableCompensatorRowsData
      (F := F) (mu := mu) hV)
    (hControl : FactorialGridPredictableCompensatorRowControlData
      (F := F) (mu := mu) hV hRows)
    (hResidual : ∀ r,
      FactorialGridSampledResidualMartingaleData
        (F := F) (mu := mu) hV hRows r)
    (w : ∀ n, TailConvexWeights n)
    (y : lp (fun _ : Nat => Lp Real 2 mu) (2 : ENNReal))
    (hCommon : FactorialGridPredictableCompensatorCommonHilbertConvexificationData
      hV hRows hControl hResidual w y)
    (hUsual : Filtration.UsualConditions mu F) :
    ∃ (Z : Lp Real 2 mu) (M Pcad : Process Ω),
      FactorialGridPredictableCompensatorCadlagCandidateData
        hV hRows hControl hResidual hCommon Z M Pcad := by
  let hCore := boundedCommonHilbertConvexificationCoreData
    hV hRows hControl hResidual w y hCommon
  let hSource := boundedCadlagCandidateSourceData
    hV hRows hControl hResidual w y hCommon
  obtain ⟨Z, M, Pcad, hCad⟩ :=
    CommonHilbertRowsData.exists_cadlagCandidate
      (boundedCommonHilbertRowsData hV hRows hControl) w y hCore
        (boundedCadlagCandidateSourceValueToLp (F := F) (mu := mu) hV)
        V hSource hUsual
  refine ⟨Z, M, Pcad, {
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
    Pcad_skeleton := hCad.Pcad_skeleton }⟩

/-! The common-stop Jordan construction supplies the hypotheses of the
cadlag-candidate endpoint separately for the positive and negative Jordan
components.  The two convexifications, and hence the two candidates, are
kept independent.  This is only a consumer of the already constructed 7C
data; it does not identify the two weights or assert the predictable bridge.
-/

theorem exists_cadlagCandidates_of_commonStopJordanComponents
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
              FactorialGridPredictableCompensatorCadlagCandidateData
                hPlus hRowsPlus hControlPlus hResidualPlus
                  hCommonPlus ZPlus MPlus PcadPlus ∧
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
              FactorialGridPredictableCompensatorCadlagCandidateData
                hMinus hRowsMinus hControlMinus hResidualMinus
                  hCommonMinus ZMinus MMinus PcadMinus := by
  obtain ⟨hPlus, hRowsPlus, hControlPlus, hResidualPlus, wPlus, yPlus,
      hPlusData, hMinus, hRowsMinus, hControlMinus, hResidualMinus, wMinus,
      yMinus, hMinusData⟩ :=
    exists_commonHilbertConvexifications_of_commonStopJordanComponents
      (F := F) (mu := mu) endpoint bad Atilde Aplus Aminus
        cumulativeVariation hReg
  obtain ⟨ZPlus, MPlus, PcadPlus, hPlusCad⟩ :=
    exists_factorialGridPredictableCompensatorCadlagCandidate
      hPlus hRowsPlus hControlPlus hResidualPlus wPlus yPlus hPlusData hUsual
  obtain ⟨ZMinus, MMinus, PcadMinus, hMinusCad⟩ :=
    exists_factorialGridPredictableCompensatorCadlagCandidate
      hMinus hRowsMinus hControlMinus hResidualMinus wMinus yMinus hMinusData hUsual
  exact ⟨hPlus, hRowsPlus, hControlPlus, hResidualPlus, wPlus, yPlus,
    hPlusData, ZPlus, MPlus, PcadPlus, hPlusCad,
    hMinus, hRowsMinus, hControlMinus, hResidualMinus, wMinus, yMinus,
    hMinusData, ZMinus, MMinus, PcadMinus, hMinusCad⟩

end HorizonFactorialGrid

end FTAPTheorem42
