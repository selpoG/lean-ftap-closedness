/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Compensator.CommonHilbertConvexificationCore
import FTAPTheorem42.Stochastic.Martingale.Regularization.ConditionalExpectationCadlagRegularization
import FTAPTheorem42.Stochastic.Process.ProcessLeftJump

/-!
# Source-independent càdlàg compensator candidates

This module contains the process-level part of the common Hilbert argument.
The row construction is deliberately hidden behind `CommonHilbertRowsData`.
The only source-specific input is a process with the usual path properties and
the conditional-expectation identity on the stopped skeleton.  In particular,
the candidate theorem does not assume the existence of a candidate process,
predictability, or monotonicity.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace HorizonFactorialGrid

theorem finset_smul_coeFn_ae_of_mem
    {μ : Measure Ω} (s : Finset Nat) (c : Nat → Real)
    (x : Nat → Lp Real (2 : ENNReal) μ) (f : Nat → Ω → Real)
    (hx : ∀ i, i ∈ s → ((x i : Ω → Real) =ᵐ[μ] f i)) :
    ((∑ i ∈ s, c i • x i : Lp Real (2 : ENNReal) μ) : Ω → Real) =ᵐ[μ]
      (fun omega => ∑ i ∈ s, c i * f i omega) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      filter_upwards [Lp.coeFn_zero (E := Real)
        (p := (2 : ENNReal)) μ] with ω hω
      simpa only [Finset.sum_empty, Pi.zero_apply] using hω
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      have htail :
          (((∑ j ∈ s, c j • x j : Lp Real (2 : ENNReal) μ) : Ω → Real)) =ᵐ[μ]
            (fun ω => ∑ j ∈ s, c j * f j ω) :=
        ih (fun j hj => hx j (by simp [hj]))
      filter_upwards [Lp.coeFn_add
          (c i • x i) (∑ j ∈ s, c j • x j),
        Lp.coeFn_smul (c i) (x i), htail, hx i (by simp)]
          with ω hadd hsmul htail hterm
      calc
        (((c i • x i) + ∑ j ∈ s, c j • x j :
            Lp Real (2 : ENNReal) μ) : Ω → Real) ω =
            ((c i • x i : Lp Real (2 : ENNReal) μ) : Ω → Real) ω +
              ((∑ j ∈ s, c j • x j : Lp Real (2 : ENNReal) μ) : Ω → Real) ω := hadd
        _ = (c i • ((x i : Lp Real (2 : ENNReal) μ) : Ω → Real)) ω +
              ∑ j ∈ s, c j * f j ω := by rw [hsmul, htail]
        _ = c i * f i ω + ∑ j ∈ s, c j * f j ω := by
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [hterm]
        _ = ∑ j ∈ insert i s, c j * f j ω := by
          rw [Finset.sum_insert hi]

variable {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
  {mu : Measure Ω} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {T : NNReal}
  {source : Ω → Real} {row : Nat → Process Ω}
  {residual : Nat → Ω → Real} {sourceBound rowBound : Real}

namespace CommonHilbertRowsData

/-! The conditional expectation operator at a skeleton time. -/

noncomputable def skeletonConditionalExpectation
    (s : NNReal) : Lp Real (2 : ENNReal) mu →L[Real] Lp Real (2 : ENNReal) mu :=
  (lpMeas Real Real (F s) 2 mu).subtypeL.comp
    (condExpL2 Real Real (F.le s))

/-! The source process supplies the regularity not present in the row API.
The last field is the one primitive bridge from the discrete residual rows to
the continuous-time skeleton.  It is only required eventually in the common
convexification index. -/

structure CadlagCandidateSourceData
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : ∀ n, TailConvexWeights n)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal))
    (hCommon : CommonHilbertConvexificationData h w y)
    (source_valueToLp : NNReal → Lp Real (2 : ENNReal) mu)
    (X : Process Ω) : Prop where
  source_valueToLp_coeFn_ae : ∀ t,
    ⇑(source_valueToLp t) =ᵐ[mu] X t
  source_terminal_ae : source =ᵐ[mu] X T
  source_stronglyAdapted : StronglyAdapted F X
  source_rightContinuous : ∀ omega t,
    ContinuousWithinAt (X · omega) (Ici t) t
  source_leftLimits : ProcessHasLeftLimits X
  source_constant_after : ∀ omega t, T ≤ t → X t omega = X T omega
  skeleton_condExp : ∀ j, ∀ᶠ n in atTop,
    skeletonConditionalExpectation (F := F) (mu := mu)
        (stoppedLimitSkeleton T j).1
        (h.residualConvexCoordinateToLp (w n)) =
      source_valueToLp (stoppedLimitSkeleton T j).1 -
        h.convexCoordinateToLp (w n) j

/-! The càdlàg process and its raw residual candidate. -/

structure CadlagCandidateData
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : ∀ n, TailConvexWeights n)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal))
    (hCommon : CommonHilbertConvexificationData h w y)
    (source_valueToLp : NNReal → Lp Real (2 : ENNReal) mu)
    (X : Process Ω)
    (hSource : CadlagCandidateSourceData h w y hCommon source_valueToLp X)
    (Z : Lp Real 2 mu) (M Pcad : Process Ω) : Prop where
  terminalLimit_eq : Z = h.coordinateLimit y 0
  terminal_residual_tendsto : Tendsto
    (fun n => h.residualConvexCoordinateToLp (w n)) atTop (𝓝 Z)
  M_martingale : Martingale M F mu
  M_rightContinuous : ∀ omega t,
    ContinuousWithinAt (M · omega) (Ici t) t
  M_leftLimits : ProcessHasLeftLimits M
  M_condExp : ∀ t, M t =ᵐ[mu]
    condExpMartingaleProcess mu F Z t
  Pcad_definition : Pcad = fun t omega => X t omega - M t omega
  Pcad_stronglyAdapted : StronglyAdapted F Pcad
  Pcad_rightContinuous : ∀ omega t,
    ContinuousWithinAt (Pcad · omega) (Ici t) t
  Pcad_leftLimits : ProcessHasLeftLimits Pcad
  Pcad_zero : Pcad 0 =ᵐ[mu] 0
  Pcad_constant_after : ∀ t, T ≤ t → Pcad t =ᵐ[mu] Pcad T
  Pcad_skeleton : ∀ j,
    Pcad (stoppedLimitSkeleton T j).1 =ᵐ[mu]
      (h.coordinateLimit y (j + 1) : Ω → Real)

theorem exists_cadlagCandidate
    (h : CommonHilbertRowsData F mu T source row residual sourceBound rowBound)
    (w : ∀ n, TailConvexWeights n)
    (y : lp (fun _ : Nat => Lp Real (2 : ENNReal) mu) (2 : ENNReal))
    (hCommon : CommonHilbertConvexificationData h w y)
    (source_valueToLp : NNReal → Lp Real (2 : ENNReal) mu)
    (X : Process Ω)
    (hSource : CadlagCandidateSourceData h w y hCommon source_valueToLp X)
    (hUsual : Filtration.UsualConditions mu F) :
    ∃ (Z : Lp Real 2 mu) (M Pcad : Process Ω),
      CadlagCandidateData h w y hCommon source_valueToLp X hSource Z M Pcad := by
  let Z : Lp Real 2 mu := h.coordinateLimit y 0
  obtain ⟨M, hMMartingale, hMRight, hMLeft, hMVersion⟩ :=
    exists_cadlagMartingaleVersion_condExpMartingaleProcess F hUsual Z
  let Pcad : Process Ω := fun t omega => X t omega - M t omega
  have hPStrong : StronglyAdapted F Pcad := by
    intro t
    dsimp [Pcad]
    exact (hSource.source_stronglyAdapted t).sub
      (hMMartingale.stronglyAdapted t)
  have hPRight : ∀ omega t,
      ContinuousWithinAt (Pcad · omega) (Ici t) t := by
    intro omega t
    dsimp [Pcad]
    exact (hSource.source_rightContinuous omega t).sub (hMRight omega t)
  have hPLeft : ProcessHasLeftLimits Pcad := by
    simpa only [Pcad] using hSource.source_leftLimits.sub hMLeft
  have hPDefinition : Pcad = fun t omega => X t omega - M t omega := by
    rfl
  have hTerminalTendsto : Tendsto
      (fun n => h.residualConvexCoordinateToLp (w n)) atTop (𝓝 Z) := by
    simpa only [Z] using hCommon.residual_coordinate_tendsto
  have hSkeleton (j : Nat) :
      Pcad (stoppedLimitSkeleton T j).1 =ᵐ[mu]
        (h.coordinateLimit y (j + 1) : Ω → Real) := by
    let s : NNReal := (stoppedLimitSkeleton T j).1
    let L : Lp Real 2 mu := h.coordinateLimit y (j + 1)
    let target : Nat → Lp Real 2 mu := fun n =>
      source_valueToLp s - h.convexCoordinateToLp (w n) j
    have hTargetTendsto : Tendsto (fun n => target n) atTop
        (𝓝 (source_valueToLp s - L)) := by
      have hDiff : Tendsto (fun n => source_valueToLp s -
          h.convexCoordinateToLp (w n) j) atTop
          (𝓝 (source_valueToLp s - L)) := by
        simpa only [L] using (tendsto_const_nhds.sub
          (hCommon.skeleton_coordinate_tendsto j))
      exact hDiff.congr' (Filter.Eventually.of_forall fun n => rfl)
    have hCE_tendsto : Tendsto
        (fun n => skeletonConditionalExpectation (F := F) (mu := mu) s
          (h.residualConvexCoordinateToLp (w n))) atTop
        (𝓝 (skeletonConditionalExpectation (F := F) (mu := mu) s Z)) := by
      exact (skeletonConditionalExpectation (F := F) (mu := mu) s).continuous.continuousAt.tendsto
        |>.comp hTerminalTendsto
    have hCE_target : ∀ᶠ n in atTop,
        skeletonConditionalExpectation (F := F) (mu := mu) (stoppedLimitSkeleton T j).1
          (h.residualConvexCoordinateToLp (w n)) = target n := by
      simpa only [target, s] using hSource.skeleton_condExp j
    have hCE_target_tendsto : Tendsto
        (fun n => skeletonConditionalExpectation (F := F) (mu := mu) s
          (h.residualConvexCoordinateToLp (w n))) atTop
        (𝓝 (source_valueToLp s - L)) := by
      exact hTargetTendsto.congr' (Filter.EventuallyEq.symm hCE_target)
    have hCELimit : skeletonConditionalExpectation (F := F) (mu := mu) s Z =
        source_valueToLp s - L :=
      tendsto_nhds_unique hCE_tendsto hCE_target_tendsto
    have hZMem : MemLp (Z : Ω → Real) (2 : ENNReal) mu := Lp.memLp Z
    have hCEBridge := hZMem.condExpL2_ae_eq_condExp (𝕜 := Real) (F.le s)
    rw [Lp.toLp_coeFn Z hZMem] at hCEBridge
    have hMtoCE : M s =ᵐ[mu]
        (skeletonConditionalExpectation (F := F) (mu := mu) s Z : Ω → Real) := by
      filter_upwards [hMVersion s, hCEBridge] with omega hM hCE
      exact hM.trans hCE.symm
    have hSourceRaw := hSource.source_valueToLp_coeFn_ae s
    have hDiffRaw :
        ((source_valueToLp s - L : Lp Real 2 mu) : Ω → Real) =ᵐ[mu]
          (fun omega => X s omega - (L : Ω → Real) omega) := by
      filter_upwards [Lp.coeFn_sub (source_valueToLp s) L,
        hSourceRaw] with omega hSub hX
      rw [Pi.sub_apply] at hSub
      rw [hSub, hX]
    have hCELimitRaw := congrArg
      (fun z : Lp Real 2 mu => (z : Ω → Real)) hCELimit
    have hMdiff : M s =ᵐ[mu]
        (fun omega => X s omega - (L : Ω → Real) omega) := by
      filter_upwards [hMtoCE, hDiffRaw] with omega hM hDiff
      exact hM.trans (congrFun hCELimitRaw omega |>.trans hDiff)
    filter_upwards [hMdiff] with omega hM
    dsimp [Pcad, L, s] at hM ⊢
    rw [hM]
    ring
  have hPZero : Pcad 0 =ᵐ[mu] 0 := by
    have hZeroTime : (stoppedLimitSkeleton T 0).1 = 0 := by
      change (grid T (Nat.unpair 0).1).sampledTime
        (Nat.unpair 0).2 = 0
      simp [grid, ChronologicalGrid.sampledTime, ChronologicalGrid.natIndex]
    have hCoordinateZero (n : Nat) :
        h.convexCoordinateToLp (w n) 0 = 0 := by
      apply Lp.ext
      have hCoordinate := hCommon.skeleton_coordinate_coeFn_ae n 0
      filter_upwards [hCoordinate] with omega hCoordinateOmega
      rw [hZeroTime] at hCoordinateOmega
      exact hCoordinateOmega.trans
        ((congrFun (hCommon.row_zero n) omega).trans (by simp))
    have hZeroTendsto : Tendsto
        (fun n => h.convexCoordinateToLp (w n) 0) atTop
          (𝓝 (0 : Lp Real 2 mu)) := by
      exact (tendsto_const_nhds : Tendsto (fun _ : Nat =>
        (0 : Lp Real 2 mu)) atTop (𝓝 0)).congr'
        (Filter.Eventually.of_forall fun n => (hCoordinateZero n).symm)
    have hLimitZero : h.coordinateLimit y (0 + 1) =
        (0 : Lp Real 2 mu) :=
      tendsto_nhds_unique (hCommon.skeleton_coordinate_tendsto 0)
        hZeroTendsto
    have hZero := hSkeleton 0
    rw [hZeroTime] at hZero
    rw [hLimitZero] at hZero
    filter_upwards [hZero] with omega hZeroOmega
    change Pcad 0 omega = (0 : Real)
    simpa using hZeroOmega
  refine ⟨Z, M, Pcad, {
    terminalLimit_eq := by rfl
    terminal_residual_tendsto := hTerminalTendsto
    M_martingale := hMMartingale
    M_rightContinuous := hMRight
    M_leftLimits := hMLeft
    M_condExp := hMVersion
    Pcad_definition := hPDefinition
    Pcad_stronglyAdapted := hPStrong
    Pcad_rightContinuous := hPRight
    Pcad_leftLimits := hPLeft
    Pcad_zero := hPZero
    Pcad_constant_after := by
      have hSourceAE : (h.sourceToLp : Ω → Real) =ᵐ[mu] X T :=
        h.sourceToLp_coeFn_ae.trans hSource.source_terminal_ae
      have hSourceLpMeas : AEStronglyMeasurable[F T]
          (h.sourceToLp : Ω → Real) mu :=
        (aestronglyMeasurable_congr hSourceAE).2
          (hSource.source_stronglyAdapted T).aestronglyMeasurable
      have hSourceMeas : AEStronglyMeasurable[F T] source mu :=
        (aestronglyMeasurable_congr h.sourceToLp_coeFn_ae).1 hSourceLpMeas
      have hResidualRowMeas : ∀ n,
          AEStronglyMeasurable[F T] (h.residualConvexRow (w n)) mu := by
        intro n
        rw [h.residualConvexRow_eq_source_sub_compensator (w n)]
        exact hSourceMeas.sub
          ((hCommon.row_isStronglyPredictable n).stronglyAdapted T).aestronglyMeasurable
      have hCoordinateMeas : ∀ n,
          AEStronglyMeasurable[F T]
            (h.residualConvexCoordinateToLp (w n) : Ω → Real) mu := by
        intro n
        apply (aestronglyMeasurable_congr
          (hCommon.residual_coordinate_coeFn_ae n)).2
        exact hResidualRowMeas n
      have hZFT : AEStronglyMeasurable[F T] (Z : Ω → Real) mu := by
        change Z ∈ {f : Lp Real 2 mu |
          AEStronglyMeasurable[F T] (f : Ω → Real) mu}
        apply (isClosed_aestronglyMeasurable (F := Real)
          (p := (2 : ENNReal)) (μ := mu) (F.le T)).mem_of_tendsto
          hTerminalTendsto
        exact Filter.Eventually.of_forall hCoordinateMeas
      have hZMem : MemLp (Z : Ω → Real) (2 : ENNReal) mu := Lp.memLp Z
      have hCondT : condExpMartingaleProcess mu F Z T =ᵐ[mu]
          (Z : Ω → Real) := by
        change mu[(Z : Ω → Real) | F T] =ᵐ[mu] (Z : Ω → Real)
        exact condExp_of_aestronglyMeasurable' (F.le T) hZFT
          (hZMem.integrable (by norm_num))
      have hMTerminal : M T =ᵐ[mu] (Z : Ω → Real) :=
        (hMVersion T).trans hCondT
      have hMConstant : ∀ t, T ≤ t → M t =ᵐ[mu] M T := by
        intro t ht
        have hZFt : AEStronglyMeasurable[F t] (Z : Ω → Real) mu :=
          hZFT.mono (F.mono ht)
        have hCond : condExpMartingaleProcess mu F Z t =ᵐ[mu]
            (Z : Ω → Real) := by
          change mu[(Z : Ω → Real) | F t] =ᵐ[mu] (Z : Ω → Real)
          exact condExp_of_aestronglyMeasurable' (F.le t) hZFt
            (hZMem.integrable (by norm_num))
        exact (hMVersion t).trans (hCond.trans hMTerminal.symm)
      intro t ht
      filter_upwards [hMConstant t ht] with omega hM
      dsimp [Pcad]
      rw [hSource.source_constant_after omega t ht, hM]
    Pcad_skeleton := hSkeleton }⟩

end CommonHilbertRowsData

end HorizonFactorialGrid

end FTAPTheorem42
