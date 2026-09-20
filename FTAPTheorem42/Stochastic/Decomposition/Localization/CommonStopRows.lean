/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Source.RowDecomposition
import FTAPTheorem42.Stochastic.Decomposition.Source.CommonGate
import FTAPTheorem42.Stochastic.Martingale.Basic.BoundedStoppingOptionalSampling
import FTAPTheorem42.Stochastic.Martingale.Basic.RightContinuousStoppedMartingale

/-!
# Common stopping of selected inverse rows

The common-gate endpoint supplies exact hitting rows at the selected levels.
Each such row is then stopped once more at the common infimum of the hitting
times.  The martingale part is stopped by optional sampling.  The residual is
not given any new finite-variation semantics: its base-grid estimate is
reproved, with the one possible off-grid crossing increment charged explicitly
to the already available residual sup bound.

`CommonStoppedRowsData` and `CommonStoppedRowsEndpoint` are result bundles
assembled by the producers below.  In particular, their decomposition and
bound fields are established by the row and common-gate consumers; no final
decomposition conclusion is assumed as an input capability.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

/-- Convex averages of the common stopped source, shared by both row constructions. -/
noncomputable def commonStoppedRowsSourceConvexRow
    {S : Process Omega}
    {alpha : Omega → WithTop NNReal}
    (v : ∀ n, TailConvexWeights n) (n : Nat) : Process Omega :=
  fun t omega =>
    (v n).apply (fun _ omega =>
      MeasureTheory.stoppedProcess S alpha t omega - S 0 omega) omega

/-! ## A finite-grid estimate for an additional common stop -/

omit [MeasurableSpace Omega] in
theorem stoppedProcess_gridVariation_le_add_two_of_sup_at
    {B : Process Omega}
    (T : NNReal) (r : Nat) (tau : Omega → WithTop NNReal)
    (omega : Omega)
    (hTauT : tau omega ≤ (T : WithTop NNReal))
    {V C : Real} (hC : 0 ≤ C)
    (hVar :
      (∑ k ∈ Finset.range (size T r),
        |B ((grid T r).sampledTime (k + 1)) omega -
          B ((grid T r).sampledTime k) omega|) ≤ V)
    (hSup : ∀ t, t ≤ T → |B t omega| ≤ C) :
      (∑ k ∈ Finset.range (size T r),
        |MeasureTheory.stoppedProcess B tau
              ((grid T r).sampledTime (k + 1)) omega -
          MeasureTheory.stoppedProcess B tau
              ((grid T r).sampledTime k) omega|) ≤ V + 2 * C := by
  let N := size T r
  let G := grid T r
  let crossing : Finset Nat := (Finset.range N).filter fun k =>
    (G.sampledTime k : WithTop NNReal) < tau omega ∧
      tau omega < (G.sampledTime (k + 1) : WithTop NNReal)
  have hcross_subset : crossing ⊆ Finset.range N := by
    intro k hk
    exact (Finset.mem_filter.mp hk).1
  have hcross_card : crossing.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    by_contra hij
    rcases lt_or_gt_of_ne hij with hij' | hji'
    · have hs : G.sampledTime (i + 1) ≤ G.sampledTime j := by
        exact G.sampledTime_mono (by omega)
      have hi' := (Finset.mem_filter.mp hi).2
      have hj' := (Finset.mem_filter.mp hj).2
      have hbad : (G.sampledTime (i + 1) : WithTop NNReal) <
          (G.sampledTime (i + 1) : WithTop NNReal) := by
        exact (WithTop.coe_le_coe.mpr hs).trans_lt
          (hj'.1.trans hi'.2)
      exact (lt_irrefl _ hbad).elim
    · have hs : G.sampledTime (j + 1) ≤ G.sampledTime i := by
        exact G.sampledTime_mono (by omega)
      have hj' := (Finset.mem_filter.mp hj).2
      have hi' := (Finset.mem_filter.mp hi).2
      have hbad : (G.sampledTime (j + 1) : WithTop NNReal) <
          (G.sampledTime (j + 1) : WithTop NNReal) := by
        exact (WithTop.coe_le_coe.mpr hs).trans_lt
          (hi'.1.trans hj'.2)
      exact (lt_irrefl _ hbad).elim
  have hterm : ∀ k ∈ Finset.range N,
      |MeasureTheory.stoppedProcess B tau (G.sampledTime (k + 1)) omega -
          MeasureTheory.stoppedProcess B tau (G.sampledTime k) omega| ≤
        |B (G.sampledTime (k + 1)) omega - B (G.sampledTime k) omega| +
          (if k ∈ crossing then 2 * C else 0) := by
    intro k hk
    have hkN : k < N := Finset.mem_range.mp hk
    have htime_k : G.sampledTime k ≤ T := by
      exact (G.sampledTime_mono hkN.le).trans_eq (sampledTime_size T r)
    have htime_k1 : G.sampledTime (k + 1) ≤ T := by
      exact (G.sampledTime_mono (Nat.succ_le_iff.mpr hkN)).trans_eq
        (sampledTime_size T r)
    by_cases hright : (G.sampledTime (k + 1) : WithTop NNReal) ≤ tau omega
    · have hleft : (G.sampledTime k : WithTop NNReal) ≤ tau omega :=
        (WithTop.coe_le_coe.mpr (G.sampledTime_mono (Nat.le_succ k))).trans hright
      rw [MeasureTheory.stoppedProcess_eq_of_le hright,
        MeasureTheory.stoppedProcess_eq_of_le hleft]
      have hnonneg : 0 ≤ (if k ∈ crossing then 2 * C else 0) := by
        split_ifs
        · positivity
        · rfl
      linarith
    · by_cases hleft : tau omega ≤ (G.sampledTime k : WithTop NNReal)
      · have hright' : tau omega ≤
            (G.sampledTime (k + 1) : WithTop NNReal) :=
          hleft.trans (WithTop.coe_le_coe.mpr
            (G.sampledTime_mono (Nat.le_succ k)))
        rw [MeasureTheory.stoppedProcess_eq_of_ge hright',
          MeasureTheory.stoppedProcess_eq_of_ge hleft]
        have hnonneg : 0 ≤
            |B (G.sampledTime (k + 1)) omega - B (G.sampledTime k) omega| :=
          abs_nonneg _
        have hzero : |B (tau omega).untopA omega -
            B (tau omega).untopA omega| = 0 := by simp
        have hnonneg' : 0 ≤ (if k ∈ crossing then 2 * C else 0) := by
          split_ifs
          · positivity
          · rfl
        simp only [hzero]
        linarith
      · have hcross : k ∈ crossing := by
          apply Finset.mem_filter.mpr
          refine ⟨hk, ?_⟩
          constructor
          · exact lt_of_not_ge hleft
          · exact lt_of_not_ge hright
        have hleft' : G.sampledTime k ≤ tau omega :=
          (lt_of_not_ge hleft).le
        have hright' : tau omega ≤
            (G.sampledTime (k + 1) : WithTop NNReal) :=
          (lt_of_not_ge hright).le
        rw [MeasureTheory.stoppedProcess_eq_of_ge hright',
          MeasureTheory.stoppedProcess_eq_of_le hleft']
        have hTauLe : (tau omega).untopA ≤ T :=
          WithTop.untopA_le hTauT
        have hBoundTau := hSup (tau omega).untopA hTauLe
        have hBoundLeft := hSup (G.sampledTime k) htime_k
        have hCrossBound :
            |B (tau omega).untopA omega - B (G.sampledTime k) omega| ≤
              2 * C := by
          calc
            |B (tau omega).untopA omega - B (G.sampledTime k) omega| ≤
                |B (tau omega).untopA omega| + |B (G.sampledTime k) omega| :=
              abs_sub _ _
            _ ≤ C + C := add_le_add hBoundTau hBoundLeft
            _ = 2 * C := by ring
        rw [ite_eq_left hcross]
        exact hCrossBound.trans (le_add_of_nonneg_left (abs_nonneg _))
  have hsum_term :
      (∑ k ∈ Finset.range N,
        |MeasureTheory.stoppedProcess B tau (G.sampledTime (k + 1)) omega -
            MeasureTheory.stoppedProcess B tau (G.sampledTime k) omega|) ≤
      (∑ k ∈ Finset.range N,
        |B (G.sampledTime (k + 1)) omega - B (G.sampledTime k) omega|) +
        ∑ k ∈ Finset.range N, (if k ∈ crossing then 2 * C else 0) := by
    calc
      (∑ k ∈ Finset.range N,
          |MeasureTheory.stoppedProcess B tau (G.sampledTime (k + 1)) omega -
            MeasureTheory.stoppedProcess B tau (G.sampledTime k) omega|) ≤
          ∑ k ∈ Finset.range N,
            (|B (G.sampledTime (k + 1)) omega - B (G.sampledTime k) omega| +
              (if k ∈ crossing then 2 * C else 0)) := by
        apply Finset.sum_le_sum
        intro k hk
        exact hterm k hk
      _ = (∑ k ∈ Finset.range N,
          |B (G.sampledTime (k + 1)) omega - B (G.sampledTime k) omega|) +
          ∑ k ∈ Finset.range N, (if k ∈ crossing then 2 * C else 0) := by
        rw [Finset.sum_add_distrib]
  have hsum_cross :
      (∑ k ∈ Finset.range N, (if k ∈ crossing then 2 * C else 0)) ≤
        2 * C := by
    have hsum_eq :
        (∑ k ∈ Finset.range N, (if k ∈ crossing then 2 * C else 0)) =
          ∑ k ∈ crossing, 2 * C := by
      have hsubset :
          (∑ k ∈ crossing, (if k ∈ crossing then 2 * C else 0)) =
            ∑ k ∈ Finset.range N, (if k ∈ crossing then 2 * C else 0) := by
        apply Finset.sum_subset hcross_subset
        intro k hk hnot
        simp [hnot]
      have hleft :
          (∑ k ∈ crossing, (if k ∈ crossing then 2 * C else 0)) =
            ∑ k ∈ crossing, 2 * C := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [hk]
      exact hsubset.symm.trans hleft
    rw [hsum_eq, Finset.sum_const]
    have hcard : (crossing.card : Real) ≤ 1 := by
      exact_mod_cast hcross_card
    simpa [nsmul_eq_mul] using
      (mul_le_mul_of_nonneg_right hcard
        (mul_nonneg (by norm_num) hC))
  calc
    (∑ k ∈ Finset.range (size T r),
        |MeasureTheory.stoppedProcess B tau
              ((grid T r).sampledTime (k + 1)) omega -
          MeasureTheory.stoppedProcess B tau
              ((grid T r).sampledTime k) omega|) ≤
        (∑ k ∈ Finset.range N,
          |B (G.sampledTime (k + 1)) omega - B (G.sampledTime k) omega|) +
          ∑ k ∈ Finset.range N, (if k ∈ crossing then 2 * C else 0) := by
      simpa [N, G] using hsum_term
    _ ≤ V + 2 * C := by
      exact add_le_add hVar hsum_cross

/-! ## Stopped row definitions and elementary process laws -/

noncomputable def commonStoppedRowMartingale
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (selection : Nat → Nat)
    (a : Real) (ha : 0 ≤ a) (T : NNReal)
    (alphaSeq : Nat → Omega → WithTop NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlphaSeqStop : ∀ k, IsStoppingTime F (alphaSeq k))
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    (k : Nat) : Process Omega :=
  MeasureTheory.stoppedProcess
    (rowInverseMartingaleGain u (selection k) hUsual source ha T
      (alphaSeq k) (hAlphaSeqStop k)) alpha

noncomputable def commonStoppedRowResidual
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (selection : Nat → Nat)
    (a : Real) (ha : 0 ≤ a) (T : NNReal)
    (alphaSeq : Nat → Omega → WithTop NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlphaSeqStop : ∀ k, IsStoppingTime F (alphaSeq k))
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    (k : Nat) : Process Omega :=
  MeasureTheory.stoppedProcess
    (rowInverseResidualGain u (selection k) hUsual source ha T
      (alphaSeq k) (hAlphaSeqStop k)) alpha

theorem rowInverseMartingaleGain_rightContinuous
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlphaStop : IsStoppingTime F alpha) :
    ∀ omega t, ContinuousWithinAt
      (rowInverseMartingaleGain u n hUsual source ha T alpha hAlphaStop · omega)
      (Ici t) t := by
  intro omega t
  unfold rowInverseMartingaleGain
  exact ((grid T (rowCommonLevel u n)).martingaleIntegralProcess_rightContinuous
    _ _ (nativeMartingaleConvexRow_rightContinuous u n hUsual source ha T)) omega t

theorem rowInverseMartingaleGain_eq_at_horizon_of_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlphaStop : IsStoppingTime F alpha)
    {t : NNReal} (hTt : T ≤ t) :
    rowInverseMartingaleGain u n hUsual source ha T alpha hAlphaStop t =
      rowInverseMartingaleGain u n hUsual source ha T alpha hAlphaStop T := by
  let q := rowCommonLevel u n
  let G := grid T q
  let K := rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
    u n a T alpha
  let M := nativeMartingaleConvexRow u n hUsual source ha T
  change G.martingaleIntegralProcess K M t =
    G.martingaleIntegralProcess K M T
  rw [G.martingaleIntegralProcess_eq_last_of_le K M]
  · simp [G, sampledTime_size]
  · simpa [G] using hTt

/-! ## Optional-sampling `L²` control at a bounded common stop -/

theorem martingale_stoppedProcess_memLp_two_and_integral_sq_le
    {M : Process Omega} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {tau : Omega → WithTop NNReal} {T : NNReal}
    (hM : Martingale M F mu)
    (hMRight : ∀ omega t, ContinuousWithinAt (M · omega) (Ici t) t)
    (hTau : IsStoppingTime F tau)
    (hMT : MemLp (M T) (2 : ENNReal) mu)
    (hMConstant : ∀ omega, M (T + 1) omega = M T omega) :
    MemLp (MeasureTheory.stoppedProcess M tau T) (2 : ENNReal) mu ∧
      (∫ omega, (MeasureTheory.stoppedProcess M tau T omega) ^ 2 ∂mu) ≤
        ∫ omega, (M T omega) ^ 2 ∂mu := by
  let sigma : Omega → NNReal := fun omega =>
    RightContinuousStoppedMartingale.boundedTime T tau omega
  have hSigma : IsStoppingTime F (fun omega =>
      (sigma omega : WithTop NNReal)) := by
    simpa [sigma] using
      (RightContinuousStoppedMartingale.boundedTime_isStoppingTime hTau T)
  have hSigmaT : ∀ omega, sigma omega ≤ T := by
    intro omega
    exact RightContinuousStoppedMartingale.boundedTime_le T tau omega
  have hMT1 : MemLp (M (T + 1)) (2 : ENNReal) mu := by
    apply (memLp_congr_ae (Filter.Eventually.of_forall hMConstant)).mpr
    exact hMT
  have hOptional :=
    Martingale.sample_ae_eq_condExp_terminal_of_boundedStoppingTime
      hM hSigma hSigmaT hMRight
  have hStopEq : MeasureTheory.stoppedProcess M tau T =ᵐ[mu]
      (fun omega => M (sigma omega) omega) := by
    filter_upwards [] with omega
    exact (RightContinuousStoppedMartingale.sample_boundedTime_eq_stoppedProcess
      M tau T omega).symm
  have hStopCond : MeasureTheory.stoppedProcess M tau T =ᵐ[mu]
      mu[M (T + 1) | hSigma.measurableSpace] := hStopEq.trans hOptional
  have hCond : MemLp (mu[M (T + 1) | hSigma.measurableSpace])
      (2 : ENNReal) mu := hMT1.condExp (by norm_num)
  have hStopMem : MemLp (MeasureTheory.stoppedProcess M tau T)
      (2 : ENNReal) mu := (memLp_congr_ae hStopCond).mpr hCond
  have hNorm : eLpNorm (MeasureTheory.stoppedProcess M tau T)
      (2 : ENNReal) mu ≤ eLpNorm (M T) (2 : ENNReal) mu := by
    calc
      eLpNorm (MeasureTheory.stoppedProcess M tau T) (2 : ENNReal) mu =
          eLpNorm (mu[M (T + 1) | hSigma.measurableSpace])
            (2 : ENNReal) mu := eLpNorm_congr_ae hStopCond
      _ ≤ eLpNorm (M (T + 1)) (2 : ENNReal) mu :=
        eLpNorm_condExp_le_eLpNorm _ (by norm_num)
      _ = eLpNorm (M T) (2 : ENNReal) mu :=
        eLpNorm_congr_ae (Filter.Eventually.of_forall hMConstant)
  have hSqNorm := integral_norm_sq_le_of_eLpNorm_two_le
    hStopMem hMT hNorm
  refine ⟨hStopMem, ?_⟩
  simpa only [Real.norm_eq_abs, sq_abs] using hSqNorm

/-! ## Process identities used by the common-stop consumer -/

omit [MeasurableSpace Omega] in
theorem stoppedProcess_add
    (P Q : Process Omega) (tau : Omega → WithTop NNReal) :
    MeasureTheory.stoppedProcess (P + Q) tau =
      MeasureTheory.stoppedProcess P tau +
        MeasureTheory.stoppedProcess Q tau := by
  funext t omega
  simp [MeasureTheory.stoppedProcess, Pi.add_apply]

omit [MeasurableSpace Omega] in
theorem stoppedProcess_sub_const
    (P : Process Omega) (c : Omega → Real)
    (tau : Omega → WithTop NNReal) :
    MeasureTheory.stoppedProcess (fun t omega => P t omega - c omega) tau =
      (fun t omega => MeasureTheory.stoppedProcess P tau t omega - c omega) := by
  funext t omega
  simp [MeasureTheory.stoppedProcess]

/-! The native martingale terminal rows inherit a level-independent bound from
the stopped Doob martingale estimate. -/

theorem nativeMartingaleConvexRow_terminal_difference_integral_sq_le
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (n : Nat)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) :
    (∫ omega,
      (nativeMartingaleConvexRow u n hUsual source ha T T omega -
        nativeMartingaleConvexRow u n hUsual source ha T 0 omega) ^ 2 ∂mu) ≤
      4 * (a + 4 * max source.bound 0) ^ 2 := by
  let C : Real := a + 4 * max source.bound 0
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hComponentT : ∀ r, ∀ᵐ omega ∂mu,
      |nativeMartingaleProcess hUsual source ha T r T omega| ≤ C := by
    intro r
    have hEq := nativeMartingaleProcess_at_native_grid_doobPart_ae
      (S := S) (F := F) (mu := mu) hUsual source ha T r (size T r)
        (le_rfl)
    have hBound := (grid T r).ae_abs_doobVariationStoppedMartingalePart_le
      source ha
    filter_upwards [hEq, hBound] with omega hEqOmega hBoundOmega
    rw [sampledTime_size] at hEqOmega
    rw [hEqOmega]
    exact hBoundOmega _
  have hComponent0 : ∀ r, ∀ᵐ omega ∂mu,
      |nativeMartingaleProcess hUsual source ha T r 0 omega| ≤ C := by
    intro r
    have hEq := nativeMartingaleProcess_at_native_grid_doobPart_ae
      (S := S) (F := F) (mu := mu) hUsual source ha T r 0
        (Nat.zero_le _)
    have hBound := (grid T r).ae_abs_doobVariationStoppedMartingalePart_le
      source ha
    have hZero : (grid T r).sampledTime 0 = 0 := by
      simp [grid, ChronologicalGrid.sampledTime, ChronologicalGrid.natIndex]
    filter_upwards [hEq, hBound] with omega hEqOmega hBoundOmega
    rw [hZero] at hEqOmega
    rw [hEqOmega]
    exact hBoundOmega _
  have hRowT : ∀ᵐ omega ∂mu,
      |nativeMartingaleConvexRow u n hUsual source ha T T omega| ≤ C := by
    have hAll := (u n).support.eventually_all.mpr
      (fun r _hr => hComponentT r)
    filter_upwards [hAll] with omega hOmega
    unfold nativeMartingaleConvexRow TailConvexWeights.apply
    calc
      |∑ r ∈ (u n).support,
          (u n).weight r * nativeMartingaleProcess hUsual source ha T r T omega| ≤
          ∑ r ∈ (u n).support,
            |(u n).weight r * nativeMartingaleProcess hUsual source ha T r T omega| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r ∈ (u n).support, (u n).weight r * C := by
        apply Finset.sum_le_sum
        intro r hr
        rw [abs_mul, abs_of_nonneg ((u n).nonneg r hr)]
        exact mul_le_mul_of_nonneg_left (hOmega r hr)
          ((u n).nonneg r hr)
      _ = C := by
        rw [← Finset.sum_mul, (u n).sum_eq_one, one_mul]
  have hRow0 : ∀ᵐ omega ∂mu,
      |nativeMartingaleConvexRow u n hUsual source ha T 0 omega| ≤ C := by
    have hAll := (u n).support.eventually_all.mpr
      (fun r _hr => hComponent0 r)
    filter_upwards [hAll] with omega hOmega
    unfold nativeMartingaleConvexRow TailConvexWeights.apply
    calc
      |∑ r ∈ (u n).support,
          (u n).weight r * nativeMartingaleProcess hUsual source ha T r 0 omega| ≤
          ∑ r ∈ (u n).support,
            |(u n).weight r * nativeMartingaleProcess hUsual source ha T r 0 omega| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r ∈ (u n).support, (u n).weight r * C := by
        apply Finset.sum_le_sum
        intro r hr
        rw [abs_mul, abs_of_nonneg ((u n).nonneg r hr)]
        exact mul_le_mul_of_nonneg_left (hOmega r hr)
          ((u n).nonneg r hr)
      _ = C := by
        rw [← Finset.sum_mul, (u n).sum_eq_one, one_mul]
  have hDiffInt : Integrable (fun omega =>
      (nativeMartingaleConvexRow u n hUsual source ha T T omega -
        nativeMartingaleConvexRow u n hUsual source ha T 0 omega) ^ 2) mu :=
    ((nativeMartingaleConvexRow_memLp_two u n hUsual source ha T T).sub
      (nativeMartingaleConvexRow_memLp_two u n hUsual source ha T 0)).integrable_sq
  have hConstInt : Integrable (fun _omega : Omega => (2 * C) ^ 2) mu :=
    integrable_const _
  have hDiffBound : (∫ omega,
      (nativeMartingaleConvexRow u n hUsual source ha T T omega -
        nativeMartingaleConvexRow u n hUsual source ha T 0 omega) ^ 2 ∂mu) ≤
      (2 * C) ^ 2 := by
    calc
      (∫ omega,
          (nativeMartingaleConvexRow u n hUsual source ha T T omega -
            nativeMartingaleConvexRow u n hUsual source ha T 0 omega) ^ 2 ∂mu) ≤
          ∫ _omega : Omega, (2 * C) ^ 2 ∂mu := by
        apply integral_mono_ae hDiffInt hConstInt
        filter_upwards [hRowT, hRow0] with omega hT h0
        have habs :
            |nativeMartingaleConvexRow u n hUsual source ha T T omega -
              nativeMartingaleConvexRow u n hUsual source ha T 0 omega| ≤ 2 * C := by
          calc
            |nativeMartingaleConvexRow u n hUsual source ha T T omega -
                nativeMartingaleConvexRow u n hUsual source ha T 0 omega| ≤
                |nativeMartingaleConvexRow u n hUsual source ha T T omega| +
                  |nativeMartingaleConvexRow u n hUsual source ha T 0 omega| :=
              abs_sub _ _
            _ ≤ C + C := add_le_add hT h0
            _ = 2 * C := by ring
        rw [← sq_abs]
        exact (sq_le_sq₀ (abs_nonneg _)
          (mul_nonneg (by norm_num) hC)).2 habs
      _ = (2 * C) ^ 2 := by simp
  calc
    (∫ omega,
        (nativeMartingaleConvexRow u n hUsual source ha T T omega -
          nativeMartingaleConvexRow u n hUsual source ha T 0 omega) ^ 2 ∂mu) ≤
        (2 * C) ^ 2 := hDiffBound
    _ = 4 * (a + 4 * max source.bound 0) ^ 2 := by
      dsimp [C]
      ring

/-! ## The concrete common-stop package -/

structure CommonStoppedRowsData
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (selection : Nat → Nat)
    {a : Real} (ha : 0 < a) (T : NNReal)
    (alphaSeq : Nat → Omega → WithTop NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlphaSeqStop : ∀ k, IsStoppingTime F (alphaSeq k))
    (hAlphaStop : IsStoppingTime F alpha)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu) : Prop where
  rowData : ∀ k,
    RowInverseDecompositionData u (selection k) hUsual source ha T
      (alphaSeq k) (hAlphaSeqStop k)
  martingale : ∀ k,
    Martingale
      (commonStoppedRowMartingale u selection a ha.le T alphaSeq alpha
        hAlphaSeqStop hUsual source k) F mu
  residual_baseGridVariation : ∀ k, ∀ᵐ omega ∂mu,
    (∑ j ∈ Finset.range (size T (selection k)),
      |commonStoppedRowResidual u selection a ha.le T alphaSeq alpha
          hAlphaSeqStop hUsual source k
          ((grid T (selection k)).sampledTime (j + 1)) omega -
        commonStoppedRowResidual u selection a ha.le T alphaSeq alpha
          hAlphaSeqStop hUsual source k
          ((grid T (selection k)).sampledTime j) omega|) ≤
      (6 * (a + 4 * max source.bound 0) +
        2 * (a + 2 * max source.bound 0)) +
        2 * (16 * (a + 4 * max source.bound 0) +
          2 * (a + 2 * max source.bound 0))
  residual_horizon_sup : ∀ k, ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
    |commonStoppedRowResidual u selection a ha.le T alphaSeq alpha
        hAlphaSeqStop hUsual source k t omega| ≤
      16 * (a + 4 * max source.bound 0) +
        2 * (a + 2 * max source.bound 0)
  stoppedSource_eq_martingale_add_residual : ∀ k t omega,
    MeasureTheory.stoppedProcess S alpha t omega - S 0 omega =
      commonStoppedRowMartingale u selection a ha.le T alphaSeq alpha
        hAlphaSeqStop hUsual source k t omega +
      commonStoppedRowResidual u selection a ha.le T alphaSeq alpha
        hAlphaSeqStop hUsual source k t omega
  martingale_terminal_memLp : ∀ k,
    MemLp
      (commonStoppedRowMartingale u selection a ha.le T alphaSeq alpha
        hAlphaSeqStop hUsual source k T) (2 : ENNReal) mu
  martingale_terminal_L2_bound : ∀ k,
    (∫ omega,
      (commonStoppedRowMartingale u selection a ha.le T alphaSeq alpha
        hAlphaSeqStop hUsual source k T omega) ^ 2 ∂mu) ≤
      4 * (∫ omega,
        (nativeMartingaleConvexRow u (selection k) hUsual source ha.le T T omega -
          nativeMartingaleConvexRow u (selection k) hUsual source ha.le T 0 omega) ^ 2 ∂mu)
  martingale_terminal_L2_uniform_bound : ∀ k,
    (∫ omega,
      (commonStoppedRowMartingale u selection a ha.le T alphaSeq alpha
        hAlphaSeqStop hUsual source k T omega) ^ 2 ∂mu) ≤
      16 * (a + 4 * max source.bound 0) ^ 2

/-! ## One selected row after the common stop -/

theorem commonStoppedRowData_of_rowData
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (selection : Nat → Nat)
    {a : Real} (ha : 0 < a) (T : NNReal)
    (alphaSeq : Nat → Omega → WithTop NNReal)
    (alpha : Omega → WithTop NNReal)
    (hAlphaSeqStop : ∀ k, IsStoppingTime F (alphaSeq k))
    (hAlphaStop : IsStoppingTime F alpha)
    (hAlphaSeqLe : ∀ k omega, alphaSeq k omega ≤ (T : WithTop NNReal))
    (hAlphaLe : ∀ k omega, alpha omega ≤ alphaSeq k omega)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    (hRowData : ∀ k,
      RowInverseDecompositionData u (selection k) (hUsual := hUsual)
        source ha T (alphaSeq k) (hAlphaSeqStop k)) :
    CommonStoppedRowsData u selection ha T alphaSeq alpha hAlphaSeqStop
      hAlphaStop hUsual source := by
  classical
  have hAlphaT : ∀ (k : Nat) (omega : Omega),
      alpha omega ≤ (T : WithTop NNReal) := by
    intro k omega
    exact (hAlphaLe k omega).trans (hAlphaSeqLe k omega)
  refine ⟨hRowData, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    let N : Process Omega :=
      rowInverseMartingaleGain u (selection k) hUsual source ha.le T
        (alphaSeq k) (hAlphaSeqStop k)
    have hN := (hRowData k).2.2.2.2.1
    have hNRight : ∀ omega t, ContinuousWithinAt (N · omega) (Ici t) t := by
      intro omega t
      exact rowInverseMartingaleGain_rightContinuous u (selection k) hUsual source
        ha.le T (alphaSeq k) (hAlphaSeqStop k) omega t
    have hCommon :=
      RightContinuousStoppedMartingale.Martingale.stoppedProcess_of_rightContinuous
        hN hAlphaStop hNRight
    simpa [N, commonStoppedRowMartingale] using hCommon
  · intro k
    let B : Process Omega :=
      rowInverseResidualGain u (selection k) hUsual source ha.le T
        (alphaSeq k) (hAlphaSeqStop k)
    have hVar := (hRowData k).2.1
    have hSup := (hRowData k).2.2.1
    have hVar' : ∀ᵐ omega ∂mu,
        (∑ j ∈ Finset.range (size T (selection k)),
          |MeasureTheory.stoppedProcess B alpha
              ((grid T (selection k)).sampledTime (j + 1)) omega -
            MeasureTheory.stoppedProcess B alpha
              ((grid T (selection k)).sampledTime j) omega|) ≤
          (6 * (a + 4 * max source.bound 0) +
            2 * (a + 2 * max source.bound 0)) +
            2 * (16 * (a + 4 * max source.bound 0) +
              2 * (a + 2 * max source.bound 0)) := by
      filter_upwards [hVar, hSup] with omega hVarOmega hSupOmega
      apply stoppedProcess_gridVariation_le_add_two_of_sup_at
        T (selection k) alpha omega (hAlphaT k omega) (by positivity)
        hVarOmega hSupOmega
    simpa [B, commonStoppedRowResidual] using hVar'
  · intro k
    let B : Process Omega :=
      rowInverseResidualGain u (selection k) hUsual source ha.le T
        (alphaSeq k) (hAlphaSeqStop k)
    have hSup := (hRowData k).2.2.1
    have hSup' : ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
        |MeasureTheory.stoppedProcess B alpha t omega| ≤
          16 * (a + 4 * max source.bound 0) +
            2 * (a + 2 * max source.bound 0) := by
      filter_upwards [hSup] with omega hSupOmega
      intro t ht
      change |B (min (t : WithTop NNReal) (alpha omega)).untopA omega| ≤ _
      apply hSupOmega
      exact WithTop.untopA_le
        ((min_le_left _ _).trans (WithTop.coe_le_coe.mpr ht))
    simpa [B, commonStoppedRowResidual] using hSup'
  · intro k t omega
    let N : Process Omega :=
      rowInverseMartingaleGain u (selection k) hUsual source ha.le T
        (alphaSeq k) (hAlphaSeqStop k)
    let B : Process Omega :=
      rowInverseResidualGain u (selection k) hUsual source ha.le T
        (alphaSeq k) (hAlphaSeqStop k)
    have hDec := (hRowData k).2.2.2.1
    have hRowEq :
        (fun s omega =>
          MeasureTheory.stoppedProcess S (alphaSeq k) s omega - S 0 omega) =
          N + B := by
      funext s omega
      exact hDec s omega
    have hStopped := congrArg
      (fun P : Process Omega => MeasureTheory.stoppedProcess P alpha) hRowEq
    have hSourceStop :
        MeasureTheory.stoppedProcess
            (MeasureTheory.stoppedProcess S (alphaSeq k)) alpha =
          MeasureTheory.stoppedProcess S alpha :=
      MeasureTheory.stoppedProcess_stoppedProcess_of_le_right (hAlphaLe k)
    rw [stoppedProcess_sub_const, stoppedProcess_add, hSourceStop] at hStopped
    have hPoint := congrFun (congrFun hStopped t) omega
    simpa [N, B, commonStoppedRowMartingale, commonStoppedRowResidual] using hPoint
  · intro k
    let N : Process Omega :=
      rowInverseMartingaleGain u (selection k) hUsual source ha.le T
        (alphaSeq k) (hAlphaSeqStop k)
    have hN := (hRowData k).2.2.2.2.1
    have hNRight : ∀ omega t, ContinuousWithinAt (N · omega) (Ici t) t := by
      intro omega t
      exact rowInverseMartingaleGain_rightContinuous u (selection k) hUsual source
        ha.le T (alphaSeq k) (hAlphaSeqStop k) omega t
    have hNT : MemLp (N T) (2 : ENNReal) mu := by
      simpa [N, sampledTime_size] using (hRowData k).2.2.2.2.2.1
    have hNConstant : ∀ omega, N (T + 1) omega = N T omega := by
      intro omega
      exact congrFun
        (rowInverseMartingaleGain_eq_at_horizon_of_le u (selection k) hUsual source
          ha.le T (alphaSeq k) (hAlphaSeqStop k) (by exact le_add_right le_rfl)) omega
    have hStopped := martingale_stoppedProcess_memLp_two_and_integral_sq_le
      hN hNRight hAlphaStop hNT hNConstant
    simpa [N, commonStoppedRowMartingale] using hStopped.1
  · intro k
    let N : Process Omega :=
      rowInverseMartingaleGain u (selection k) hUsual source ha.le T
        (alphaSeq k) (hAlphaSeqStop k)
    have hN := (hRowData k).2.2.2.2.1
    have hNRight : ∀ omega t, ContinuousWithinAt (N · omega) (Ici t) t := by
      intro omega t
      exact rowInverseMartingaleGain_rightContinuous u (selection k) hUsual source
        ha.le T (alphaSeq k) (hAlphaSeqStop k) omega t
    have hNT : MemLp (N T) (2 : ENNReal) mu := by
      simpa [N, sampledTime_size] using (hRowData k).2.2.2.2.2.1
    have hNConstant : ∀ omega, N (T + 1) omega = N T omega := by
      intro omega
      exact congrFun
        (rowInverseMartingaleGain_eq_at_horizon_of_le u (selection k) hUsual source
          ha.le T (alphaSeq k) (hAlphaSeqStop k) (by exact le_add_right le_rfl)) omega
    have hStopped := martingale_stoppedProcess_memLp_two_and_integral_sq_le
      hN hNRight hAlphaStop hNT hNConstant
    have hRowBound :
        (∫ omega, (N T omega) ^ 2 ∂mu) ≤
          4 * (∫ omega,
            (nativeMartingaleConvexRow u (selection k) hUsual source
                ha.le T T omega -
              nativeMartingaleConvexRow u (selection k) hUsual source
                ha.le T 0 omega) ^ 2 ∂mu) := by
      simpa [N, sampledTime_size] using (hRowData k).2.2.2.2.2.2
    exact hStopped.2.trans hRowBound
  · intro k
    let N : Process Omega :=
      rowInverseMartingaleGain u (selection k) hUsual source ha.le T
        (alphaSeq k) (hAlphaSeqStop k)
    have hN := (hRowData k).2.2.2.2.1
    have hNRight : ∀ omega t, ContinuousWithinAt (N · omega) (Ici t) t := by
      intro omega t
      exact rowInverseMartingaleGain_rightContinuous u (selection k) hUsual source
        ha.le T (alphaSeq k) (hAlphaSeqStop k) omega t
    have hNT : MemLp (N T) (2 : ENNReal) mu := by
      simpa [N, sampledTime_size] using (hRowData k).2.2.2.2.2.1
    have hNConstant : ∀ omega, N (T + 1) omega = N T omega := by
      intro omega
      exact congrFun
        (rowInverseMartingaleGain_eq_at_horizon_of_le u (selection k) hUsual source
          ha.le T (alphaSeq k) (hAlphaSeqStop k) (by exact le_add_right le_rfl)) omega
    have hStopped := martingale_stoppedProcess_memLp_two_and_integral_sq_le
      hN hNRight hAlphaStop hNT hNConstant
    have hRowBound :=
      nativeMartingaleConvexRow_terminal_difference_integral_sq_le
        u (selection k) hUsual source ha.le T
    have hRawBound :
        (∫ omega, (N T omega) ^ 2 ∂mu) ≤
          4 * (4 * (a + 4 * max source.bound 0) ^ 2) := by
      calc
        (∫ omega, (N T omega) ^ 2 ∂mu) ≤
            4 * (∫ omega,
              (nativeMartingaleConvexRow u (selection k) hUsual source
                  ha.le T T omega -
                nativeMartingaleConvexRow u (selection k) hUsual source
                  ha.le T 0 omega) ^ 2 ∂mu) := by
          simpa [N, sampledTime_size] using (hRowData k).2.2.2.2.2.2
        _ ≤ 4 * (4 * (a + 4 * max source.bound 0) ^ 2) := by
          exact mul_le_mul_of_nonneg_left hRowBound (by norm_num)
    calc
      (∫ omega,
          (commonStoppedRowMartingale u selection a ha.le T alphaSeq alpha
            hAlphaSeqStop hUsual source k T omega) ^ 2 ∂mu) ≤
          ∫ omega, (N T omega) ^ 2 ∂mu := by
        simpa [N, commonStoppedRowMartingale] using hStopped.2
      _ ≤ 4 * (4 * (a + 4 * max source.bound 0) ^ 2) := hRawBound
      _ = 16 * (a + 4 * max source.bound 0) ^ 2 := by ring

/-! ## Direct consumer of the common-gate endpoint -/

structure CommonStoppedRowsEndpoint
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (u : ∀ n, TailConvexWeights n) (selection : Nat → Nat)
    (a : Real) (T : NNReal)
    {eta : Real}
    (alphaSeq : Nat → Omega → WithTop NNReal)
    (alpha : Omega → WithTop NNReal)
    (R : Omega → Real)
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu) : Prop where
  eta_pos : 0 < eta
  a_pos : 0 < a
  selection_strictMono : StrictMono selection
  selection_error : ∀ k, mu {omega |
      (1 / 6 : Real) ≤ dist (((u (selection k)).apply (fun r =>
        variationGateTerminal a T r S F mu)) omega)
        (R omega)} ≤ ENNReal.ofReal (eta * ((1 / 2 : Real) ^ (k + 1)))
  alphaSeq_eq : ∀ k omega, alphaSeq k omega = min (T : WithTop NNReal)
    (LeftContinuousHittingTime.strictHittingAfter
      (fun t omega => -variationGateConvexRow u (selection k) a T S F mu t omega)
      (-1 / 2) omega)
  alphaSeq_le_T : ∀ k omega, alphaSeq k omega ≤ (T : WithTop NNReal)
  alphaSeq_stopping : ∀ k, IsStoppingTime F (alphaSeq k)
  alpha_stopping : IsStoppingTime F alpha
  alpha_eq_iInf : ∀ omega, alpha omega = ⨅ k, alphaSeq k omega
  alpha_le_alphaSeq : ∀ k omega, alpha omega ≤ alphaSeq k omega
  alpha_measure : mu {omega | alpha omega < (T : WithTop NNReal)} ≤
    ENNReal.ofReal (4 * eta)
  data : CommonStoppedRowsData u selection a_pos T alphaSeq alpha
    alphaSeq_stopping alpha_stopping hUsual source

theorem exists_commonGateStoppedRows
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (hUsual : Filtration.UsualConditions mu F)
    (hS : IsSemimartingale S F mu)
    (source : BoundedSemimartingaleSource S F mu)
    (T : NNReal) {eta : Real} (heta : 0 < eta) :
    ∃ (a : Real) (u : ∀ n, TailConvexWeights n)
      (selection : Nat → Nat)
      (alphaSeq : Nat → Omega → WithTop NNReal)
      (alpha : Omega → WithTop NNReal) (R : Omega → Real),
      CommonStoppedRowsEndpoint (eta := eta) u selection a T alphaSeq alpha R
        hUsual source := by
  classical
  obtain ⟨a, _w, _v, u, _predictableLimit, _martingaleLimit, _M, _Xbar,
      _Mbar, _A, _terminal, _Mcad, _Xcorr, selection, R, _gLimit,
      alphaSeq, alpha, hGate⟩ :=
    exists_commonGateRows hUsual hS source T heta
  rcases hGate with ⟨_haNonneg, haPos, _hGateTail, _hu, _hRows,
    hSelection, hSelectionError, hAlphaSeqEq, _hTerminalBound, _hGLimit,
    _hAE, _hRBounds, _hExpectation, hAlphaSeqStop, hAlphaStop,
    hAlphaInf, hAlphaLe, hAlphaMeasure⟩
  have hAlphaSeqLe : ∀ k omega,
      alphaSeq k omega ≤ (T : WithTop NNReal) := by
    intro k omega
    rw [hAlphaSeqEq k omega]
    exact min_le_left _ _
  have hAlphaLeInf : ∀ k omega, alpha omega ≤ alphaSeq k omega := by
    intro k omega
    rw [hAlphaInf omega]
    exact iInf_le (fun j => alphaSeq j omega) k
  have hRowData : ∀ k,
      RowInverseDecompositionData u (selection k) hUsual source haPos T
        (alphaSeq k) (hAlphaSeqStop k) := by
    intro k
    have hAlphaHit : ∀ omega, alphaSeq k omega ≤ min (T : WithTop NNReal)
        (LeftContinuousHittingTime.strictHittingAfter
          (fun t omega =>
            -variationGateConvexRow u (selection k) a T S F mu t omega)
          (-1 / 2) omega) := by
      intro omega
      exact le_of_eq (hAlphaSeqEq k omega)
    have hNoCross : ∀ j, j < size T (rowCommonLevel u (selection k)) →
        ∀ omega,
          ((grid T (rowCommonLevel u (selection k))).sampledTime j :
            WithTop NNReal) < alphaSeq k omega →
          (grid T (rowCommonLevel u (selection k))).sampledTime j <
            (grid T (rowCommonLevel u (selection k))).sampledTime (j + 1) →
          ((grid T (rowCommonLevel u (selection k))).sampledTime (j + 1) :
            WithTop NNReal) ≤ alphaSeq k omega := by
      intro j hj omega hleft hcell
      exact rowAlpha_noCross_of_exact_hitting u (selection k) a T S F mu
        (alphaSeq k) (hAlphaSeqEq k) j omega hj hleft
    exact rowInverseDecompositionData_of_hitting u (selection k) hUsual source
      haPos T (alphaSeq k) (hAlphaSeqStop k) hAlphaHit hNoCross
  have hData : CommonStoppedRowsData u selection haPos T alphaSeq alpha
      hAlphaSeqStop hAlphaStop hUsual source :=
    commonStoppedRowData_of_rowData u selection haPos T alphaSeq alpha
      hAlphaSeqStop hAlphaStop hAlphaSeqLe hAlphaLeInf hUsual source hRowData
  refine ⟨a, u, selection, alphaSeq, alpha, R, ?_⟩
  exact
    { eta_pos := heta
      a_pos := haPos
      selection_strictMono := hSelection
      selection_error := hSelectionError
      alphaSeq_eq := hAlphaSeqEq
      alphaSeq_le_T := hAlphaSeqLe
      alphaSeq_stopping := hAlphaSeqStop
      alpha_stopping := hAlphaStop
      alpha_eq_iInf := hAlphaInf
      alpha_le_alphaSeq := hAlphaLe
      alpha_measure := hAlphaMeasure
      data := hData }

end HorizonFactorialGrid

end FTAPTheorem42
