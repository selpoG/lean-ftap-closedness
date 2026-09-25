/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStopConvexification
import FTAPTheorem42.Stochastic.Martingale.Regularization.ConditionalExpectationCadlagRegularization
import FTAPTheorem42.Stochastic.Martingale.Basic.MartingaleAbsoluteEnvelope
import FTAPTheorem42.Stochastic.Martingale.Quadratic.MartingaleQuadraticJump
import FTAPTheorem42.Stochastic.Process.ProcessLeftJump

/-!
# Càdlàg limit of the common-stop martingale rows

The common terminal convexification is consumed without changing its weights.
The terminal `L²` limit is regularized as a càdlàg conditional-expectation
martingale.  Doob's absolute-value envelope then gives convergence in measure
uniformly on the finite horizon, and a strict subsequence gives one common
null set with pathwise uniform convergence on `[0,T]`.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

open _root_.FTAPTheorem42.FactorialChronologicalGrid

/-! The data structure keeps the source rows and their exact decomposition.
The last two fields are the process-level convergence output used by the next
finite-variation boundary. -/

structure CommonStoppedRowsCadlagMartingaleLimitData
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {eta : Real}
    {u : ∀ n, TailConvexWeights n} {selection : Nat → Nat}
    {a : Real} {T : NNReal}
    {alphaSeq : Nat → Omega → WithTop NNReal}
    {alpha : Omega → WithTop NNReal} {R : Omega → Real}
    {hUsual : Filtration.UsualConditions mu F}
    {source : BoundedSemimartingaleSource S F mu}
    (endpoint : CommonStoppedRowsEndpoint
      (S := S) (F := F) (mu := mu) (eta := eta) u selection a T alphaSeq alpha R
      hUsual source)
    (v : ∀ n, TailConvexWeights n) (Z : Lp Real 2 mu)
    (Nbar Bbar Xbar : Nat → Process Omega)
    (M : Process Omega) (cutoff : Nat → Nat) : Prop where
  convexification : CommonStoppedRowsTerminalTailConvexificationData
    endpoint v Z Nbar Bbar Xbar
  cutoff_strictMono : StrictMono cutoff
  M_martingale : Martingale M F mu
  M_rightContinuous : ∀ omega t,
    ContinuousWithinAt (M · omega) (Ici t) t
  M_leftLimits : ProcessHasLeftLimits M
  M_condExp : ∀ t, M t =ᵐ[mu]
    condExpMartingaleProcess mu F Z t
  M_zero : M 0 =ᵐ[mu] 0
  M_constant_after : ∀ t, T ≤ t → M t =ᵐ[mu] M T
  Nbar_martingale : ∀ n, Martingale (Nbar n) F mu
  Nbar_rightContinuous : ∀ n omega t,
    ContinuousWithinAt (Nbar n · omega) (Ici t) t
  Nbar_leftLimits : ∀ n, ProcessHasLeftLimits (Nbar n)
  Nbar_constant_after : ∀ n t, T ≤ t → Nbar n t = Nbar n T
  terminal_difference_norm_tendsto : Tendsto
    (fun n => eLpNorm (Nbar n T - M T) (2 : ENNReal) mu)
    atTop (𝓝 0)
  envelope_memLp : ∀ n, MemLp (martingaleDifferenceEnvelope Nbar M T n)
    (2 : ENNReal) mu
  envelope_norm_bound : ∀ n,
    eLpNorm (martingaleDifferenceEnvelope Nbar M T n) (2 : ENNReal) mu ≤
      2 * eLpNorm (Nbar n T - M T) (2 : ENNReal) mu
  envelope_norm_tendsto : Tendsto
    (fun n => eLpNorm (martingaleDifferenceEnvelope Nbar M T n) (2 : ENNReal) mu)
    atTop (𝓝 0)
  envelope_tendstoInMeasure : TendstoInMeasure mu
    (fun n omega => martingaleDifferenceEnvelope Nbar M T n omega)
    atTop (fun _ => 0)
  envelope_dominates : ∀ n, ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
    ‖Nbar n t omega - M t omega‖ ≤ martingaleDifferenceEnvelope Nbar M T n omega
  cutoff_envelope_tendsto_ae : ∀ᵐ omega ∂mu,
    Tendsto (fun k => martingaleDifferenceEnvelope Nbar M T (cutoff k) omega)
      atTop (𝓝 0)
  rows_tendstoUniformlyOn_ae : ∀ᵐ omega ∂mu,
    TendstoUniformlyOn (fun k t => Nbar (cutoff k) t omega)
      (fun t => M t omega) atTop (Iic T)

/-! ## Basic row identities -/

private theorem commonStoppedRowMartingale_zero
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {eta : Real}
    {u : ∀ n, TailConvexWeights n} {selection : Nat → Nat}
    {a : Real} {T : NNReal}
    {alphaSeq : Nat → Omega → WithTop NNReal}
    {alpha : Omega → WithTop NNReal} {R : Omega → Real}
    {hUsual : Filtration.UsualConditions mu F}
    {source : BoundedSemimartingaleSource S F mu}
    (endpoint : CommonStoppedRowsEndpoint
      (S := S) (F := F) (mu := mu) (eta := eta) u selection a T alphaSeq alpha R
      hUsual source)
    (k : Nat) :
    commonStoppedRowMartingale u selection a endpoint.a_pos.le T
      alphaSeq alpha endpoint.alphaSeq_stopping hUsual source k 0 = 0 := by
  classical
  funext omega
  unfold commonStoppedRowMartingale
  rw [MeasureTheory.stoppedProcess_eq_of_le (by exact bot_le)]
  unfold rowInverseMartingaleGain
  unfold ChronologicalGrid.martingaleIntegralProcess
  simp only [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  have hzero := deterministicIntervalMartingaleTransform_eq_zero_of_le
    (rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
      u (selection k) a T (alphaSeq k))
    (nativeMartingaleConvexRow (u := u) (n := selection k) hUsual source
      endpoint.a_pos.le T)
    (s := (grid T (rowCommonLevel u (selection k))).sampledTime j)
    (t := (grid T (rowCommonLevel u (selection k))).sampledTime (j + 1))
    (u := 0)
    ((grid T (rowCommonLevel u (selection k))).sampledTime_mono
      (Nat.le_succ j)) (by exact bot_le)
  exact congrFun hzero omega

private theorem commonStoppedRowsMartingaleConvexRow_martingale
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {eta : Real}
    {u : ∀ n, TailConvexWeights n} {selection : Nat → Nat}
    {a : Real} {T : NNReal}
    {alphaSeq : Nat → Omega → WithTop NNReal}
    {alpha : Omega → WithTop NNReal} {R : Omega → Real}
    {hUsual : Filtration.UsualConditions mu F}
    {source : BoundedSemimartingaleSource S F mu}
    (endpoint : CommonStoppedRowsEndpoint
      (S := S) (F := F) (mu := mu) (eta := eta) u selection a T alphaSeq alpha R
      hUsual source)
    (v : ∀ n, TailConvexWeights n) (n : Nat) :
    Martingale (commonStoppedRowsMartingaleConvexRow endpoint v n) F mu := by
  classical
  have hSum : Martingale
      (∑ k ∈ (v n).support,
        (v n).weight k •
          commonStoppedRowMartingale u selection a endpoint.a_pos.le T
            alphaSeq alpha endpoint.alphaSeq_stopping hUsual source k) F mu := by
    induction (v n).support using Finset.induction_on with
    | empty =>
        simpa using (martingale_zero Real F mu)
    | @insert k s hks ih =>
        rw [Finset.sum_insert hks]
        exact (endpoint.data.martingale k).smul ((v n).weight k) |>.add ih
  have hEq : commonStoppedRowsMartingaleConvexRow endpoint v n =
      ∑ k ∈ (v n).support,
        (v n).weight k •
          commonStoppedRowMartingale u selection a endpoint.a_pos.le T
            alphaSeq alpha endpoint.alphaSeq_stopping hUsual source k := by
    funext t omega
    simp [commonStoppedRowsMartingaleConvexRow, TailConvexWeights.apply,
      Finset.sum_apply, Pi.smul_apply]
  rw [hEq]
  exact hSum

private theorem commonStoppedRowsMartingaleConvexRow_rightContinuous
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {eta : Real}
    {u : ∀ n, TailConvexWeights n} {selection : Nat → Nat}
    {a : Real} {T : NNReal}
    {alphaSeq : Nat → Omega → WithTop NNReal}
    {alpha : Omega → WithTop NNReal} {R : Omega → Real}
    {hUsual : Filtration.UsualConditions mu F}
    {source : BoundedSemimartingaleSource S F mu}
    (endpoint : CommonStoppedRowsEndpoint
      (S := S) (F := F) (mu := mu) (eta := eta) u selection a T alphaSeq alpha R
      hUsual source)
    (v : ∀ n, TailConvexWeights n) (n : Nat) :
    ∀ omega t, ContinuousWithinAt
      (commonStoppedRowsMartingaleConvexRow endpoint v n · omega) (Ici t) t := by
  classical
  intro omega t
  unfold commonStoppedRowsMartingaleConvexRow TailConvexWeights.apply
  induction (v n).support using Finset.induction_on with
  | empty =>
      simpa using (continuousWithinAt_const :
        ContinuousWithinAt (fun _ : NNReal => (0 : Real)) (Ici t) t)
  | @insert k s hks ih =>
      simp only [Finset.sum_insert hks]
      exact ((RightContinuousStoppedMartingale.stoppedProcess_rightContinuous _
        (rowInverseMartingaleGain_rightContinuous u (selection k) hUsual source
          endpoint.a_pos.le T (alphaSeq k) (endpoint.alphaSeq_stopping k)) omega t).const_mul
            ((v n).weight k)).add ih

private theorem commonStoppedRowsMartingaleConvexRow_leftLimits
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {eta : Real}
    {u : ∀ n, TailConvexWeights n} {selection : Nat → Nat}
    {a : Real} {T : NNReal}
    {alphaSeq : Nat → Omega → WithTop NNReal}
    {alpha : Omega → WithTop NNReal} {R : Omega → Real}
    {hUsual : Filtration.UsualConditions mu F}
    {source : BoundedSemimartingaleSource S F mu}
    (endpoint : CommonStoppedRowsEndpoint
      (S := S) (F := F) (mu := mu) (eta := eta) u selection a T alphaSeq alpha R
      hUsual source)
    (v : ∀ n, TailConvexWeights n) (n : Nat) :
    ProcessHasLeftLimits (commonStoppedRowsMartingaleConvexRow endpoint v n) := by
  classical
  have hNativeLeft : ∀ k, ProcessHasLeftLimits
      (nativeMartingaleConvexRow u (selection k) hUsual source endpoint.a_pos.le T) :=
    fun k => nativeMartingaleConvexRow_leftLimits u (selection k) hUsual source
      endpoint.a_pos.le T
  have hGainLeft : ∀ k, ProcessHasLeftLimits
      (rowInverseMartingaleGain u (selection k) hUsual source endpoint.a_pos.le T
        (alphaSeq k) (endpoint.alphaSeq_stopping k)) := by
    intro k
    unfold rowInverseMartingaleGain
    exact (grid T (rowCommonLevel u (selection k))).martingaleIntegralProcess_hasLeftLimits
      (rowInverseCoefficientProcess (S := S) (F := F) (mu := mu)
        u (selection k) a T (alphaSeq k))
      (nativeMartingaleConvexRow u (selection k) hUsual source endpoint.a_pos.le T)
      (hNativeLeft k)
  have hRowLeft : ∀ k, ProcessHasLeftLimits
      (commonStoppedRowMartingale u selection a endpoint.a_pos.le T
        alphaSeq alpha endpoint.alphaSeq_stopping hUsual source k) := by
    intro k
    exact (hGainLeft k).stoppedProcess alpha
  unfold commonStoppedRowsMartingaleConvexRow TailConvexWeights.apply
  induction (v n).support using Finset.induction_on with
  | empty =>
      change ProcessHasLeftLimits (fun _ _ => 0)
      intro omega t
      exact tendsto_leftLim_of_tendsto
        (f := fun _ : NNReal => (0 : Real)) (a := t)
        ⟨0, tendsto_const_nhds⟩
  | @insert k s hks ih =>
      simp only [Finset.sum_insert hks]
      exact ((hRowLeft k).const_mul ((v n).weight k)).add ih

private theorem commonStoppedRowsMartingaleConvexRow_constant_after
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {eta : Real}
    {u : ∀ n, TailConvexWeights n} {selection : Nat → Nat}
    {a : Real} {T : NNReal}
    {alphaSeq : Nat → Omega → WithTop NNReal}
    {alpha : Omega → WithTop NNReal} {R : Omega → Real}
    {hUsual : Filtration.UsualConditions mu F}
    {source : BoundedSemimartingaleSource S F mu}
    (endpoint : CommonStoppedRowsEndpoint
      (S := S) (F := F) (mu := mu) (eta := eta) u selection a T alphaSeq alpha R
      hUsual source)
    (v : ∀ n, TailConvexWeights n) (n : Nat) {t : NNReal} (ht : T ≤ t) :
    commonStoppedRowsMartingaleConvexRow endpoint v n t =
      commonStoppedRowsMartingaleConvexRow endpoint v n T := by
  funext omega
  change (v n).apply (fun k =>
    fun omega =>
      commonStoppedRowMartingale u selection a endpoint.a_pos.le T
        alphaSeq alpha endpoint.alphaSeq_stopping hUsual source k t omega) omega =
    (v n).apply (fun k =>
      fun omega =>
        commonStoppedRowMartingale u selection a endpoint.a_pos.le T
          alphaSeq alpha endpoint.alphaSeq_stopping hUsual source k T omega) omega
  simp only [TailConvexWeights.apply]
  apply Finset.sum_congr rfl
  intro k hk
  have hαT : alpha omega ≤ (T : WithTop NNReal) :=
    (endpoint.alpha_le_alphaSeq k omega).trans (endpoint.alphaSeq_le_T k omega)
  have hαt : alpha omega ≤ (t : WithTop NNReal) :=
    hαT.trans (WithTop.coe_le_coe.mpr ht)
  unfold commonStoppedRowMartingale
  rw [MeasureTheory.stoppedProcess_eq_of_ge hαt,
    MeasureTheory.stoppedProcess_eq_of_ge hαT]

/-! ## The terminal limit and its Doob envelopes -/

theorem exists_commonStoppedRows_cadlagMartingaleLimit
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (hUsual : Filtration.UsualConditions mu F)
    (hS : IsSemimartingale S F mu)
    (source : BoundedSemimartingaleSource S F mu)
    (T : NNReal) {eta : Real} (heta : 0 < eta) :
    ∃ (a : Real) (u : ∀ n, TailConvexWeights n)
      (selection : Nat → Nat)
      (alphaSeq : Nat → Omega → WithTop NNReal)
      (alpha : Omega → WithTop NNReal) (R : Omega → Real),
      ∃ endpoint : CommonStoppedRowsEndpoint
        (eta := eta) u selection a T alphaSeq alpha R hUsual source,
        ∃ (v : ∀ n, TailConvexWeights n) (Z : Lp Real 2 mu)
          (Nbar Bbar Xbar : Nat → Process Omega) (M : Process Omega)
          (cutoff : Nat → Nat),
          CommonStoppedRowsCadlagMartingaleLimitData endpoint v Z Nbar Bbar Xbar
            M cutoff := by
  classical
  obtain ⟨a, u, selection, alphaSeq, alpha, R, endpoint, v, Z,
      Nbar, Bbar, Xbar, hData⟩ :=
    exists_commonStoppedRows_terminalTailConvexification hUsual hS source T heta
  obtain ⟨M, hMMartingale, hMRight, hMLeft, hMVersion⟩ :=
    exists_cadlagMartingaleVersion_condExpMartingaleProcess F hUsual Z
  have hNbarMartingale : ∀ n, Martingale (Nbar n) F mu := by
    intro n
    rw [hData.martingale_row_eq n]
    exact commonStoppedRowsMartingaleConvexRow_martingale endpoint v n
  have hNbarRight : ∀ n omega t, ContinuousWithinAt
      (Nbar n · omega) (Ici t) t := by
    intro n omega t
    rw [hData.martingale_row_eq n]
    exact commonStoppedRowsMartingaleConvexRow_rightContinuous endpoint v n omega t
  have hNbarLeft : ∀ n, ProcessHasLeftLimits (Nbar n) := by
    intro n
    rw [hData.martingale_row_eq n]
    exact commonStoppedRowsMartingaleConvexRow_leftLimits endpoint v n
  have hNbarConstant : ∀ n t, T ≤ t → Nbar n t = Nbar n T := by
    intro n t ht
    rw [hData.martingale_row_eq n]
    exact commonStoppedRowsMartingaleConvexRow_constant_after endpoint v n ht
  have hTerminalMem : ∀ n, MemLp (Nbar n T) (2 : ENNReal) mu := by
    intro n
    have hCommonMem : MemLp
        (commonStoppedRowsTerminalConvexRow endpoint v n : Omega → Real)
        (2 : ENNReal) mu :=
      Lp.memLp _
    exact (memLp_congr_ae (hData.terminal_row_eq n)).mp hCommonMem
  have hTerminalToLpEq : ∀ n,
      (hTerminalMem n).toLp (Nbar n T) =
        commonStoppedRowsTerminalConvexRow endpoint v n := by
    intro n
    exact (MemLp.toLp_congr (hTerminalMem n)
      (Lp.memLp (commonStoppedRowsTerminalConvexRow endpoint v n))
      (hData.terminal_row_eq n).symm).trans
        (Lp.toLp_coeFn (commonStoppedRowsTerminalConvexRow endpoint v n)
          (Lp.memLp _))
  have hTerminalLpTendsto : Tendsto
      (fun n => (hTerminalMem n).toLp (Nbar n T)) atTop (𝓝 Z) := by
    apply hData.terminal_tendsto.congr'
    exact Filter.Eventually.of_forall fun n => (hTerminalToLpEq n).symm
  have hTerminalNorm : Tendsto
      (fun n => eLpNorm (Nbar n T - (Z : Omega → Real))
        (2 : ENNReal) mu) atTop (𝓝 0) := by
    have hLp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
      (fun n => (hTerminalMem n).toLp (Nbar n T)) Z).mp hTerminalLpTendsto
    apply hLp.congr'
    exact Filter.Eventually.of_forall fun n => by
      apply eLpNorm_congr_ae
      filter_upwards [(hTerminalMem n).coeFn_toLp] with omega hEq
      simpa only [Pi.sub_apply] using
        congrArg (fun x : Real => x - (Z : Omega → Real) omega) hEq
  have hTerminalMeas : ∀ n,
      AEStronglyMeasurable[F T]
        (commonStoppedRowsTerminalConvexRow endpoint v n : Omega → Real) mu := by
    intro n
    apply (aestronglyMeasurable_congr (hData.terminal_row_eq n)).2
    exact ((hNbarMartingale n).stronglyMeasurable T).aestronglyMeasurable
  have hZFT : AEStronglyMeasurable[F T] (Z : Omega → Real) mu := by
    change Z ∈ {f : Lp Real 2 mu |
      AEStronglyMeasurable[F T] (f : Omega → Real) mu}
    apply (isClosed_aestronglyMeasurable (F := Real) (p := (2 : ENNReal))
      (μ := mu) (F.le T)).mem_of_tendsto hData.terminal_tendsto
    exact Filter.Eventually.of_forall hTerminalMeas
  have hCondT : condExpMartingaleProcess mu F Z T =ᵐ[mu]
      (Z : Omega → Real) := by
    change mu[(Z : Omega → Real) | F T] =ᵐ[mu] (Z : Omega → Real)
    exact condExp_of_aestronglyMeasurable' (F.le T) hZFT
      ((Lp.memLp Z).integrable (by norm_num))
  have hMTerminal : M T =ᵐ[mu] (Z : Omega → Real) :=
    (hMVersion T).trans hCondT
  have hMConstant : ∀ t, T ≤ t → M t =ᵐ[mu] M T := by
    intro t ht
    have hZFt : AEStronglyMeasurable[F t] (Z : Omega → Real) mu :=
      hZFT.mono (F.mono ht)
    have hCond : condExpMartingaleProcess mu F Z t =ᵐ[mu]
        (Z : Omega → Real) := by
      change mu[(Z : Omega → Real) | F t] =ᵐ[mu] (Z : Omega → Real)
      exact condExp_of_aestronglyMeasurable' (F.le t) hZFt
        ((Lp.memLp Z).integrable (by norm_num))
    exact (hMVersion t).trans (hCond.trans hMTerminal.symm)
  have hMMem : MemLp (M T) (2 : ENNReal) mu :=
    (memLp_congr_ae hMTerminal).mpr (Lp.memLp Z)
  have hDifferenceMem : ∀ n, MemLp (Nbar n T - M T)
      (2 : ENNReal) mu := fun n => (hTerminalMem n).sub hMMem
  have hDifferenceNormEq : ∀ n,
      eLpNorm (Nbar n T - M T) (2 : ENNReal) mu =
        eLpNorm (Nbar n T - (Z : Omega → Real)) (2 : ENNReal) mu := by
    intro n
    apply eLpNorm_congr_ae
    filter_upwards [hMTerminal] with omega hM
    simpa only [Pi.sub_apply] using
      congrArg (fun x : Real => Nbar n T omega - x) hM
  have hDifferenceNorm : Tendsto
      (fun n => eLpNorm (Nbar n T - M T) (2 : ENNReal) mu)
      atTop (𝓝 0) := by
    apply hTerminalNorm.congr'
    exact Filter.Eventually.of_forall fun n => (hDifferenceNormEq n).symm
  have hEnvelopeMem : ∀ n,
      MemLp (martingaleDifferenceEnvelope Nbar M T n)
        (2 : ENNReal) mu := by
    intro n
    exact Martingale.martingaleAbsoluteEnvelope_memLp
      ((hNbarMartingale n).sub hMMartingale) T (hDifferenceMem n)
  have hEnvelopeBound : ∀ n,
      eLpNorm (martingaleDifferenceEnvelope Nbar M T n)
        (2 : ENNReal) mu ≤
        2 * eLpNorm (Nbar n T - M T) (2 : ENNReal) mu := by
    intro n
    exact Martingale.eLpNorm_martingaleAbsoluteEnvelope_le_two_mul
      ((hNbarMartingale n).sub hMMartingale) T (hDifferenceMem n)
  have hEnvelopeNorm : Tendsto
      (fun n => eLpNorm (martingaleDifferenceEnvelope Nbar M T n)
        (2 : ENNReal) mu) atTop (𝓝 0) := by
    have hTwo : Tendsto
        (fun n => (2 : ENNReal) * eLpNorm (Nbar n T - M T)
          (2 : ENNReal) mu) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hDifferenceNorm
        (Or.inr (by norm_num : (2 : ENNReal) ≠ ∞))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hTwo (fun _ => bot_le) hEnvelopeBound
  have hEnvelopeInMeasure : TendstoInMeasure mu
      (fun n omega => martingaleDifferenceEnvelope Nbar M T n omega)
      atTop (fun _ => 0) := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := (2 : ENNReal))
      (by norm_num)
    apply hEnvelopeNorm.congr'
    exact Filter.Eventually.of_forall fun n => by
      apply eLpNorm_congr_ae
      exact Filter.Eventually.of_forall fun omega => by simp
  have hEnvelopeDominates : ∀ n, ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
      ‖Nbar n t omega - M t omega‖ ≤
        martingaleDifferenceEnvelope Nbar M T n omega := by
    intro n
    have hDom := Martingale.norm_le_martingaleAbsoluteEnvelope_ae
      ((hNbarMartingale n).sub hMMartingale) T (hDifferenceMem n)
      (fun omega t => (hNbarRight n omega t).sub (hMRight omega t))
    have hProcEq : Nbar n - M = (fun t => Nbar n t - M t) := by
      funext t
      rfl
    rw [hProcEq] at hDom
    simpa only [martingaleDifferenceEnvelope, Pi.sub_apply] using hDom
  obtain ⟨cutoff, hCutoff, hEnvelopeAE⟩ :=
    hEnvelopeInMeasure.exists_seq_tendsto_ae
  have hEnvelopeAE' : ∀ᵐ omega ∂mu,
      Tendsto (fun k => martingaleDifferenceEnvelope Nbar M T (cutoff k) omega)
        atTop (𝓝 0) := hEnvelopeAE
  have hDomAll : ∀ᵐ omega ∂mu, ∀ k, ∀ t, t ≤ T →
      ‖Nbar (cutoff k) t omega - M t omega‖ ≤
        martingaleDifferenceEnvelope Nbar M T (cutoff k) omega := by
    rw [ae_all_iff]
    intro k
    exact hEnvelopeDominates (cutoff k)
  have hUniform : ∀ᵐ omega ∂mu,
      TendstoUniformlyOn (fun k t => Nbar (cutoff k) t omega)
        (fun t => M t omega) atTop (Iic T) := by
    filter_upwards [hEnvelopeAE', hDomAll] with omega hE hD
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro epsilon hepsilon
    obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 hE) epsilon hepsilon
    filter_upwards [eventually_ge_atTop K] with k hk
    have hk' := hK k hk
    intro t ht
    have hE_nonneg : 0 ≤ martingaleDifferenceEnvelope Nbar M T (cutoff k) omega := by
      unfold martingaleDifferenceEnvelope
        FactorialChronologicalGrid.martingaleAbsoluteEnvelope
      exact Real.sqrt_nonneg _
    calc
      dist (M t omega) (Nbar (cutoff k) t omega) =
          ‖Nbar (cutoff k) t omega - M t omega‖ := by
        rw [Real.dist_eq, abs_sub_comm, Real.norm_eq_abs]
      _ ≤ martingaleDifferenceEnvelope Nbar M T (cutoff k) omega :=
        hD k t ht
      _ < epsilon := by
        have hk'' : martingaleDifferenceEnvelope Nbar M T (cutoff k) omega <
            epsilon := by
          simpa [Real.dist_eq, abs_of_nonneg hE_nonneg] using hk'
        exact hk''
  have hNbarZero : ∀ n, Nbar n 0 = 0 := by
    intro n
    rw [hData.martingale_row_eq n]
    funext omega
    unfold commonStoppedRowsMartingaleConvexRow TailConvexWeights.apply
    apply Finset.sum_eq_zero
    intro k hk
    change (v n).weight k *
      commonStoppedRowMartingale u selection a endpoint.a_pos.le T
        alphaSeq alpha endpoint.alphaSeq_stopping hUsual source k 0 omega = 0
    rw [commonStoppedRowMartingale_zero endpoint k]
    simp
  have hMZero : M 0 =ᵐ[mu] 0 := by
    filter_upwards [hUniform] with omega hω
    have hPoint := hω.tendsto_at (show (0 : NNReal) ∈ Iic T by simp)
    have hPoint' : Tendsto (fun _ : Nat => (0 : Real)) atTop (𝓝 (M 0 omega)) := by
      apply hPoint.congr'
      exact Filter.Eventually.of_forall fun k =>
        congrFun (hNbarZero (cutoff k)) omega
    exact tendsto_nhds_unique hPoint' tendsto_const_nhds
  refine ⟨a, u, selection, alphaSeq, alpha, R, endpoint, v, Z,
    Nbar, Bbar, Xbar, M, cutoff, ?_⟩
  exact
    { convexification := hData
      cutoff_strictMono := hCutoff
      M_martingale := hMMartingale
      M_rightContinuous := hMRight
      M_leftLimits := hMLeft
      M_condExp := hMVersion
      M_zero := hMZero
      M_constant_after := hMConstant
      Nbar_martingale := hNbarMartingale
      Nbar_rightContinuous := hNbarRight
      Nbar_leftLimits := hNbarLeft
      Nbar_constant_after := hNbarConstant
      terminal_difference_norm_tendsto := hDifferenceNorm
      envelope_memLp := hEnvelopeMem
      envelope_norm_bound := hEnvelopeBound
      envelope_norm_tendsto := hEnvelopeNorm
      envelope_tendstoInMeasure := hEnvelopeInMeasure
      envelope_dominates := hEnvelopeDominates
      cutoff_envelope_tendsto_ae := hEnvelopeAE'
      rows_tendstoUniformlyOn_ae := hUniform }

end HorizonFactorialGrid

end FTAPTheorem42
