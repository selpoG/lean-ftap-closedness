/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStopRows

/-!
# A source-independent analytic interface for common-stop rows

The bounded and envelope routes produce the same finite-grid analytic data:
martingale rows, residual rows, their exact stopped-source identity, terminal
`L²` bounds, and finite-grid residual controls.  This module records that data
without retaining a source-specific provider and applies one terminal tail
convexification to it.  Only finite-grid variation and horizon supremum are
recorded; no continuous-time total variation is asserted.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

/-! ## The common source-independent certificate -/

structure CommonStoppedRowsUniformAnalyticData
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    (T : NNReal) (alpha : Omega → WithTop NNReal)
    (hAlphaStop : IsStoppingTime F alpha)
    (selection : Nat → Nat)
    (N B : Nat → Process Omega)
    (V : Omega → Real) (L : Real)
    (hUsual : Filtration.UsualConditions mu F) : Prop where
  alpha_le_horizon : ∀ omega, alpha omega ≤ (T : WithTop NNReal)
  selection_strictMono : StrictMono selection
  martingale : ∀ k, Martingale (N k) F mu
  martingale_zero : ∀ k, N k 0 = 0
  martingale_rightContinuous : ∀ k omega t,
    ContinuousWithinAt ((N k) · omega) (Ici t) t
  terminal_memLp : ∀ k, MemLp (N k T) (2 : ENNReal) mu
  terminal_bound_nonneg : 0 ≤ L
  terminal_norm_le : ∀ k,
    ‖(terminal_memLp k).toLp (N k T)‖ ≤ L
  residual_memLp : MemLp V (2 : ENNReal) mu
  residual_integrable : Integrable V mu
  residual_nonneg : ∀ omega, 0 ≤ V omega
  residual_baseGridVariation : ∀ k, ∀ᵐ omega ∂mu,
    (∑ j ∈ Finset.range (size T (selection k)),
      |B k ((grid T (selection k)).sampledTime (j + 1)) omega -
        B k ((grid T (selection k)).sampledTime j) omega|) ≤ V omega
  residual_horizon_sup : ∀ k, ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
    |B k t omega| ≤ V omega
  stoppedSource_eq_martingale_add_residual : ∀ k t omega,
    MeasureTheory.stoppedProcess S alpha t omega - S 0 omega =
      N k t omega + B k t omega

/-! ## Full-time rows and terminal coordinates -/

noncomputable def commonStoppedRowsUniformAnalyticMartingaleConvexRow
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {T : NNReal} {alpha : Omega → WithTop NNReal}
    {hAlphaStop : IsStoppingTime F alpha}
    {selection : Nat → Nat} {N B : Nat → Process Omega}
    {V : Omega → Real} {L : Real}
    {hUsual : Filtration.UsualConditions mu F}
    (_data : CommonStoppedRowsUniformAnalyticData (S := S) T alpha hAlphaStop selection N B V L
      hUsual)
    (v : ∀ n, TailConvexWeights n) (n : Nat) : Process Omega :=
  fun t omega =>
    (v n).apply (fun k => fun omega => N k t omega) omega

noncomputable def commonStoppedRowsUniformAnalyticResidualConvexRow
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {T : NNReal} {alpha : Omega → WithTop NNReal}
    {hAlphaStop : IsStoppingTime F alpha}
    {selection : Nat → Nat} {N B : Nat → Process Omega}
    {V : Omega → Real} {L : Real}
    {hUsual : Filtration.UsualConditions mu F}
    (_data : CommonStoppedRowsUniformAnalyticData (S := S) T alpha hAlphaStop selection N B V L
      hUsual)
    (v : ∀ n, TailConvexWeights n) (n : Nat) : Process Omega :=
  fun t omega =>
    (v n).apply (fun k => fun omega => B k t omega) omega

noncomputable def commonStoppedRowsUniformAnalyticTerminalConvexRow
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {T : NNReal} {alpha : Omega → WithTop NNReal}
    {hAlphaStop : IsStoppingTime F alpha}
    {selection : Nat → Nat} {N B : Nat → Process Omega}
    {V : Omega → Real} {L : Real}
    {hUsual : Filtration.UsualConditions mu F}
    (data : CommonStoppedRowsUniformAnalyticData (S := S) T alpha hAlphaStop selection N B V L
      hUsual)
    (v : ∀ n, TailConvexWeights n) (n : Nat) : Lp Real 2 mu :=
  (v n).applyVector (fun k => (data.terminal_memLp k).toLp (N k T))

/-! ## The generic terminal-tail output -/

structure CommonStoppedRowsUniformAnalyticTailConvexificationData
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {T : NNReal} {alpha : Omega → WithTop NNReal}
    {hAlphaStop : IsStoppingTime F alpha}
    {selection : Nat → Nat} {N B : Nat → Process Omega}
    {V : Omega → Real} {L : Real}
    {hUsual : Filtration.UsualConditions mu F}
    (data : CommonStoppedRowsUniformAnalyticData (S := S) T alpha hAlphaStop selection N B V L
      hUsual)
    (v : ∀ n, TailConvexWeights n) (Z : Lp Real 2 mu)
    (Nbar Bbar Xbar : Nat → Process Omega) : Prop where
  terminal_tendsto : Tendsto
    (fun n => commonStoppedRowsUniformAnalyticTerminalConvexRow data v n)
    atTop (𝓝 Z)
  terminal_row_eq : ∀ n,
    (commonStoppedRowsUniformAnalyticTerminalConvexRow data v n : Omega → Real) =ᵐ[mu]
      Nbar n T
  martingale_row_eq : ∀ n,
    Nbar n = commonStoppedRowsUniformAnalyticMartingaleConvexRow data v n
  residual_row_eq : ∀ n,
    Bbar n = commonStoppedRowsUniformAnalyticResidualConvexRow data v n
  source_row_eq : ∀ n,
    Xbar n = commonStoppedRowsSourceConvexRow (S := S) (alpha := alpha) v n
  source_row_eq_stopped : ∀ n t omega,
    Xbar n t omega =
      MeasureTheory.stoppedProcess S alpha t omega - S 0 omega
  stoppedSource_eq_add : ∀ n t omega,
    MeasureTheory.stoppedProcess S alpha t omega - S 0 omega =
      Nbar n t omega + Bbar n t omega

/-! ## The generic terminal-tail consumer -/

theorem CommonStoppedRowsUniformAnalyticData.exists_terminalTailConvexification
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu F]
    {T : NNReal} {alpha : Omega → WithTop NNReal}
    {hAlphaStop : IsStoppingTime F alpha}
    {selection : Nat → Nat} {N B : Nat → Process Omega}
    {V : Omega → Real} {L : Real}
    {hUsual : Filtration.UsualConditions mu F}
    (data : CommonStoppedRowsUniformAnalyticData (S := S) T alpha hAlphaStop selection N B V L
      hUsual) :
    ∃ (v : ∀ n, TailConvexWeights n) (Z : Lp Real 2 mu)
      (Nbar Bbar Xbar : Nat → Process Omega),
      CommonStoppedRowsUniformAnalyticTailConvexificationData data v Z Nbar Bbar Xbar := by
  let x : Nat → Lp Real 2 mu := fun k =>
    (data.terminal_memLp k).toLp (N k T)
  have hx : ∀ k, ‖x k‖ ≤ L := by
    intro k
    exact data.terminal_norm_le k
  obtain ⟨Z, hZ⟩ :=
    TailConvexWeights.exists_tendsto_tailNormSqNearMinimizers hx data.terminal_bound_nonneg
  let v : ∀ n, TailConvexWeights n :=
    TailConvexWeights.tailNormSqNearMinimizers x
  let Nbar : Nat → Process Omega := fun n =>
    commonStoppedRowsUniformAnalyticMartingaleConvexRow data v n
  let Bbar : Nat → Process Omega := fun n =>
    commonStoppedRowsUniformAnalyticResidualConvexRow data v n
  let Xbar : Nat → Process Omega := fun n =>
    commonStoppedRowsSourceConvexRow (S := S) (alpha := alpha) v n
  have hTerminalTendsto : Tendsto
      (fun n => commonStoppedRowsUniformAnalyticTerminalConvexRow data v n)
      atTop (𝓝 Z) := by
    simpa [v, commonStoppedRowsUniformAnalyticTerminalConvexRow, x] using hZ
  have hTerminalRow : ∀ n,
      (commonStoppedRowsUniformAnalyticTerminalConvexRow data v n : Omega → Real) =ᵐ[mu]
        Nbar n T := by
    intro n
    have hRaw := (v n).applyVector_coeFn_ae
      (fun k => (data.terminal_memLp k).toLp (N k T))
      (fun k => N k T)
      (fun k => MemLp.coeFn_toLp (data.terminal_memLp k))
    change (commonStoppedRowsUniformAnalyticTerminalConvexRow data v n : Omega → Real) =ᵐ[mu]
      (v n).apply (fun k => fun omega => N k T omega)
    exact hRaw
  have hSourceRow : ∀ n t omega,
      Xbar n t omega =
        MeasureTheory.stoppedProcess S alpha t omega - S 0 omega := by
    intro n t omega
    change (v n).apply (fun _ omega =>
      MeasureTheory.stoppedProcess S alpha t omega - S 0 omega) omega = _
    simp only [TailConvexWeights.apply]
    rw [← Finset.sum_mul, (v n).sum_eq_one, one_mul]
  have hDecomposition : ∀ n t omega,
      MeasureTheory.stoppedProcess S alpha t omega - S 0 omega =
        Nbar n t omega + Bbar n t omega := by
    intro n t omega
    change MeasureTheory.stoppedProcess S alpha t omega - S 0 omega =
      (v n).apply (fun k => fun omega => N k t omega) omega +
        (v n).apply (fun k => fun omega => B k t omega) omega
    have hConst :
        MeasureTheory.stoppedProcess S alpha t omega - S 0 omega =
          ∑ k ∈ (v n).support, (v n).weight k *
            (MeasureTheory.stoppedProcess S alpha t omega - S 0 omega) := by
      rw [← Finset.sum_mul, (v n).sum_eq_one, one_mul]
    rw [hConst]
    calc
      (∑ k ∈ (v n).support, (v n).weight k *
          (MeasureTheory.stoppedProcess S alpha t omega - S 0 omega)) =
          ∑ k ∈ (v n).support, (v n).weight k *
            (N k t omega + B k t omega) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [data.stoppedSource_eq_martingale_add_residual k t omega]
      _ = (∑ k ∈ (v n).support, (v n).weight k * N k t omega) +
          ∑ k ∈ (v n).support, (v n).weight k * B k t omega := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
      _ = Nbar n t omega + Bbar n t omega := by
        rfl
  refine ⟨v, Z, Nbar, Bbar, Xbar, ?_⟩
  refine ⟨hTerminalTendsto, hTerminalRow, ?_, ?_, ?_, hSourceRow, hDecomposition⟩
  · intro n
    rfl
  · intro n
    rfl
  · intro n
    rfl

end HorizonFactorialGrid

end FTAPTheorem42
