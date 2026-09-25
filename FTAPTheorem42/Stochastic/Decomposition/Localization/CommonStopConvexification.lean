/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.Localization.CommonStopRows
import FTAPTheorem42.Stochastic.Martingale.Quadratic.DiscreteMartingaleSquaredIncrement

/-!
# Terminal convexification of common-stop rows

The common-stop endpoint gives one family of rows with a common stopped source.
Their martingale terminals have a uniform `L²` bound.  We apply the existing
Hilbert tail convexification once to these terminal variables and use exactly
the same weights for the full-time martingale and residual rows.  Thus the
source decomposition is preserved at every time; no component-dependent
reselection is made.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

/-! ## The three full-time rows and their terminal `L²` coordinates -/

noncomputable def commonStoppedRowsMartingaleConvexRow
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
    (v : ∀ n, TailConvexWeights n) (n : Nat) : Process Omega :=
  fun t omega =>
    (v n).apply (fun k =>
      fun omega =>
        commonStoppedRowMartingale u selection a endpoint.a_pos.le T
          alphaSeq alpha endpoint.alphaSeq_stopping hUsual
          source k t omega) omega

noncomputable def commonStoppedRowsResidualConvexRow
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
    (v : ∀ n, TailConvexWeights n) (n : Nat) : Process Omega :=
  fun t omega =>
    (v n).apply (fun k =>
      fun omega =>
        commonStoppedRowResidual u selection a endpoint.a_pos.le T
          alphaSeq alpha endpoint.alphaSeq_stopping hUsual
          source k t omega) omega

noncomputable def commonStoppedRowsTerminalConvexRow
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
  (v : ∀ n, TailConvexWeights n) (n : Nat) : Lp Real 2 mu :=
  (v n).applyVector (fun k =>
    (endpoint.data.martingale_terminal_memLp k).toLp
      (commonStoppedRowMartingale u selection a endpoint.a_pos.le T
        alphaSeq alpha endpoint.alphaSeq_stopping hUsual source k T))

/-! ## Data returned by the terminal convexification -/

structure CommonStoppedRowsTerminalTailConvexificationData
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
    (Nbar Bbar Xbar : Nat → Process Omega) : Prop where
  terminal_tendsto : Tendsto
    (fun n => commonStoppedRowsTerminalConvexRow endpoint v n) atTop (𝓝 Z)
  terminal_row_eq : ∀ n,
    (commonStoppedRowsTerminalConvexRow endpoint v n : Omega → Real) =ᵐ[mu]
      Nbar n T
  martingale_row_eq : ∀ n,
    Nbar n = commonStoppedRowsMartingaleConvexRow endpoint v n
  residual_row_eq : ∀ n,
    Bbar n = commonStoppedRowsResidualConvexRow endpoint v n
  source_row_eq : ∀ n,
    Xbar n = commonStoppedRowsSourceConvexRow (S := S) (alpha := alpha) v n
  source_row_eq_stopped : ∀ n t omega,
    Xbar n t omega =
      MeasureTheory.stoppedProcess S alpha t omega - S 0 omega
  stoppedSource_eq_add : ∀ n t omega,
    MeasureTheory.stoppedProcess S alpha t omega - S 0 omega =
      Nbar n t omega + Bbar n t omega

/-! ## The terminal-row Hilbert estimate -/

theorem commonStoppedRowsTerminal_norm_le
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
    ‖(endpoint.data.martingale_terminal_memLp k).toLp
        (commonStoppedRowMartingale u selection a endpoint.a_pos.le T
          alphaSeq alpha endpoint.alphaSeq_stopping hUsual source k T)‖ ≤
      4 * (a + 4 * max source.bound 0) := by
  let N : Process Omega :=
    commonStoppedRowMartingale u selection a endpoint.a_pos.le T
      alphaSeq alpha endpoint.alphaSeq_stopping hUsual source k
  let hN : MemLp (N T) (2 : ENNReal) mu :=
    endpoint.data.martingale_terminal_memLp k
  have hC : 0 ≤ 4 * (a + 4 * max source.bound 0) := by
    have hInner : 0 ≤ a + 4 * max source.bound 0 := by
      nlinarith [endpoint.a_pos.le, le_max_right source.bound 0]
    positivity
  rw [MeasureTheory.Lp.norm_toLp]
  calc
    ENNReal.toReal (eLpNorm (N T) (2 : ENNReal) mu) ≤
        ENNReal.toReal (ENNReal.ofReal (4 * (a + 4 * max source.bound 0))) := by
      apply ENNReal.toReal_mono ENNReal.ofReal_ne_top
      apply DiscreteMartingaleSquaredIncrement.eLpNorm_two_le_of_integral_sq_le hN hC
      calc
        (∫ omega, (N T omega) ^ 2 ∂mu) ≤
            16 * (a + 4 * max source.bound 0) ^ 2 := by
          simpa [N] using endpoint.data.martingale_terminal_L2_uniform_bound k
        _ = (4 * (a + 4 * max source.bound 0)) ^ 2 := by ring
    _ = 4 * (a + 4 * max source.bound 0) :=
      ENNReal.toReal_ofReal hC

/-! ## One common family of terminal weights -/

theorem CommonStoppedRowsEndpoint.exists_terminalTailConvexification
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
      hUsual source) :
    ∃ (v : ∀ n, TailConvexWeights n) (Z : Lp Real 2 mu)
      (Nbar Bbar Xbar : Nat → Process Omega),
      CommonStoppedRowsTerminalTailConvexificationData endpoint v Z Nbar Bbar Xbar := by
  let x : Nat → Lp Real 2 mu := fun k =>
    (endpoint.data.martingale_terminal_memLp k).toLp
      (commonStoppedRowMartingale u selection a endpoint.a_pos.le T
        alphaSeq alpha endpoint.alphaSeq_stopping hUsual source k T)
  have hx : ∀ k, ‖x k‖ ≤ 4 * (a + 4 * max source.bound 0) := by
    intro k
    exact commonStoppedRowsTerminal_norm_le endpoint k
  have hC : 0 ≤ 4 * (a + 4 * max source.bound 0) := by
    have hInner : 0 ≤ a + 4 * max source.bound 0 := by
      nlinarith [endpoint.a_pos.le, le_max_right source.bound 0]
    positivity
  obtain ⟨Z, hZ⟩ :=
    TailConvexWeights.exists_tendsto_tailNormSqNearMinimizers hx hC
  let v : ∀ n, TailConvexWeights n :=
    TailConvexWeights.tailNormSqNearMinimizers x
  let Nbar : Nat → Process Omega := fun n =>
    commonStoppedRowsMartingaleConvexRow endpoint v n
  let Bbar : Nat → Process Omega := fun n =>
    commonStoppedRowsResidualConvexRow endpoint v n
  let Xbar : Nat → Process Omega := fun n =>
    commonStoppedRowsSourceConvexRow (S := S) (alpha := alpha) v n
  have hTerminalTendsto : Tendsto
      (fun n => commonStoppedRowsTerminalConvexRow endpoint v n)
      atTop (𝓝 Z) := by
    simpa [v, commonStoppedRowsTerminalConvexRow, x] using hZ
  have hTerminalRow : ∀ n,
      (commonStoppedRowsTerminalConvexRow endpoint v n : Omega → Real) =ᵐ[mu]
        Nbar n T := by
    intro n
    have hRaw := (v n).applyVector_coeFn_ae
      (fun k =>
        (endpoint.data.martingale_terminal_memLp k).toLp
          (commonStoppedRowMartingale u selection a endpoint.a_pos.le T
            alphaSeq alpha endpoint.alphaSeq_stopping hUsual source k T))
      (fun k => commonStoppedRowMartingale u selection a endpoint.a_pos.le T
        alphaSeq alpha endpoint.alphaSeq_stopping hUsual source k T)
      (fun k => MemLp.coeFn_toLp (endpoint.data.martingale_terminal_memLp k))
    change (commonStoppedRowsTerminalConvexRow endpoint v n : Omega → Real) =ᵐ[mu]
      (v n).apply (fun k => fun omega =>
        commonStoppedRowMartingale u selection a endpoint.a_pos.le T
          alphaSeq alpha endpoint.alphaSeq_stopping hUsual source k T omega)
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
      (v n).apply (fun k =>
        fun omega =>
          commonStoppedRowMartingale u selection a endpoint.a_pos.le T
            alphaSeq alpha endpoint.alphaSeq_stopping hUsual source k t omega) omega +
        (v n).apply (fun k =>
          fun omega =>
            commonStoppedRowResidual u selection a endpoint.a_pos.le T
              alphaSeq alpha endpoint.alphaSeq_stopping hUsual source k t omega) omega
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
            (commonStoppedRowMartingale u selection a endpoint.a_pos.le T
              alphaSeq alpha endpoint.alphaSeq_stopping hUsual source k t omega +
             commonStoppedRowResidual u selection a endpoint.a_pos.le T
              alphaSeq alpha endpoint.alphaSeq_stopping hUsual source k t omega) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [endpoint.data.stoppedSource_eq_martingale_add_residual k t omega]
      _ = (∑ k ∈ (v n).support, (v n).weight k *
            commonStoppedRowMartingale u selection a endpoint.a_pos.le T
              alphaSeq alpha endpoint.alphaSeq_stopping hUsual source k t omega) +
          ∑ k ∈ (v n).support, (v n).weight k *
            commonStoppedRowResidual u selection a endpoint.a_pos.le T
              alphaSeq alpha endpoint.alphaSeq_stopping hUsual source k t omega := by
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

/-! ## Public producer: common stop followed by one terminal convexification -/

theorem exists_commonStoppedRows_terminalTailConvexification
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
      ∃ endpoint : CommonStoppedRowsEndpoint
        (eta := eta) u selection a T alphaSeq alpha R hUsual source,
        ∃ (v : ∀ n, TailConvexWeights n) (Z : Lp Real 2 mu)
          (Nbar Bbar Xbar : Nat → Process Omega),
          CommonStoppedRowsTerminalTailConvexificationData endpoint v Z Nbar Bbar Xbar := by
  obtain ⟨a, u, selection, alphaSeq, alpha, R, endpoint⟩ :=
    exists_commonGateStoppedRows hUsual hS source T heta
  obtain ⟨v, Z, Nbar, Bbar, Xbar, hData⟩ :=
    endpoint.exists_terminalTailConvexification
  exact ⟨a, u, selection, alphaSeq, alpha, R, endpoint,
    v, Z, Nbar, Bbar, Xbar, hData⟩

end HorizonFactorialGrid

end FTAPTheorem42
