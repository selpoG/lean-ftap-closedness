/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Source.StoppedCadlagRows
import FTAPTheorem42.Stochastic.Martingale.Basic.MartingaleAbsoluteEnvelope

/-!
# Finite-horizon convergence of the regularized martingale rows

The common terminal coordinates converge in `L²`.  The row-wise càdlàg
martingale versions and the common limiting martingale therefore have a
vanishing terminal difference in `L²`.  Doob's factorial-grid maximal
estimate turns this into a vanishing `L²` envelope on `[0,T]`, and hence into
convergence in measure of the envelopes.  No identity between a regularized
row and its raw row between grid times, or after `T`, is used here.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

open _root_.FTAPTheorem42.FactorialChronologicalGrid

/-! The data already supplied by the preceding row-wise regularization
endpoint.  Keeping it as a proposition lets the convergence consumer return
the same rows, rather than selecting a second set of convex weights. -/

def StoppedCadlagRowsData
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal)
    (w : ∀ n, TailConvexWeights n)
    (predictableLimit martingaleLimit : Nat → Lp Real 2 mu)
    (M : Process Omega)
    (Xbar Mbar A : Nat → Process Omega)
    (terminal : Nat → Lp Real 2 mu)
    (Mcad Xcorr : Nat → Process Omega) : Prop :=
  (∀ j, Tendsto
    (fun n => (w n).applyVector (fun r =>
      stoppedPredictableApproximationToLp source ha T
        (stoppedLimitSkeleton T j).1 (stoppedLimitSkeleton T j).2 r))
    atTop (𝓝 (predictableLimit j))) ∧
  (∀ j, Tendsto
    (fun n => (w n).applyVector (fun r =>
      stoppedMartingaleApproximationToLp source ha T
        (stoppedLimitSkeleton T j).1 (stoppedLimitSkeleton T j).2 r))
    atTop (𝓝 (martingaleLimit j))) ∧
  Martingale M F mu ∧
  (∀ omega t, ContinuousWithinAt (M · omega) (Ici t) t) ∧
  ProcessHasLeftLimits M ∧
  (∀ i, M (stoppedLimitSkeleton T i).1 =ᵐ[mu]
    (martingaleLimit i : Omega → Real)) ∧
  (∀ n, Xbar n = Mbar n + A n) ∧
  (∀ n, IsStronglyPredictable F (A n)) ∧
  (∀ n, MeasureTheory.stoppedProcess (A n)
    (fun _ : Omega => (T : WithTop NNReal)) = A n) ∧
  (∀ n omega, BoundedVariationOn (A n · omega) Set.univ) ∧
  (∀ n, ∀ᵐ omega ∂mu,
    eVariationOn (A n · omega) Set.univ ≤
      ENNReal.ofReal (a + 2 * max source.bound 0)) ∧
  (∀ n i, Xbar n (stoppedLimitSkeleton T i).1 =ᵐ[mu]
    (w n).apply (fun r => stoppedSourceApproximation a T
      (stoppedLimitSkeleton T i).1 (stoppedLimitSkeleton T i).2 r S F mu)) ∧
  (∀ n i, Mbar n (stoppedLimitSkeleton T i).1 =ᵐ[mu]
    (((w n).applyVector (fun r =>
      stoppedMartingaleApproximationToLp source ha T
        (stoppedLimitSkeleton T i).1 (stoppedLimitSkeleton T i).2 r) :
      Lp Real 2 mu) : Omega → Real)) ∧
  (∀ n i, A n (stoppedLimitSkeleton T i).1 =ᵐ[mu]
    (((w n).applyVector (fun r =>
      stoppedPredictableApproximationToLp source ha T
        (stoppedLimitSkeleton T i).1 (stoppedLimitSkeleton T i).2 r) :
      Lp Real 2 mu) : Omega → Real)) ∧
  (∀ n, terminal n =
    (w n).applyVector (fun r =>
      stoppedMartingaleApproximationToLp source ha T
        (stoppedLimitSkeleton T (stoppedLimitTerminalIndex T)).1
        (stoppedLimitSkeleton T (stoppedLimitTerminalIndex T)).2 r)) ∧
  (∀ n, Martingale (Mcad n) F mu) ∧
  (∀ n omega t, ContinuousWithinAt (Mcad n · omega) (Ici t) t) ∧
  (∀ n, ProcessHasLeftLimits (Mcad n)) ∧
  (∀ n t, Mcad n t =ᵐ[mu]
    condExpMartingaleProcess mu F (terminal n) t) ∧
  (∀ n k, Mcad n ((grid T n).time k) =ᵐ[mu]
    Mbar n ((grid T n).time k)) ∧
  (∀ n i, (Nat.unpair i).1 ≤ n →
    Mcad n (stoppedLimitSkeleton T i).1 =ᵐ[mu]
      Mbar n (stoppedLimitSkeleton T i).1) ∧
  (∀ n, Xcorr n = Mcad n + A n) ∧
  (∀ n, Xcorr n - Xbar n = Mcad n - Mbar n)

theorem stoppedCadlagRows_terminal_l2_finiteHorizon_envelope
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal)
    (w : ∀ n, TailConvexWeights n)
    (martingaleLimit : Nat → Lp Real 2 mu)
    (M : Process Omega)
    (Mbar : Nat → Process Omega)
    (terminal : Nat → Lp Real 2 mu)
    (Mcad : Nat → Process Omega)
    (hTerminal : ∀ n, terminal n =
      (w n).applyVector (fun r =>
        stoppedMartingaleApproximationToLp source ha T
          (stoppedLimitSkeleton T (stoppedLimitTerminalIndex T)).1
          (stoppedLimitSkeleton T (stoppedLimitTerminalIndex T)).2 r))
    (hTerminalTendsto : Tendsto (fun n => terminal n) atTop
      (𝓝 (martingaleLimit (stoppedLimitTerminalIndex T))))
    (hM : Martingale M F mu)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (hMSkeleton : M (stoppedLimitSkeleton T (stoppedLimitTerminalIndex T)).1 =ᵐ[mu]
      (martingaleLimit (stoppedLimitTerminalIndex T) : Omega → Real))
    (hMbarSkeleton : ∀ n i,
      Mbar n (stoppedLimitSkeleton T i).1 =ᵐ[mu]
        (((w n).applyVector (fun r =>
          stoppedMartingaleApproximationToLp source ha T
            (stoppedLimitSkeleton T i).1
            (stoppedLimitSkeleton T i).2 r) : Lp Real 2 mu) :
          Omega → Real))
    (hMcad : ∀ n, Martingale (Mcad n) F mu)
    (hMcadRight : ∀ n omega t,
      ContinuousWithinAt (Mcad n · omega) (Ici t) t)
    (hBaseGrid : ∀ n (k : Fin (size T n + 1)),
      Mcad n ((grid T n).time k) =ᵐ[mu]
        Mbar n ((grid T n).time k)) :
    (Tendsto
      (fun n => eLpNorm
        ((terminal n : Omega → Real) -
          (martingaleLimit (stoppedLimitTerminalIndex T) : Omega → Real))
        (2 : ENNReal) mu)
      atTop (𝓝 0)) ∧
    (∀ n, MemLp (Mcad n T) (2 : ENNReal) mu) ∧
    MemLp (M T) (2 : ENNReal) mu ∧
    (∀ n, MemLp (Mcad n T - M T) (2 : ENNReal) mu) ∧
    (∀ n, MemLp
      (FactorialChronologicalGrid.martingaleAbsoluteEnvelope
        (fun t => Mcad n t - M t) T) (2 : ENNReal) mu) ∧
    (∀ n, eLpNorm
      (FactorialChronologicalGrid.martingaleAbsoluteEnvelope
        (fun t => Mcad n t - M t) T) (2 : ENNReal) mu ≤
      2 * eLpNorm (Mcad n T - M T) (2 : ENNReal) mu) ∧
    Tendsto (fun n => eLpNorm
      (FactorialChronologicalGrid.martingaleAbsoluteEnvelope
        (fun t => Mcad n t - M t) T) (2 : ENNReal) mu)
      atTop (𝓝 0) ∧
    TendstoInMeasure mu
      (fun n omega =>
        FactorialChronologicalGrid.martingaleAbsoluteEnvelope
          (fun t => Mcad n t - M t) T omega)
      atTop (fun _ => 0) ∧
    (∀ n, ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
      ‖Mcad n t omega - M t omega‖ ≤
        FactorialChronologicalGrid.martingaleAbsoluteEnvelope
          (fun t => Mcad n t - M t) T omega) := by
  let terminalIndex := stoppedLimitTerminalIndex T
  have hTerminalMem : ∀ n, MemLp (terminal n : Omega → Real)
      (2 : ENNReal) mu := fun n => Lp.memLp (terminal n)
  have hLimitMem : MemLp (martingaleLimit terminalIndex : Omega → Real)
      (2 : ENNReal) mu := Lp.memLp (martingaleLimit terminalIndex)
  have hTerminalNorm : Tendsto (fun n => eLpNorm
      ((terminal n : Omega → Real) -
        (martingaleLimit terminalIndex : Omega → Real))
      (2 : ENNReal) mu) atTop (𝓝 0) := by
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
      (fun n => terminal n) (martingaleLimit terminalIndex)).mp
      hTerminalTendsto
  have hMcadTerminal : ∀ n, Mcad n T =ᵐ[mu] (terminal n : Omega → Real) := by
    intro n
    let k : Fin (size T n + 1) :=
      ⟨size T n, Nat.lt_succ_self _⟩
    have hBase := hBaseGrid n k
    have hTime : (grid T n).time k = T := by
      rw [← (grid T n).sampledTime_fin_eq k]
      exact sampledTime_size T n
    rw [hTime] at hBase
    have hMbar := hMbarSkeleton n terminalIndex
    have hMbarT : Mbar n T =ᵐ[mu]
        (((w n).applyVector (fun r =>
          stoppedMartingaleApproximationToLp source ha T
            (stoppedLimitSkeleton T terminalIndex).1
            (stoppedLimitSkeleton T terminalIndex).2 r) : Lp Real 2 mu) :
          Omega → Real) := by
      convert hMbar using 1
      · simp only [terminalIndex, stoppedLimitSkeleton_terminalIndex]
    have hTerminalFun := congrArg
      (fun z : Lp Real 2 mu => (z : Omega → Real)) (hTerminal n)
    filter_upwards [hBase, hMbarT] with omega hBaseOmega hMbarOmega
    exact hBaseOmega.trans (hMbarOmega.trans
      (congrFun hTerminalFun omega).symm)
  have hMTerminal : M T =ᵐ[mu]
      (martingaleLimit terminalIndex : Omega → Real) := by
    simpa only [terminalIndex, stoppedLimitSkeleton_terminalIndex] using
      hMSkeleton
  have hMcadMem : ∀ n, MemLp (Mcad n T) (2 : ENNReal) mu := by
    intro n
    exact (memLp_congr_ae (hMcadTerminal n)).mpr (hTerminalMem n)
  have hMMem : MemLp (M T) (2 : ENNReal) mu :=
    (memLp_congr_ae hMTerminal).mpr hLimitMem
  have hDifferenceMem : ∀ n, MemLp (Mcad n T - M T)
      (2 : ENNReal) mu := fun n => (hMcadMem n).sub hMMem
  have hDifferenceTerminalNorm : ∀ n, eLpNorm (Mcad n T - M T)
      (2 : ENNReal) mu = eLpNorm
        ((terminal n : Omega → Real) -
          (martingaleLimit terminalIndex : Omega → Real))
        (2 : ENNReal) mu := by
    intro n
    apply eLpNorm_congr_ae
    exact (hMcadTerminal n).sub hMTerminal
  have hDifferenceNorm : Tendsto (fun n => eLpNorm (Mcad n T - M T)
      (2 : ENNReal) mu) atTop (𝓝 0) := by
    apply hTerminalNorm.congr'
    exact Filter.Eventually.of_forall fun n =>
      (hDifferenceTerminalNorm n).symm
  have hEnvelopeMem : ∀ n, MemLp
      (FactorialChronologicalGrid.martingaleAbsoluteEnvelope
        (fun t => Mcad n t - M t) T) (2 : ENNReal) mu := by
    intro n
    exact Martingale.martingaleAbsoluteEnvelope_memLp
      ((hMcad n).sub hM) T (hDifferenceMem n)
  have hEnvelopeBound : ∀ n, eLpNorm
      (FactorialChronologicalGrid.martingaleAbsoluteEnvelope
        (fun t => Mcad n t - M t) T) (2 : ENNReal) mu ≤
      2 * eLpNorm (Mcad n T - M T) (2 : ENNReal) mu := by
    intro n
    exact Martingale.eLpNorm_martingaleAbsoluteEnvelope_le_two_mul
      ((hMcad n).sub hM) T (hDifferenceMem n)
  have hEnvelopeNorm : Tendsto (fun n => eLpNorm
      (FactorialChronologicalGrid.martingaleAbsoluteEnvelope
        (fun t => Mcad n t - M t) T) (2 : ENNReal) mu)
      atTop (𝓝 0) := by
    have hTwo : Tendsto (fun n => (2 : ENNReal) *
        eLpNorm (Mcad n T - M T) (2 : ENNReal) mu)
        atTop (𝓝 0) := by
      simpa using
        (ENNReal.Tendsto.const_mul hDifferenceNorm
          (Or.inr (by norm_num : (2 : ENNReal) ≠ ∞)))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hTwo ?_ ?_
    · exact fun _ => bot_le
    · exact hEnvelopeBound
  have hEnvelopeInMeasure : TendstoInMeasure mu
      (fun n omega =>
        FactorialChronologicalGrid.martingaleAbsoluteEnvelope
          (fun t => Mcad n t - M t) T omega)
      atTop (fun _ => 0) := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := (2 : ENNReal))
      (by norm_num)
    apply hEnvelopeNorm.congr'
    exact Filter.Eventually.of_forall fun n => by
      apply eLpNorm_congr_ae
      exact Filter.Eventually.of_forall fun omega => by simp
  have hEnvelopeDominates : ∀ n, ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
      ‖Mcad n t omega - M t omega‖ ≤
        FactorialChronologicalGrid.martingaleAbsoluteEnvelope
          (fun t => Mcad n t - M t) T omega := by
    intro n
    apply Martingale.norm_le_martingaleAbsoluteEnvelope_ae
      ((hMcad n).sub hM) T
      (hDifferenceMem n)
    intro omega t
    exact (hMcadRight n omega t).sub (hMRight omega t)
  exact ⟨hTerminalNorm, hMcadMem, hMMem, hDifferenceMem, hEnvelopeMem,
    hEnvelopeBound, hEnvelopeNorm, hEnvelopeInMeasure, hEnvelopeDominates⟩

/-! The public consumer below makes the preceding row endpoint choose the
weights.  The envelope theorem is then applied to exactly those rows. -/

theorem exists_stoppedProcessConvexification_cadlag_rows_terminal_envelope
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (hUsual : Filtration.UsualConditions mu F)
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) :
    ∃ (w : ∀ n, TailConvexWeights n)
      (predictableLimit martingaleLimit : Nat → Lp Real 2 mu)
      (M : Process Omega)
      (Xbar Mbar A : Nat → Process Omega)
      (terminal : Nat → Lp Real 2 mu)
      (Mcad Xcorr : Nat → Process Omega),
      StoppedCadlagRowsData source ha T w predictableLimit martingaleLimit M
        Xbar Mbar A terminal Mcad Xcorr ∧
      Tendsto (fun n => eLpNorm
        ((terminal n : Omega → Real) -
          (martingaleLimit (stoppedLimitTerminalIndex T) : Omega → Real))
        (2 : ENNReal) mu) atTop (𝓝 0) ∧
      (∀ n, MemLp (Mcad n T) (2 : ENNReal) mu) ∧
      MemLp (M T) (2 : ENNReal) mu ∧
      (∀ n, MemLp (Mcad n T - M T) (2 : ENNReal) mu) ∧
      (∀ n, MemLp
        (FactorialChronologicalGrid.martingaleAbsoluteEnvelope
          (fun t => Mcad n t - M t) T) (2 : ENNReal) mu) ∧
      (∀ n, eLpNorm
        (FactorialChronologicalGrid.martingaleAbsoluteEnvelope
          (fun t => Mcad n t - M t) T) (2 : ENNReal) mu ≤
        2 * eLpNorm (Mcad n T - M T) (2 : ENNReal) mu) ∧
      Tendsto (fun n => eLpNorm
        (FactorialChronologicalGrid.martingaleAbsoluteEnvelope
          (fun t => Mcad n t - M t) T) (2 : ENNReal) mu)
        atTop (𝓝 0) ∧
      TendstoInMeasure mu
        (fun n omega =>
          FactorialChronologicalGrid.martingaleAbsoluteEnvelope
            (fun t => Mcad n t - M t) T omega)
        atTop (fun _ => 0) ∧
      (∀ n, ∀ᵐ omega ∂mu, ∀ t, t ≤ T →
        ‖Mcad n t omega - M t omega‖ ≤
          FactorialChronologicalGrid.martingaleAbsoluteEnvelope
            (fun t => Mcad n t - M t) T omega) := by
  obtain ⟨w, predictableLimit, martingaleLimit, M, Xbar, Mbar, A,
      terminal, Mcad, Xcorr, hPredictable, hMartingale, hM, hMRight,
      hMLeft, hMSkeleton, hXbar, hAPredictable, hAStop, hABV, hAVar,
      hXbarSkeleton, hMbarSkeleton, hASkeleton, hTerminal,
      hMcad, hMcadRight, hMcadLeft, hMcadVersion, hBaseGrid,
      hSkeletonEq, hXcorr, hDifference⟩ :=
    exists_stoppedProcessConvexification_cadlag_rows hUsual source ha T
  have hTerminalTendsto : Tendsto (fun n => terminal n) atTop
      (𝓝 (martingaleLimit (stoppedLimitTerminalIndex T))) := by
    apply (hMartingale (stoppedLimitTerminalIndex T)).congr'
    exact Filter.Eventually.of_forall fun n => (hTerminal n).symm
  have hMTerminal := hMSkeleton (stoppedLimitTerminalIndex T)
  obtain ⟨hTerminalNorm, hMcadMem, hMMem, hDifferenceMem, hEnvelopeMem,
      hEnvelopeBound, hEnvelopeNorm, hEnvelopeInMeasure,
      hEnvelopeDominates⟩ :=
    stoppedCadlagRows_terminal_l2_finiteHorizon_envelope source ha T w
      martingaleLimit M Mbar terminal Mcad hTerminal hTerminalTendsto hM
      hMRight hMTerminal hMbarSkeleton hMcad hMcadRight hBaseGrid
  refine ⟨w, predictableLimit, martingaleLimit, M, Xbar, Mbar, A,
    terminal, Mcad, Xcorr, ?_, hTerminalNorm, hMcadMem, hMMem,
    hDifferenceMem, hEnvelopeMem, hEnvelopeBound, hEnvelopeNorm,
    hEnvelopeInMeasure, hEnvelopeDominates⟩
  exact ⟨hPredictable, hMartingale, hM, hMRight, hMLeft, hMSkeleton,
    hXbar, hAPredictable, hAStop, hABV, hAVar, hXbarSkeleton,
    hMbarSkeleton, hASkeleton, hTerminal, hMcad, hMcadRight, hMcadLeft,
    hMcadVersion, hBaseGrid, hSkeletonEq, hXcorr, hDifference⟩

end HorizonFactorialGrid

end FTAPTheorem42
