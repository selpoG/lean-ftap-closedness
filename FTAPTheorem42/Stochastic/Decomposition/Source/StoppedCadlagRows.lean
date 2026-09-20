/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Source.StoppedProcessConvexification

/-!
# Càdlàg martingale versions of the stopped process rows

The terminal coordinate of each common-weight martingale row is an `L²`
variable.  Conditional-expectation regularization therefore supplies a
càdlàg true martingale version.  The version is identified with the raw row
on every time of its base factorial grid, and at each fixed canonical
skeleton time once the row level is sufficiently high.  No equality between
the version and the raw row is asserted between grid times.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

/-! ## Terminal variables and a skeleton bridge -/

private theorem stoppedLimitSkeleton_pair_time
    (T : NNReal) (r : Nat) (k : Fin (size T r + 1)) :
    (stoppedLimitSkeleton T (Nat.pair r k.1)).1 =
      (grid T r).time k := by
  change (grid T (Nat.unpair (Nat.pair r k.1)).1).sampledTime
      (Nat.unpair (Nat.pair r k.1)).2 = (grid T r).time k
  rw [show Nat.unpair (Nat.pair r k.1) = (r, k.1) by simp]
  exact (grid T r).sampledTime_fin_eq k

theorem stoppedCadlagRow_eq_rawRow_on_skeleton
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a)
    (T : NNReal) (w : ∀ n, TailConvexWeights n)
    (terminal : Nat → Lp Real 2 mu)
    (Mbar : Nat → Process Omega) (Mcad : Nat → Process Omega)
    (hTerminal : ∀ n, terminal n =
      (w n).applyVector (fun r =>
        stoppedMartingaleApproximationToLp source ha T
          (stoppedLimitSkeleton T (stoppedLimitTerminalIndex T)).1
          (stoppedLimitSkeleton T (stoppedLimitTerminalIndex T)).2 r))
    (hMbar : ∀ n i,
      Mbar n (stoppedLimitSkeleton T i).1 =ᵐ[mu]
        (((w n).applyVector (fun r =>
          stoppedMartingaleApproximationToLp source ha T
            (stoppedLimitSkeleton T i).1
            (stoppedLimitSkeleton T i).2 r) : Lp Real 2 mu) :
          Omega → Real))
    (hVersion : ∀ n t,
      Mcad n t =ᵐ[mu]
        condExpMartingaleProcess mu F (terminal n) t)
    (n i : Nat) (hin : (Nat.unpair i).1 ≤ n) :
    Mcad n (stoppedLimitSkeleton T i).1 =ᵐ[mu]
      Mbar n (stoppedLimitSkeleton T i).1 := by
  let terminalIndex := stoppedLimitTerminalIndex T
  have hiT : (stoppedLimitSkeleton T i).1 ≤
      (stoppedLimitSkeleton T terminalIndex).1 := by
    rw [show (stoppedLimitSkeleton T terminalIndex).1 = T by
      simp only [terminalIndex, stoppedLimitSkeleton_terminalIndex]]
    exact (stoppedLimitSkeleton T i).2
  have hLaw := condExpL2_applyVector_stoppedMartingale_skeleton_eq
    source ha T i terminalIndex hiT (w n) hin
  have hTerminalMem : MemLp (terminal n : Omega → Real) 2 mu :=
    Lp.memLp (terminal n)
  have hBridge := hTerminalMem.condExpL2_ae_eq_condExp (𝕜 := Real)
    (F.le (stoppedLimitSkeleton T i).1)
  rw [Lp.toLp_coeFn (terminal n) hTerminalMem] at hBridge
  have hLaw' :
      (condExpL2 Real Real (F.le (stoppedLimitSkeleton T i).1)
        (terminal n) : Lp Real 2 mu) =
        (w n).applyVector (fun r =>
          stoppedMartingaleApproximationToLp source ha T
            (stoppedLimitSkeleton T i).1
            (stoppedLimitSkeleton T i).2 r) := by
    simpa only [hTerminal n] using hLaw
  have hLawFun := congrArg
    (fun z : Lp Real 2 mu => (z : Omega → Real)) hLaw'
  filter_upwards [hVersion n (stoppedLimitSkeleton T i).1,
      hBridge, hMbar n i] with omega hVersionOmega hBridgeOmega hMbarOmega
  rw [hVersionOmega]
  change mu[(terminal n : Omega → Real) |
      F (stoppedLimitSkeleton T i).1] omega = _
  rw [← hBridgeOmega]
  exact (congrFun hLawFun omega).trans hMbarOmega.symm

/-! ## The row-wise regularization endpoint -/

theorem exists_stoppedProcessConvexification_cadlag_rows
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
      (∀ n, Xcorr n - Xbar n = Mcad n - Mbar n) := by
  obtain ⟨w, predictableLimit, martingaleLimit, M, Xbar, Mbar, A,
      hPredictable, hMartingale, hM, hMRight, hMLeft, hMSkeleton,
      hXbar, hAPredictable, hAStop, hABV, hAVar, hXbarSkeleton,
      hMbarSkeleton, hASkeleton⟩ :=
    exists_stoppedProcessConvexification_rows hUsual source ha T
  let terminal : Nat → Lp Real 2 mu := fun n =>
    (w n).applyVector (fun r =>
      stoppedMartingaleApproximationToLp source ha T
        (stoppedLimitSkeleton T (stoppedLimitTerminalIndex T)).1
        (stoppedLimitSkeleton T (stoppedLimitTerminalIndex T)).2 r)
  have hCadlag (n : Nat) :=
    exists_cadlagMartingaleVersion_condExpMartingaleProcess F hUsual
      (terminal n)
  choose Mcad hMcad hMcadRight hMcadLeft hMcadVersion using hCadlag
  let Xcorr : Nat → Process Omega := fun n => Mcad n + A n
  have hSkeletonEq : ∀ n i, (Nat.unpair i).1 ≤ n →
      Mcad n (stoppedLimitSkeleton T i).1 =ᵐ[mu]
        Mbar n (stoppedLimitSkeleton T i).1 := by
    intro n i hin
    exact stoppedCadlagRow_eq_rawRow_on_skeleton source ha T w
      terminal Mbar Mcad (fun n => rfl) hMbarSkeleton hMcadVersion n i hin
  have hBaseGridEq : ∀ n (k : Fin (size T n + 1)),
      Mcad n ((grid T n).time k) =ᵐ[mu]
        Mbar n ((grid T n).time k) := by
    intro n k
    have hSkel := hSkeletonEq n (Nat.pair n k.1) (by simp)
    have hTime := stoppedLimitSkeleton_pair_time T n k
    rw [hTime] at hSkel
    exact hSkel
  refine ⟨w, predictableLimit, martingaleLimit, M, Xbar, Mbar, A,
    terminal, Mcad, Xcorr, hPredictable, hMartingale, hM, hMRight, hMLeft,
    hMSkeleton, hXbar, hAPredictable, hAStop, hABV, hAVar, hXbarSkeleton,
    hMbarSkeleton, hASkeleton, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rfl
  · exact hMcad
  · exact hMcadRight
  · exact hMcadLeft
  · exact hMcadVersion
  · exact hBaseGridEq
  · exact hSkeletonEq
  · intro n
    rfl
  · intro n
    funext t omega
    change Mcad n t omega + A n t omega - Xbar n t omega =
      Mcad n t omega - Mbar n t omega
    rw [congrFun (congrFun (hXbar n) t) omega]
    simp only [Pi.add_apply]
    ring

end HorizonFactorialGrid

end FTAPTheorem42
