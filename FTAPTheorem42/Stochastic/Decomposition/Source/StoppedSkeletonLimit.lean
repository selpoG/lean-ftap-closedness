/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Decomposition.Source.StoppedCommonConvexLimit
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# A canonical dense skeleton for stopped factorial Doob limits

We enumerate all points of all fixed-horizon factorial grids.  This gives a
right-dense skeleton of `[0,T]`.  Nestedness implies that every skeleton time
is represented exactly, rather than merely approximated, on every sufficiently
fine grid.  The common stopped-component convexification is then specialized
to this canonical skeleton.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

/-- Enumerate the constantly extended points of every fixed-horizon
factorial grid. -/
noncomputable def stoppedLimitSkeleton (T : NNReal) (n : Nat) : Set.Iic T :=
  let p := Nat.unpair n
  ⟨(grid T p.1).sampledTime p.2, by
    have hIndex :
        (grid T p.1).natIndex p.2 ≤
          (grid T p.1).natIndex (size T p.1) := by
      change min p.2 (size T p.1) ≤
        min (size T p.1) (size T p.1)
      simp
    exact ((grid T p.1).monotone_time hIndex).trans_eq
      (sampledTime_size T p.1)⟩

/-- Each skeleton point occurs on the grid whose level is its first paired
coordinate. -/
theorem stoppedLimitSkeleton_mem_grid_range (T : NNReal) (n : Nat) :
    (stoppedLimitSkeleton T n).1 ∈
      Set.range (grid T (Nat.unpair n).1).time := by
  exact ⟨(grid T (Nat.unpair n).1).natIndex (Nat.unpair n).2, rfl⟩

/-- A distinguished skeleton index whose value is the horizon. -/
noncomputable def stoppedLimitTerminalIndex (T : NNReal) : Nat :=
  Nat.pair 0 (size T 0)

@[simp]
theorem stoppedLimitSkeleton_terminalIndex (T : NNReal) :
    (stoppedLimitSkeleton T (stoppedLimitTerminalIndex T)).1 = T := by
  change (grid T (Nat.unpair (Nat.pair 0 (size T 0))).1).sampledTime
      (Nat.unpair (Nat.pair 0 (size T 0))).2 = T
  rw [show Nat.unpair (Nat.pair 0 (size T 0)) = (0, size T 0) by simp]
  exact sampledTime_size T 0

/-- A skeleton point is represented exactly by every later right-factorial
approximation. -/
theorem grid_time_approxIndex_stoppedLimitSkeleton_eq
    (T : NNReal) (n : Nat) {r : Nat} (hr : (Nat.unpair n).1 ≤ r) :
    (grid T r).time
        (approxIndex T (stoppedLimitSkeleton T n).1
          (stoppedLimitSkeleton T n).2 r) =
      (stoppedLimitSkeleton T n).1 := by
  apply grid_time_approxIndex_eq_of_mem_range
  exact range_grid_mono T hr (stoppedLimitSkeleton_mem_grid_range T n)

/-- On a sufficiently fine grid, the stopped martingale approximation obeys
the conditional-expectation identity at two ordered skeleton times in the
original filtration. -/
theorem condExp_stoppedMartingaleApproximation_skeleton_ae_eq
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    (a : Real) (T : NNReal) (i j : Nat)
    (hij : (stoppedLimitSkeleton T i).1 ≤
      (stoppedLimitSkeleton T j).1)
    (r : Nat) (hir : (Nat.unpair i).1 ≤ r) :
    mu[
      stoppedMartingaleApproximation a T
        (stoppedLimitSkeleton T j).1 (stoppedLimitSkeleton T j).2
        r S F mu |
      F (stoppedLimitSkeleton T i).1] =ᵐ[mu]
      stoppedMartingaleApproximation a T
        (stoppedLimitSkeleton T i).1 (stoppedLimitSkeleton T i).2
        r S F mu := by
  have hConditional := condExp_stoppedMartingaleApproximation_ae_eq
    source a T
      (stoppedLimitSkeleton T i).1 (stoppedLimitSkeleton T j).1
      (stoppedLimitSkeleton T i).2 (stoppedLimitSkeleton T j).2
      hij r
  change mu[
      stoppedMartingaleApproximation a T
        (stoppedLimitSkeleton T j).1 (stoppedLimitSkeleton T j).2
        r S F mu |
      F ((grid T r).sampledTime (approxIndex T
        (stoppedLimitSkeleton T i).1 (stoppedLimitSkeleton T i).2 r))] =ᵐ[mu]
    stoppedMartingaleApproximation a T
      (stoppedLimitSkeleton T i).1 (stoppedLimitSkeleton T i).2
      r S F mu at hConditional
  rw [(grid T r).sampledTime_fin_eq (approxIndex T
    (stoppedLimitSkeleton T i).1 (stoppedLimitSkeleton T i).2 r)] at hConditional
  rw [grid_time_approxIndex_stoppedLimitSkeleton_eq T i hir] at hConditional
  exact hConditional

/-- The preceding conditional-expectation identity as an exact identity in
`L²`. -/
theorem condExpL2_stoppedMartingaleApproximationToLp_skeleton_eq
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) (i j : Nat)
    (hij : (stoppedLimitSkeleton T i).1 ≤
      (stoppedLimitSkeleton T j).1)
    (r : Nat) (hir : (Nat.unpair i).1 ≤ r) :
    ((condExpL2 Real Real
        (F.le (stoppedLimitSkeleton T i).1)
        (stoppedMartingaleApproximationToLp source ha T
          (stoppedLimitSkeleton T j).1 (stoppedLimitSkeleton T j).2 r) :
      lpMeas Real Real (F (stoppedLimitSkeleton T i).1) 2 mu) :
        Lp Real 2 mu) =
      stoppedMartingaleApproximationToLp source ha T
        (stoppedLimitSkeleton T i).1 (stoppedLimitSkeleton T i).2 r := by
  apply Lp.ext
  have hjMem := memLp_two_stoppedMartingaleApproximation source ha T
    (stoppedLimitSkeleton T j).1 (stoppedLimitSkeleton T j).2 r
  exact (hjMem.condExpL2_ae_eq_condExp
      (F.le (stoppedLimitSkeleton T i).1)).trans
    ((condExp_stoppedMartingaleApproximation_skeleton_ae_eq
        source a T i j hij r hir).trans
      (MemLp.coeFn_toLp
        (memLp_two_stoppedMartingaleApproximation source ha T
          (stoppedLimitSkeleton T i).1 (stoppedLimitSkeleton T i).2 r)).symm)

/-- A sufficiently late convex row preserves the stopped martingale law at
ordered skeleton times. -/
theorem condExpL2_applyVector_stoppedMartingale_skeleton_eq
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) (i j : Nat)
    (hij : (stoppedLimitSkeleton T i).1 ≤
      (stoppedLimitSkeleton T j).1)
    {n : Nat} (w : TailConvexWeights n)
    (hin : (Nat.unpair i).1 ≤ n) :
    ((condExpL2 Real Real
        (F.le (stoppedLimitSkeleton T i).1)
        (w.applyVector fun r =>
          stoppedMartingaleApproximationToLp source ha T
            (stoppedLimitSkeleton T j).1 (stoppedLimitSkeleton T j).2 r) :
      lpMeas Real Real (F (stoppedLimitSkeleton T i).1) 2 mu) :
        Lp Real 2 mu) =
      w.applyVector fun r =>
        stoppedMartingaleApproximationToLp source ha T
          (stoppedLimitSkeleton T i).1 (stoppedLimitSkeleton T i).2 r := by
  classical
  unfold TailConvexWeights.applyVector
  simp only [map_sum, map_smul, Submodule.coe_sum,
    Submodule.coe_smul_of_tower]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  exact condExpL2_stoppedMartingaleApproximationToLp_skeleton_eq
    source ha T i j hij r (hin.trans (w.tail r hr))

/-- The canonical fixed-horizon skeleton is right-dense in `[0,T]`. -/
theorem stoppedLimitSkeleton_rightDense (T : NNReal) :
    ∀ t : Set.Iic T,
      t ∈ closure (Set.range (stoppedLimitSkeleton T) ∩ Set.Ici t) := by
  intro t
  let index : Nat → Nat := fun r =>
    Nat.pair r (Nat.ceil (t.1 * (r.factorial : NNReal)))
  have hValue : ∀ r,
      (stoppedLimitSkeleton T (index r)).1 =
        (grid T r).time (approxIndex T t.1 t.2 r) := by
    intro r
    change (grid T (Nat.unpair (index r)).1).sampledTime
        (Nat.unpair (index r)).2 =
      (grid T r).time (approxIndex T t.1 t.2 r)
    rw [show Nat.unpair (index r) =
        (r, Nat.ceil (t.1 * (r.factorial : NNReal))) by
      simp [index]]
    exact (grid T r).sampledTime_fin_eq
      (approxIndex T t.1 t.2 r)
  have hTendsto : Tendsto
      (fun r => stoppedLimitSkeleton T (index r)) atTop (𝓝 t) := by
    apply tendsto_subtype_rng.mpr
    convert tendsto_grid_time_approxIndex T t.1 t.2 using 1
    funext r
    exact hValue r
  apply mem_closure_of_tendsto hTendsto
  filter_upwards [] with r
  constructor
  · refine ⟨index r, ?_⟩
    rfl
  · change t.1 ≤ (stoppedLimitSkeleton T (index r)).1
    rw [hValue r]
    change t.1 ≤ min (FactorialChronologicalGrid.approx r t.1) T
    exact le_min (FactorialChronologicalGrid.le_approx r t.1) t.2

/-- The common `L²` convex limits of the stopped Doob martingale components
retain the martingale conditional-expectation law on the canonical dense
skeleton. -/
theorem exists_common_stoppedComponentConvexification_skeleton_martingale
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (source : BoundedSemimartingaleSource S F mu)
    {a : Real} (ha : 0 ≤ a) (T : NNReal) :
    ∃ (w : ∀ n, TailConvexWeights n)
      (predictableLimit martingaleLimit : Nat → Lp Real 2 mu),
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
      ∀ i j,
        (stoppedLimitSkeleton T i).1 ≤ (stoppedLimitSkeleton T j).1 →
        ((condExpL2 Real Real
            (F.le (stoppedLimitSkeleton T i).1) (martingaleLimit j) :
          lpMeas Real Real (F (stoppedLimitSkeleton T i).1) 2 mu) :
            Lp Real 2 mu) = martingaleLimit i := by
  obtain ⟨w, predictableLimit, martingaleLimit,
      hPredictable, hMartingale⟩ :=
    exists_common_stoppedComponentConvexification source ha T
      (stoppedLimitSkeleton T)
  refine ⟨w, predictableLimit, martingaleLimit,
    hPredictable, hMartingale, ?_⟩
  intro i j hij
  let P : Lp Real 2 mu →L[Real] Lp Real 2 mu :=
    (lpMeas Real Real (F (stoppedLimitSkeleton T i).1) 2 mu).subtypeL.comp
      (condExpL2 Real Real (F.le (stoppedLimitSkeleton T i).1))
  have hProjected : Tendsto
      (fun n => P ((w n).applyVector (fun r =>
        stoppedMartingaleApproximationToLp source ha T
          (stoppedLimitSkeleton T j).1 (stoppedLimitSkeleton T j).2 r)))
      atTop (𝓝 (P (martingaleLimit j))) :=
    P.continuous.continuousAt.tendsto.comp (hMartingale j)
  have hEventually : ∀ᶠ n in atTop,
      P ((w n).applyVector (fun r =>
        stoppedMartingaleApproximationToLp source ha T
          (stoppedLimitSkeleton T j).1 (stoppedLimitSkeleton T j).2 r)) =
        (w n).applyVector (fun r =>
          stoppedMartingaleApproximationToLp source ha T
            (stoppedLimitSkeleton T i).1 (stoppedLimitSkeleton T i).2 r) := by
    filter_upwards [eventually_ge_atTop (Nat.unpair i).1] with n hn
    exact condExpL2_applyVector_stoppedMartingale_skeleton_eq
      source ha T i j hij (w n) hn
  have hProjectedAsRow : Tendsto
      (fun n => (w n).applyVector (fun r =>
        stoppedMartingaleApproximationToLp source ha T
          (stoppedLimitSkeleton T i).1 (stoppedLimitSkeleton T i).2 r))
      atTop (𝓝 (P (martingaleLimit j))) :=
    hProjected.congr' hEventually
  exact tendsto_nhds_unique hProjectedAsRow (hMartingale i)

end HorizonFactorialGrid

end FTAPTheorem42
