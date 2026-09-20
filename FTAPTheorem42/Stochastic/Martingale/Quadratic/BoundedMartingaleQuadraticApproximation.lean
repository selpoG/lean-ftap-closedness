/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Quadratic.FiniteGridMartingaleQuadraticDecomposition
import FTAPTheorem42.Stochastic.Martingale.Basic.ConditionalExpectationL2

/-!
# Finite-horizon quadratic approximations of bounded martingales

Fix a deterministic horizon `T`.  Consecutive factorial grids, clamped at
`T`, decompose the square of the stopped source martingale into a true
martingale transform and a nonnegative sum of squared increments.  The grid
level is shifted by `ceil T`, so every grid already reaches the horizon.

This is the concrete approximation sequence used to construct the
finite-horizon martingale energy measure.  No quadratic-variation process or
countably additive energy control is assumed in this module.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace BoundedMartingaleQuadraticApproximation

/-- The factorial-grid level used for the `n`-th approximation. -/
noncomputable def level (T : NNReal) (n : Nat) : Nat := Nat.ceil T + n

theorem ceil_le_level (T : NNReal) (n : Nat) : Nat.ceil T <= level T n := by
  exact Nat.le_add_right _ _

theorem self_le_level (T : NNReal) (n : Nat) : n <= level T n := by
  exact Nat.le_add_left n (Nat.ceil T)

theorem level_mono (T : NNReal) : Monotone (level T) := by
  intro n m hnm
  exact Nat.add_le_add_left hnm (Nat.ceil T)

/-- The `n`-th factorial grid, clamped at the deterministic horizon. -/
noncomputable def grid (T : NNReal) (n : Nat) :
    ChronologicalGrid NNReal ((level T n) * (level T n).factorial) :=
  FactorialChronologicalGrid.stoppedGrid T (level T n)

omit [MeasurableSpace Omega] in
@[simp]
theorem grid_sampledTime_zero (T : NNReal) (n : Nat) :
    (grid T n).sampledTime 0 = 0 := by
  simp [grid, ChronologicalGrid.sampledTime, ChronologicalGrid.natIndex,
    FactorialChronologicalGrid.stoppedGrid_time, FactorialChronologicalGrid.grid]

omit [MeasurableSpace Omega] in
@[simp]
theorem grid_sampledTime_last (T : NNReal) (n : Nat) :
    (grid T n).sampledTime ((level T n) * (level T n).factorial) = T := by
  simpa [grid, ChronologicalGrid.sampledTime] using
    FactorialChronologicalGrid.stoppedGrid_last_time T (ceil_le_level T n)

omit [MeasurableSpace Omega] in
/-- The stopped source is right-continuous. -/
theorem stoppedSource_rightContinuous
    (M : Process Omega)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) :
    ∀ omega t, ContinuousWithinAt
      (deterministicallyStoppedProcess M T · omega) (Ici t) t := by
  exact RightContinuousStoppedMartingale.stoppedProcess_rightContinuous
    M (τ := fun _ : Omega => (T : WithTop NNReal)) hMRight

/-- The martingale term in the square decomposition on the `n`-th grid. -/
noncomputable def martingalePart
    (M : Process Omega) (T : NNReal) (n : Nat) : Process Omega :=
  (2 : Real) • (grid T n).martingaleIntegralProcess
    (deterministicallyStoppedProcess M T) (deterministicallyStoppedProcess M T)

/-- The nonnegative squared-increment term on the `n`-th grid.  Between two
grid points this process need not be increasing. -/
noncomputable def squaredIncrementPart
    (M : Process Omega) (T : NNReal) (n : Nat) : Process Omega :=
  (grid T n).squaredIncrementProcess (deterministicallyStoppedProcess M T)

omit [MeasurableSpace Omega] in
/-- Every grid approximation gives the exact square decomposition, at every
time and sample point. -/
theorem martingalePart_add_squaredIncrementPart
    (M : Process Omega) (T t : NNReal) (n : Nat) (omega : Omega) :
    martingalePart M T n t omega + squaredIncrementPart M T n t omega =
      deterministicallyStoppedProcess M T t omega ^ 2
        - deterministicallyStoppedProcess M T 0 omega ^ 2 := by
  have hIdentity :=
    (grid T n).two_mul_martingaleIntegralProcess_add_squaredIncrementProcess
      (deterministicallyStoppedProcess M T) t omega
  simpa only [martingalePart, squaredIncrementPart, Pi.smul_apply, smul_eq_mul,
    grid_sampledTime_last, grid_sampledTime_zero, min_zero,
    min_eq_left (show min t T <= T from min_le_right t T),
    deterministicallyStoppedProcess_apply, min_self] using hIdentity

omit [MeasurableSpace Omega] in
/-- The squared-increment term is pointwise nonnegative. -/
theorem squaredIncrementPart_nonneg
    (M : Process Omega) (T t : NNReal) (n : Nat) (omega : Omega) :
    0 <= squaredIncrementPart M T n t omega :=
  (grid T n).squaredIncrementProcess_nonneg (deterministicallyStoppedProcess M T) t omega

/-- A deterministic bound on the source over `[0,T]` makes every martingale
term in the quadratic approximation a true martingale. -/
theorem martingalePart_isMartingale
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    [SigmaFiniteFiltration mu F]
    {M : Process Omega} (hM : Martingale M F mu)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) {C : Real}
    (hMBound : ∀ t, t <= T -> ∀ᵐ omega ∂mu,
      |M t omega| <= C)
    (n : Nat) :
    Martingale (martingalePart M T n) F mu := by
  have hStoppedBound : ∀ t, ∀ᵐ omega ∂mu,
      |deterministicallyStoppedProcess M T t omega| <= C := by
    intro t
    simpa only [deterministicallyStoppedProcess_apply] using
      hMBound (min t T) (min_le_right t T)
  exact (grid T n).two_smul_martingaleIntegralProcess_isMartingale
    (C := fun _ => C) (martingale_deterministicallyStopped hM hMRight T)
    (stoppedSource_rightContinuous M hMRight T) hStoppedBound

/-- The terminal value of every martingale approximation is square
integrable. -/
theorem martingalePart_terminal_memLp_two
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    [SigmaFiniteFiltration mu F]
    {M : Process Omega} (hM : Martingale M F mu)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu)
    {C : Real}
    (hMBound : ∀ t, t <= T -> ∀ᵐ omega ∂mu,
      |M t omega| <= C)
    (n : Nat) :
    MemLp (martingalePart M T n T) (2 : ENNReal) mu := by
  let G := grid T n
  let X := deterministicallyStoppedProcess M T
  let N := (level T n) * (level T n).factorial
  have hX : Martingale X F mu := martingale_deterministicallyStopped hM hMRight T
  have hXLp : ∀ k, MemLp (G.natSample X k) (2 : ENNReal) mu := by
    intro k
    exact stoppedProcess_const_memLp_two hM T hMT (G.sampledTime k)
  have hXBound : ∀ k, ∀ᵐ omega ∂mu,
      |G.natSample X k omega| <= C := by
    intro k
    simpa only [ChronologicalGrid.natSample, X, deterministicallyStoppedProcess_apply] using
      hMBound (min (G.sampledTime k) T) (min_le_right _ _)
  have hDiscrete : MemLp
      (discretePredictableIntegral (G.natSample X) (G.natSample X) N)
      (2 : ENNReal) mu :=
    DiscretePredictableIntegral.memLp_two
      (ChronologicalGrid.Martingale.natSample (G := G) hX) hXLp
      (G.stronglyAdapted_natSample hX.stronglyAdapted) hXBound N
  have hTerminal : martingalePart M T n T =
      (2 : Real) •
        discretePredictableIntegral (G.natSample X) (G.natSample X) N := by
    funext omega
    have hLast : G.sampledTime N = T := by
      simpa only [G, N] using grid_sampledTime_last T n
    have hAtLast :
        G.martingaleIntegralProcess X X T omega =
          G.martingaleIntegralProcess X X (G.sampledTime N) omega :=
      congrArg (fun u => G.martingaleIntegralProcess X X u omega) hLast.symm
    calc
      martingalePart M T n T omega =
          2 * G.martingaleIntegralProcess X X T omega := rfl
      _ = 2 * G.martingaleIntegralProcess X X (G.sampledTime N) omega :=
        congrArg (fun z : Real => 2 * z) hAtLast
      _ = 2 * discretePredictableIntegral
          (G.natSample X) (G.natSample X) N omega :=
        congrArg (fun z : Real => 2 * z)
          (congrFun (G.martingaleIntegralProcess_last X X) omega)
      _ = ((2 : Real) • discretePredictableIntegral
          (G.natSample X) (G.natSample X) N) omega := by
        rfl
  rw [hTerminal]
  exact hDiscrete.const_smul 2

omit [MeasurableSpace Omega] in
/-- Every martingale approximation has right-continuous paths. -/
theorem martingalePart_rightContinuous
    (M : Process Omega)
    (hMRight : ∀ omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) (n : Nat) :
    ∀ omega t, ContinuousWithinAt
      (martingalePart M T n · omega) (Ici t) t := by
  exact (grid T n).two_smul_martingaleIntegralProcess_rightContinuous
    (deterministicallyStoppedProcess M T) (stoppedSource_rightContinuous M hMRight T)

omit [MeasurableSpace Omega] in
/-- Every martingale approximation is constant after the deterministic
horizon. -/
theorem martingalePart_constantAfter
    (M : Process Omega) (T : NNReal) (n : Nat) {t : NNReal}
    (ht : T <= t) :
    martingalePart M T n t = martingalePart M T n T := by
  unfold martingalePart
  change 2 * (grid T n).martingaleIntegralProcess
      (deterministicallyStoppedProcess M T) (deterministicallyStoppedProcess M T) t =
    2 * (grid T n).martingaleIntegralProcess
      (deterministicallyStoppedProcess M T) (deterministicallyStoppedProcess M T) T
  congr 1
  rw [(grid T n).martingaleIntegralProcess_eq_last_of_le
    (deterministicallyStoppedProcess M T) (deterministicallyStoppedProcess M T)]
  · rw [grid_sampledTime_last]
  · simpa only [grid_sampledTime_last] using ht

omit [MeasurableSpace Omega] in
/-- Every squared-increment approximation is constant after the deterministic
horizon. -/
theorem squaredIncrementPart_constantAfter
    (M : Process Omega) (T : NNReal) (n : Nat) {t : NNReal}
    (ht : T <= t) :
    squaredIncrementPart M T n t = squaredIncrementPart M T n T := by
  funext omega
  have htIdentity := martingalePart_add_squaredIncrementPart M T t n omega
  have hTIdentity := martingalePart_add_squaredIncrementPart M T T n omega
  have hN := congrFun (martingalePart_constantAfter M T n ht) omega
  have hX : deterministicallyStoppedProcess M T t omega
    = deterministicallyStoppedProcess M T T omega := by
    simp only [deterministicallyStoppedProcess_apply, min_eq_right ht, min_self]
  rw [hN, hX] at htIdentity
  linarith

end BoundedMartingaleQuadraticApproximation

end FTAPTheorem42
