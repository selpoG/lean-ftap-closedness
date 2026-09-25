/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.Elementary.PredictableElementaryLeftStepMartingaleApproximation
import FTAPTheorem42.Stochastic.Martingale.Quadratic.SquareIntegrableMartingaleQuadraticApproximation
import FTAPTheorem42.Stochastic.Martingale.Basic.UniformL2MartingaleLimit
import Mathlib.Probability.StrongLaw

/-!
# Uniform integrability of `M^2` quadratic grid sums

Let `M` be a true square-integrable martingale on a deterministic finite
horizon.  The terminal sums of squared increments along the factorial grids
have a common first moment, but that fact alone does not prevent loss of mass
under forward-convex almost-everywhere limits.

This file proves the missing uniform integrability.  The centered terminal
value is split into a bounded truncation and an `L^2`-small residual.  Only
their conditional expectations at the finite grid times are used.  The
bounded component has a grid-independent `L^2` bound for its quadratic sum;
the residual component has uniformly small `L^1` energy by the discrete
martingale isometry.  Their incrementwise square inequality controls the
original quadratic sum.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace SquareIntegrableMartingaleQuadraticUniformIntegrability

open BoundedMartingaleQuadraticApproximation
open SquareIntegrableMartingaleQuadraticApproximation

/-- The centered terminal value on the fixed horizon. -/
noncomputable def centeredTerminal
    (M : Process Omega) (T : NNReal) : Omega -> Real :=
  M T - M 0

/-- The bounded terminal cutoff at the natural level `K`. -/
noncomputable def terminalCutoff
    (M : Process Omega) (T : NNReal) (K : Nat) : Omega -> Real :=
  truncation (centeredTerminal M T) K

/-- The terminal residual left after the bounded cutoff. -/
noncomputable def terminalResidual
    (M : Process Omega) (T : NNReal) (K : Nat) : Omega -> Real :=
  centeredTerminal M T - terminalCutoff M T K

/-- The centered terminal variable belongs to `L^2`. -/
theorem centeredTerminal_memLp_two
    {mu : Measure Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {M : Process Omega} (hM : Martingale M F mu)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu) :
    MemLp (centeredTerminal M T) (2 : ENNReal) mu := by
  exact hMT.sub
    (MartingaleL2Terminal.Martingale.memLp_two_of_le_and_eLpNorm_le
      hM (show (0 : NNReal) <= T from bot_le) hMT).1

/-- Every terminal cutoff belongs to `L^2`. -/
theorem terminalCutoff_memLp_two
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {M : Process Omega} (hM : Martingale M F mu)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu) (K : Nat) :
    MemLp (terminalCutoff M T K) (2 : ENNReal) mu := by
  exact (centeredTerminal_memLp_two hM T hMT).aestronglyMeasurable
    |>.memLp_truncation

/-- Every terminal residual belongs to `L^2`. -/
theorem terminalResidual_memLp_two
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {M : Process Omega} (hM : Martingale M F mu)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu) (K : Nat) :
    MemLp (terminalResidual M T K) (2 : ENNReal) mu := by
  exact (centeredTerminal_memLp_two hM T hMT).sub
    (terminalCutoff_memLp_two hM T hMT K)

omit [MeasurableSpace Omega] in
/-- The cutoff error is dominated by twice the centered terminal size. -/
theorem norm_terminalCutoff_sub_centeredTerminal_le
    (M : Process Omega) (T : NNReal) (K : Nat) (omega : Omega) :
    ‖terminalCutoff M T K omega - centeredTerminal M T omega‖ <=
      ‖(2 : Real) * centeredTerminal M T omega‖ := by
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by norm_num : (0 : Real) <= 2)]
  calc
    |terminalCutoff M T K omega - centeredTerminal M T omega| <=
        |terminalCutoff M T K omega| +
          |centeredTerminal M T omega| := abs_sub _ _
    _ <= |centeredTerminal M T omega| +
        |centeredTerminal M T omega| :=
      add_le_add (by
        simpa only [terminalCutoff] using
          abs_truncation_le_abs_self (centeredTerminal M T) K omega) le_rfl
    _ = 2 * |centeredTerminal M T omega| := by ring

omit [MeasurableSpace Omega] in
/-- Terminal cutoffs converge pointwise to the centered terminal value. -/
theorem terminalCutoff_tendsto
    (M : Process Omega) (T : NNReal) (omega : Omega) :
    Tendsto (fun K => terminalCutoff M T K omega) atTop
      (nhds (centeredTerminal M T omega)) := by
  apply tendsto_atTop_of_eventually_const
    (i₀ := Nat.ceil |centeredTerminal M T omega| + 1)
  intro K hK
  apply truncation_eq_self
  calc
    |centeredTerminal M T omega| <=
        Nat.ceil |centeredTerminal M T omega| := Nat.le_ceil _
    _ < Nat.ceil |centeredTerminal M T omega| + 1 := by linarith
    _ <= K := by exact_mod_cast hK

/-- The cutoff residual vanishes in `L^2`. -/
theorem terminalResidual_tendsto_eLpNorm_two
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {M : Process Omega} (hM : Martingale M F mu)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu) :
    Tendsto (fun K => eLpNorm (terminalResidual M T K)
      (2 : ENNReal) mu) atTop (nhds 0) := by
  have hCentered := centeredTerminal_memLp_two hM T hMT
  have hCutoffMeas : forall K,
      AEStronglyMeasurable (terminalCutoff M T K) mu := by
    intro K
    exact hCentered.aestronglyMeasurable.truncation
  have hBound : MemLp (fun omega =>
      (2 : Real) * centeredTerminal M T omega) (2 : ENNReal) mu :=
    hCentered.const_mul 2
  have hTendsto : ∀ᵐ omega ∂mu,
      Tendsto (fun K => terminalCutoff M T K omega) atTop
        (nhds (centeredTerminal M T omega)) :=
    Filter.Eventually.of_forall (terminalCutoff_tendsto M T)
  have hLimit := tendsto_eLpNorm_two_of_ae_tendsto_of_memLp_bound
    hCutoffMeas hCentered.aestronglyMeasurable hBound
    (fun K => Filter.Eventually.of_forall
      (norm_terminalCutoff_sub_centeredTerminal_le M T K)) hTendsto
  simpa only [terminalResidual, eLpNorm_sub_comm] using hLimit

/-- Conditional expectations of the terminal cutoff on the `n`-th grid. -/
noncomputable def gridCutoffMartingale
    (mu : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (M : Process Omega) (T : NNReal) (K n : Nat) :
    Nat -> Omega -> Real :=
  fun j => mu[terminalCutoff M T K | (grid T n).sampledFiltration F j]

/-- Conditional expectations of the terminal residual on the `n`-th grid. -/
noncomputable def gridResidualMartingale
    (mu : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (M : Process Omega) (T : NNReal) (K n : Nat) :
    Nat -> Omega -> Real :=
  fun j => mu[terminalResidual M T K | (grid T n).sampledFiltration F j]

/-- The cutoff conditional expectations form a discrete martingale. -/
theorem gridCutoffMartingale_isMartingale
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (M : Process Omega) (T : NNReal) (K n : Nat) :
    Martingale (gridCutoffMartingale mu F M T K n)
      ((grid T n).sampledFiltration F) mu := by
  exact martingale_condExp (terminalCutoff M T K)
    ((grid T n).sampledFiltration F) mu

/-- The residual conditional expectations form a discrete martingale. -/
theorem gridResidualMartingale_isMartingale
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (M : Process Omega) (T : NNReal) (K n : Nat) :
    Martingale (gridResidualMartingale mu F M T K n)
      ((grid T n).sampledFiltration F) mu := by
  exact martingale_condExp (terminalResidual M T K)
    ((grid T n).sampledFiltration F) mu

/-- Every coordinate of the cutoff martingale belongs to `L^2`. -/
theorem gridCutoffMartingale_memLp_two
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {M : Process Omega} (hM : Martingale M F mu)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu)
    (K n j : Nat) :
    MemLp (gridCutoffMartingale mu F M T K n j)
      (2 : ENNReal) mu := by
  simpa only [gridCutoffMartingale] using
    (terminalCutoff_memLp_two hM T hMT K).condExp
      (m := (grid T n).sampledFiltration F j) (by norm_num)

/-- Every coordinate of the residual martingale belongs to `L^2`. -/
theorem gridResidualMartingale_memLp_two
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {M : Process Omega} (hM : Martingale M F mu)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu)
    (K n j : Nat) :
    MemLp (gridResidualMartingale mu F M T K n j)
      (2 : ENNReal) mu := by
  simpa only [gridResidualMartingale] using
    (terminalResidual_memLp_two hM T hMT K).condExp
      (m := (grid T n).sampledFiltration F j) (by norm_num)

/-- Conditional expectation preserves the deterministic cutoff bound. -/
theorem gridCutoffMartingale_bound
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (M : Process Omega) (T : NNReal) (K n j : Nat) :
    ∀ᵐ omega ∂mu,
      |gridCutoffMartingale mu F M T K n j omega| <= (K : Real) := by
  have hBound : ∀ᵐ omega ∂mu,
      ‖terminalCutoff M T K omega‖ <= (K : Real) := by
    exact Filter.Eventually.of_forall fun omega => by
      have hKnonneg : (0 : Real) <= (K : Real) := Nat.cast_nonneg K
      simpa only [Real.norm_eq_abs, terminalCutoff,
        abs_of_nonneg hKnonneg] using
        abs_truncation_le_bound (centeredTerminal M T) K omega
  simpa only [gridCutoffMartingale, Real.norm_eq_abs] using
    (ae_bdd_norm_condExp_of_ae_bdd_norm
      (m := (grid T n).sampledFiltration F j) hBound)

/-- Every residual conditional expectation is contracted in `L^2`. -/
theorem gridResidualMartingale_eLpNorm_two_le
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (M : Process Omega) (T : NNReal) (K n j : Nat) :
    eLpNorm (gridResidualMartingale mu F M T K n j)
        (2 : ENNReal) mu <=
      eLpNorm (terminalResidual M T K) (2 : ENNReal) mu := by
  simpa only [gridResidualMartingale] using
    (eLpNorm_condExp_le_eLpNorm
      (m := (grid T n).sampledFiltration F j)
      (terminalResidual M T K) (by norm_num : (1 : ENNReal) <= 2))

/-- On every grid coordinate up to the horizon, the centered stopped source
is the sum of the cutoff and residual conditional-expectation martingales. -/
theorem centeredSource_ae_eq_gridCutoff_add_residual
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    [SigmaFiniteFiltration mu F]
    {M : Process Omega} (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu)
    (K n j : Nat)
    (hj : j <= (level T n) * (level T n).factorial) :
    (fun omega =>
      (grid T n).natSample (deterministicallyStoppedProcess M T) j omega -
        (grid T n).natSample (deterministicallyStoppedProcess M T) 0 omega) =ᵐ[mu]
      gridCutoffMartingale mu F M T K n j +
        gridResidualMartingale mu F M T K n j := by
  let G := grid T n
  let X := G.natSample (deterministicallyStoppedProcess M T)
  let N := (level T n) * (level T n).factorial
  let Fs := G.sampledFiltration F
  have hStopped : Martingale (deterministicallyStoppedProcess M T) F mu :=
    martingale_deterministicallyStopped hM hMRight T
  have hX : Martingale X Fs mu :=
    ChronologicalGrid.Martingale.natSample (G := G) hStopped
  have hXLp : forall k, MemLp (X k) (2 : ENNReal) mu := by
    intro k
    exact stoppedProcess_const_memLp_two hM T hMT (G.sampledTime k)
  have hTerminalEq : centeredTerminal M T = X N - X 0 := by
    funext omega
    have hLast : G.sampledTime N = T := by
      simpa only [G, N] using grid_sampledTime_last T n
    have hZero : G.sampledTime 0 = 0 := by
      simpa only [G] using grid_sampledTime_zero T n
    change M T omega - M 0 omega =
      deterministicallyStoppedProcess M T (G.sampledTime N) omega -
        deterministicallyStoppedProcess M T (G.sampledTime 0) omega
    rw [hLast, hZero, deterministicallyStoppedProcess_apply, deterministicallyStoppedProcess_apply,
      min_self,
      show min (0 : NNReal) T = 0 from min_eq_left bot_le]
  have hCondCentered :
      mu[centeredTerminal M T | Fs j] =ᵐ[mu] X j - X 0 := by
    rw [hTerminalEq]
    have hSub := condExp_sub ((hXLp N).integrable (by norm_num))
      ((hXLp 0).integrable (by norm_num)) (Fs j)
    have hTerminal := hX.condExp_ae_eq (show j <= N from hj)
    have hZeroStrong : StronglyMeasurable[Fs j] (X 0) :=
      (hX.stronglyMeasurable 0).mono (Fs.mono (Nat.zero_le j))
    have hZero : mu[X 0 | Fs j] = X 0 :=
      condExp_of_stronglyMeasurable (Fs.le j) hZeroStrong
        ((hXLp 0).integrable (by norm_num))
    filter_upwards [hSub, hTerminal] with omega hSubOmega hTerminalOmega
    rw [hSubOmega]
    change mu[X N | Fs j] omega - mu[X 0 | Fs j] omega =
      X j omega - X 0 omega
    rw [hTerminalOmega, hZero]
  have hDecomp : centeredTerminal M T =
      terminalCutoff M T K + terminalResidual M T K := by
    funext omega
    simp only [terminalResidual, Pi.add_apply, Pi.sub_apply]
    ring
  have hCondSplit :
      mu[centeredTerminal M T | Fs j] =ᵐ[mu]
        gridCutoffMartingale mu F M T K n j +
          gridResidualMartingale mu F M T K n j := by
    rw [hDecomp]
    simpa only [gridCutoffMartingale, gridResidualMartingale, G, Fs] using
      condExp_add ((terminalCutoff_memLp_two hM T hMT K).integrable (by norm_num))
        ((terminalResidual_memLp_two hM T hMT K).integrable (by norm_num)) (Fs j)
  change (fun omega => X j omega - X 0 omega) =ᵐ[mu] _
  exact hCondCentered.symm.trans hCondSplit

/-- The cutoff component's squared-increment sum on the `n`-th grid. -/
noncomputable def gridCutoffSquaredIncrementSum
    (mu : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (M : Process Omega) (T : NNReal) (K n : Nat) : Omega -> Real :=
  discreteSquaredIncrementSum (gridCutoffMartingale mu F M T K n)
    ((level T n) * (level T n).factorial)

/-- The residual component's squared-increment sum on the `n`-th grid. -/
noncomputable def gridResidualSquaredIncrementSum
    (mu : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (M : Process Omega) (T : NNReal) (K n : Nat) : Omega -> Real :=
  discreteSquaredIncrementSum (gridResidualMartingale mu F M T K n)
    ((level T n) * (level T n).factorial)

/-- The original terminal quadratic sum is bounded by twice the cutoff
energy plus twice the residual energy. -/
theorem squaredIncrementPart_terminal_ae_le_cutoff_add_residual
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    [SigmaFiniteFiltration mu F]
    {M : Process Omega} (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu)
    (K n : Nat) :
    squaredIncrementPart M T n T ≤ᵐ[mu]
      fun omega =>
        2 * gridCutoffSquaredIncrementSum mu F M T K n omega +
          2 * gridResidualSquaredIncrementSum mu F M T K n omega := by
  let G := grid T n
  let X := G.natSample (deterministicallyStoppedProcess M T)
  let B := gridCutoffMartingale mu F M T K n
  let R := gridResidualMartingale mu F M T K n
  let N := (level T n) * (level T n).factorial
  have hAll : ∀ᵐ omega ∂mu, forall j, j <= N ->
      X j omega - X 0 omega = B j omega + R j omega := by
    rw [ae_all_iff]
    intro j
    by_cases hj : j <= N
    · filter_upwards [centeredSource_ae_eq_gridCutoff_add_residual
          hM hMRight T hMT K n j hj] with omega homega
      exact fun _ => homega
    · exact Filter.Eventually.of_forall fun _ hj' => (hj hj').elim
  filter_upwards [hAll] with omega homega
  rw [squaredIncrementPart_terminal_eq_discreteSquaredIncrementSum]
  change discreteSquaredIncrementSum X N omega <=
    2 * discreteSquaredIncrementSum B N omega +
      2 * discreteSquaredIncrementSum R N omega
  unfold discreteSquaredIncrementSum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k hk
  have hklt : k < N := Finset.mem_range.mp hk
  have hkEq := homega k hklt.le
  have hksEq := homega (k + 1) (Nat.succ_le_iff.mpr hklt)
  change (X (k + 1) omega - X k omega) ^ 2 <=
    2 * (B (k + 1) omega - B k omega) ^ 2 +
      2 * (R (k + 1) omega - R k omega) ^ 2
  have hIncrement : X (k + 1) omega - X k omega =
      (B (k + 1) omega - B k omega) +
        (R (k + 1) omega - R k omega) := by
    linarith [hkEq, hksEq]
  rw [hIncrement]
  nlinarith [sq_nonneg
    ((B (k + 1) omega - B k omega) -
      (R (k + 1) omega - R k omega))]

/-- For a fixed cutoff, every cutoff energy belongs to `L^2`. -/
theorem gridCutoffSquaredIncrementSum_memLp_two
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {M : Process Omega} (hM : Martingale M F mu)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu)
    (K n : Nat) :
    MemLp (gridCutoffSquaredIncrementSum mu F M T K n)
      (2 : ENNReal) mu := by
  exact DiscreteMartingaleSquaredIncrement.memLp_two_of_bounded
    (gridCutoffMartingale_isMartingale M T K n)
    (fun j => gridCutoffMartingale_memLp_two hM T hMT K n j)
    (gridCutoffMartingale_bound M T K n)
    ((level T n) * (level T n).factorial)

/-- For a fixed cutoff, the cutoff energies have a grid-independent `L^2`
bound. -/
theorem gridCutoffSquaredIncrementSum_eLpNorm_two_le
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {M : Process Omega} (hM : Martingale M F mu)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu)
    (K n : Nat) :
    eLpNorm (gridCutoffSquaredIncrementSum mu F M T K n)
        (2 : ENNReal) mu <=
      ENNReal.ofReal (6 * (K : Real) ^ 2) := by
  exact DiscreteMartingaleSquaredIncrement.eLpNorm_two_le_of_bounded
    (gridCutoffMartingale_isMartingale M T K n)
    (fun j => gridCutoffMartingale_memLp_two hM T hMT K n j)
    (Nat.cast_nonneg K)
    (gridCutoffMartingale_bound M T K n)
    ((level T n) * (level T n).factorial)

/-- For each fixed terminal cutoff, the cutoff energies are uniformly
integrable in `L^1`, uniformly over all factorial grids. -/
theorem gridCutoffSquaredIncrementSum_uniformIntegrable
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {M : Process Omega} (hM : Martingale M F mu)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu)
    (K : Nat) :
    UniformIntegrable
      (fun n => gridCutoffSquaredIncrementSum mu F M T K n) 1 mu := by
  let C : NNReal := ⟨6 * (K : Real) ^ 2, by positivity⟩
  apply uniformIntegrable_one_of_eLpNorm_two_le
    (fun n => gridCutoffSquaredIncrementSum mu F M T K n) C
  · exact fun n => gridCutoffSquaredIncrementSum_memLp_two hM T hMT K n
  · intro n
    rw [← ENNReal.ofReal_coe_nnreal]
    change eLpNorm (gridCutoffSquaredIncrementSum mu F M T K n)
        (2 : ENNReal) mu <= ENNReal.ofReal (6 * (K : Real) ^ 2)
    exact gridCutoffSquaredIncrementSum_eLpNorm_two_le hM T hMT K n

/-- The residual energy has a first norm bounded uniformly over all grids by
four times the squared `L^2` cutoff error. -/
theorem gridResidualSquaredIncrementSum_eLpNorm_one_le
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {M : Process Omega} (hM : Martingale M F mu)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu)
    (K n : Nat) :
    eLpNorm (gridResidualSquaredIncrementSum mu F M T K n) 1 mu <=
      4 * eLpNorm (terminalResidual M T K) (2 : ENNReal) mu ^ 2 := by
  let R := gridResidualMartingale mu F M T K n
  let N := (level T n) * (level T n).factorial
  have hRLp : forall j, MemLp (R j) (2 : ENNReal) mu :=
    fun j => gridResidualMartingale_memLp_two hM T hMT K n j
  have hDifference : eLpNorm (R N - R 0) (2 : ENNReal) mu <=
      2 * eLpNorm (terminalResidual M T K) (2 : ENNReal) mu := by
    calc
      eLpNorm (R N - R 0) (2 : ENNReal) mu <=
          eLpNorm (R N) (2 : ENNReal) mu +
            eLpNorm (R 0) (2 : ENNReal) mu :=
        eLpNorm_sub_le (by norm_num)
      _ <= eLpNorm (terminalResidual M T K) (2 : ENNReal) mu +
          eLpNorm (terminalResidual M T K) (2 : ENNReal) mu :=
        add_le_add
          (gridResidualMartingale_eLpNorm_two_le M T K n N)
          (gridResidualMartingale_eLpNorm_two_le M T K n 0)
      _ = 2 * eLpNorm (terminalResidual M T K) (2 : ENNReal) mu := by
        ring
  rw [gridResidualSquaredIncrementSum,
    DiscreteMartingaleSquaredIncrement.eLpNorm_one_eq_terminalIncrement_two_sq
      (gridResidualMartingale_isMartingale M T K n) hRLp N]
  calc
    eLpNorm (R N - R 0) (2 : ENNReal) mu ^ 2 <=
        (2 * eLpNorm (terminalResidual M T K) (2 : ENNReal) mu) ^ 2 := by
      gcongr
    _ = 4 * eLpNorm (terminalResidual M T K) (2 : ENNReal) mu ^ 2 := by
      ring

/-- The grid-independent residual-energy bound vanishes with the cutoff
level. -/
theorem residualEnergyBound_tendsto_zero
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {M : Process Omega} (hM : Martingale M F mu)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu) :
    Tendsto (fun K =>
      4 * eLpNorm (terminalResidual M T K) (2 : ENNReal) mu ^ 2)
      atTop (nhds 0) := by
  have hResidual := terminalResidual_tendsto_eLpNorm_two hM T hMT
  have hSquare : Tendsto (fun K =>
      eLpNorm (terminalResidual M T K) (2 : ENNReal) mu *
        eLpNorm (terminalResidual M T K) (2 : ENNReal) mu)
      atTop (nhds (0 * 0)) :=
    ENNReal.Tendsto.mul hResidual (Or.inr ENNReal.zero_ne_top)
      hResidual (Or.inr ENNReal.zero_ne_top)
  simpa only [pow_two, mul_zero] using
    ENNReal.Tendsto.const_mul hSquare (Or.inr (by norm_num))

/-- The `L^1` norm of every terminal quadratic sum is exactly the squared
`L^2` norm of the centered terminal martingale value. -/
theorem squaredIncrementPart_terminal_eLpNorm_one_eq_centeredTerminal_two_sq
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    [SigmaFiniteFiltration mu F]
    {M : Process Omega} (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu)
    (n : Nat) :
    eLpNorm (squaredIncrementPart M T n T) 1 mu =
      eLpNorm (centeredTerminal M T) (2 : ENNReal) mu ^ 2 := by
  let G := grid T n
  let X := G.natSample (deterministicallyStoppedProcess M T)
  let N := (level T n) * (level T n).factorial
  have hStopped : Martingale (deterministicallyStoppedProcess M T) F mu :=
    martingale_deterministicallyStopped hM hMRight T
  have hX : Martingale X (G.sampledFiltration F) mu :=
    ChronologicalGrid.Martingale.natSample (G := G) hStopped
  have hXLp : forall j, MemLp (X j) (2 : ENNReal) mu := by
    intro j
    exact stoppedProcess_const_memLp_two hM T hMT (G.sampledTime j)
  have hEndpoint : X N - X 0 = centeredTerminal M T := by
    funext omega
    have hLast : G.sampledTime N = T := by
      simpa only [G, N] using grid_sampledTime_last T n
    have hZero : G.sampledTime 0 = 0 := by
      simpa only [G] using grid_sampledTime_zero T n
    change deterministicallyStoppedProcess M T (G.sampledTime N) omega -
        deterministicallyStoppedProcess M T (G.sampledTime 0) omega =
      M T omega - M 0 omega
    rw [hLast, hZero, deterministicallyStoppedProcess_apply, deterministicallyStoppedProcess_apply,
      min_self,
      show min (0 : NNReal) T = 0 from min_eq_left bot_le]
  calc
    eLpNorm (squaredIncrementPart M T n T) 1 mu =
        eLpNorm (discreteSquaredIncrementSum X N) 1 mu := by
      rw [squaredIncrementPart_terminal_eq_discreteSquaredIncrementSum]
    _ = eLpNorm (X N - X 0) (2 : ENNReal) mu ^ 2 :=
      DiscreteMartingaleSquaredIncrement.eLpNorm_one_eq_terminalIncrement_two_sq
        hX hXLp N
    _ = eLpNorm (centeredTerminal M T) (2 : ENNReal) mu ^ 2 := by
      rw [hEndpoint]

/-- Every residual energy is integrable. -/
theorem gridResidualSquaredIncrementSum_integrable
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {M : Process Omega} (hM : Martingale M F mu)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu)
    (K n : Nat) :
    Integrable (gridResidualSquaredIncrementSum mu F M T K n) mu := by
  exact DiscreteMartingaleSquaredIncrement.integrable
    (fun j => gridResidualMartingale_memLp_two hM T hMT K n j)
    ((level T n) * (level T n).factorial)

/-- On every measurable event, the `L^1` mass of the original quadratic sum
is controlled by the corresponding cutoff and residual masses. -/
theorem eLpNorm_indicator_squaredIncrementPart_terminal_le
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    [SigmaFiniteFiltration mu F]
    {M : Process Omega} (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu)
    (K n : Nat) (s : Set Omega) (hs : MeasurableSet s) :
    eLpNorm (s.indicator (squaredIncrementPart M T n T)) 1 mu <=
      2 * eLpNorm
        (s.indicator (gridCutoffSquaredIncrementSum mu F M T K n)) 1 mu +
      2 * eLpNorm
        (s.indicator (gridResidualSquaredIncrementSum mu F M T K n)) 1 mu := by
  let A := squaredIncrementPart M T n T
  let B := gridCutoffSquaredIncrementSum mu F M T K n
  let R := gridResidualSquaredIncrementSum mu F M T K n
  have hDom : A ≤ᵐ[mu] fun omega => 2 * B omega + 2 * R omega :=
    squaredIncrementPart_terminal_ae_le_cutoff_add_residual
      hM hMRight T hMT K n
  have hBMem : MemLp B (2 : ENNReal) mu :=
    gridCutoffSquaredIncrementSum_memLp_two hM T hMT K n
  have hRInt : Integrable R mu :=
    gridResidualSquaredIncrementSum_integrable hM T hMT K n
  have hMono : eLpNorm (s.indicator A) 1 mu <=
      eLpNorm (s.indicator (fun omega => 2 * B omega + 2 * R omega)) 1 mu := by
    apply eLpNorm_mono_ae
      ((squaredIncrementPart_terminal_integrable hM hMRight T hMT n).aestronglyMeasurable.indicator
        hs)
    filter_upwards [hDom] with omega homega
    by_cases hmem : omega ∈ s
    · simp only [Set.indicator_of_mem hmem, Real.norm_eq_abs]
      rw [abs_of_nonneg (squaredIncrementPart_nonneg M T T n omega),
        abs_of_nonneg]
      · exact homega
      · exact add_nonneg
          (mul_nonneg (by norm_num)
            (discreteSquaredIncrementSum_nonneg
              (gridCutoffMartingale mu F M T K n)
              ((level T n) * (level T n).factorial) omega))
          (mul_nonneg (by norm_num)
            (discreteSquaredIncrementSum_nonneg
              (gridResidualMartingale mu F M T K n)
              ((level T n) * (level T n).factorial) omega))
    · simp only [Set.indicator_of_notMem hmem, norm_zero]
      exact le_rfl
  calc
    eLpNorm (s.indicator A) 1 mu <=
        eLpNorm (s.indicator (fun omega => 2 * B omega + 2 * R omega)) 1 mu :=
      hMono
    _ = eLpNorm
        ((2 : Real) • s.indicator B + (2 : Real) • s.indicator R) 1 mu := by
      congr 1
      funext omega
      by_cases hmem : omega ∈ s
      · simp only [Set.indicator_of_mem hmem, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul]
      · simp only [Set.indicator_of_notMem hmem, Pi.add_apply, Pi.smul_apply,
          smul_zero, add_zero]
    _ <= eLpNorm ((2 : Real) • s.indicator B) 1 mu +
        eLpNorm ((2 : Real) • s.indicator R) 1 mu :=
      eLpNorm_add_le
        (by norm_num)
    _ = 2 * eLpNorm (s.indicator B) 1 mu +
        2 * eLpNorm (s.indicator R) 1 mu := by
      rw [eLpNorm_const_smul, eLpNorm_const_smul]
      norm_num [Real.enorm_eq_ofReal]

/-- Terminal squared-increment sums of a finite-horizon `M^2` martingale are
uniformly integrable.  This is the mass-preservation input for the subsequent
forward-convex quadratic-variation limit. -/
theorem squaredIncrementPart_terminal_uniformIntegrable
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    [SigmaFiniteFiltration mu F]
    {M : Process Omega} (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu) :
    UniformIntegrable
      (fun n => squaredIncrementPart M T n T) 1 mu := by
  refine ⟨unifIntegrable_iff'.2 ?_, ?_⟩
  · intro ε hε
    obtain ⟨epsilon, _, hepsilon, hεbound⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
    have hepsilon : 0 < epsilon := ENNReal.ofReal_pos.1 hepsilon
    have hepsilonEight : 0 < epsilon / 8 := by positivity
    have hResidualEventually : ∀ᶠ K in atTop,
        4 * eLpNorm (terminalResidual M T K) (2 : ENNReal) mu ^ 2 <
          ENNReal.ofReal (epsilon / 8) :=
      (residualEnergyBound_tendsto_zero hM T hMT).eventually
        (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hepsilonEight))
    obtain ⟨K, hK⟩ := hResidualEventually.exists
    have hCutoffUI :=
      (gridCutoffSquaredIncrementSum_uniformIntegrable hM T hMT K).unifIntegrable
    obtain ⟨delta, hdeltaPositive, hdelta⟩ :=
      unifIntegrable_iff'.1 hCutoffUI (ENNReal.ofReal (epsilon / 8))
        (ENNReal.ofReal_pos.2 hepsilonEight)
    refine ⟨delta, hdeltaPositive, fun n s hs hmus => ?_⟩
    apply le_trans ?_ hεbound.le
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict hs]
    have hCutoffSmall : eLpNorm
        (s.indicator (gridCutoffSquaredIncrementSum mu F M T K n)) 1 mu <=
        ENNReal.ofReal (epsilon / 8) :=
      (eLpNorm_indicator_eq_eLpNorm_restrict hs).trans_le (hdelta n s hs hmus)
    have hResidualSmall : eLpNorm
        (s.indicator (gridResidualSquaredIncrementSum mu F M T K n)) 1 mu <=
        ENNReal.ofReal (epsilon / 8) := by
      calc
        eLpNorm
            (s.indicator (gridResidualSquaredIncrementSum mu F M T K n))
            1 mu <=
            eLpNorm (gridResidualSquaredIncrementSum mu F M T K n) 1 mu :=
          eLpNorm_indicator_le _ hs
        _ <= 4 * eLpNorm (terminalResidual M T K) (2 : ENNReal) mu ^ 2 :=
          gridResidualSquaredIncrementSum_eLpNorm_one_le hM T hMT K n
        _ <= ENNReal.ofReal (epsilon / 8) := hK.le
    calc
      eLpNorm (s.indicator (squaredIncrementPart M T n T)) 1 mu <=
          2 * eLpNorm
              (s.indicator (gridCutoffSquaredIncrementSum mu F M T K n)) 1 mu +
            2 * eLpNorm
              (s.indicator (gridResidualSquaredIncrementSum mu F M T K n))
                1 mu :=
        eLpNorm_indicator_squaredIncrementPart_terminal_le
          hM hMRight T hMT K n s hs
      _ <= 2 * ENNReal.ofReal (epsilon / 8) +
          2 * ENNReal.ofReal (epsilon / 8) :=
        by gcongr
      _ = ENNReal.ofReal (epsilon / 2) := by
        rw [← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_mul (by norm_num : (0 : Real) <= 2),
          ← ENNReal.ofReal_add (mul_nonneg (by norm_num) hepsilonEight.le)
            (mul_nonneg (by norm_num) hepsilonEight.le)]
        congr 1
        ring
      _ <= ENNReal.ofReal epsilon :=
        ENNReal.ofReal_le_ofReal (by linarith)
  · let C : NNReal :=
      (eLpNorm (centeredTerminal M T) (2 : ENNReal) mu ^ 2).toNNReal
    refine ⟨C, fun n => ?_⟩
    have hCenteredTop :
        eLpNorm (centeredTerminal M T) (2 : ENNReal) mu ≠ ∞ :=
      (centeredTerminal_memLp_two hM T hMT).eLpNorm_ne_top
    have hSquareTop :
        eLpNorm (centeredTerminal M T) (2 : ENNReal) mu ^ 2 ≠ ∞ :=
      ENNReal.pow_ne_top hCenteredTop
    rw [squaredIncrementPart_terminal_eLpNorm_one_eq_centeredTerminal_two_sq
      hM hMRight T hMT n]
    exact le_of_eq (ENNReal.coe_toNNReal hSquareTop).symm

end SquareIntegrableMartingaleQuadraticUniformIntegrability

end FTAPTheorem42
