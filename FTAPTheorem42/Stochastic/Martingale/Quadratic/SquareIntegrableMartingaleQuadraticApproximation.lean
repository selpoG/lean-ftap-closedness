/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Quadratic.BoundedMartingaleQuadraticApproximation
import FTAPTheorem42.Stochastic.Martingale.Quadratic.DiscreteMartingaleSquaredIncrement
import FTAPTheorem42.Stochastic.Martingale.Basic.SquareIntegrableFiniteGridMartingaleProcess

/-!
# Quadratic approximations of finite-horizon `M²` martingales

The factorial-grid square decomposition does not require a pathwise bound on
its source.  For a true martingale whose terminal value at the fixed horizon
belongs to `L²`, every left-endpoint coefficient and every stopped increment
belongs to `L²`.  Their products are therefore integrable, so the martingale
part of each quadratic approximation is a true `L¹` martingale.

The exact square decomposition then gives integrability and a uniform first
moment estimate for the nonnegative squared-increment part.  These are the
data-level estimates needed to extend the quadratic-energy construction from
bounded martingales to general finite-horizon `M²` martingales.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace SquareIntegrableMartingaleQuadraticApproximation

open BoundedMartingaleQuadraticApproximation

/-- The martingale part of every factorial-grid square decomposition is a
true martingale under the terminal `L²` assumption alone. -/
theorem martingalePart_isMartingale
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    [SigmaFiniteFiltration mu F]
    {M : Process Omega} (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu)
    (n : Nat) :
    Martingale (martingalePart M T n) F mu := by
  let X := deterministicallyStoppedProcess M T
  have hX : Martingale X F mu := martingale_deterministicallyStopped hM hMRight T
  have hXRight : forall omega t,
      ContinuousWithinAt (X · omega) (Ici t) t :=
    stoppedSource_rightContinuous M hMRight T
  have hXLp : forall t, MemLp (X t) (2 : ENNReal) mu := by
    intro t
    exact stoppedProcess_const_memLp_two hM T hMT t
  have hIntegral :=
    (grid T n).martingaleIntegralProcess_isMartingale_of_memLp_two
      hX hXRight hXLp hX.stronglyAdapted hXLp
  exact Martingale.smul 2 hIntegral

/-- The terminal quadratic martingale approximation is integrable. -/
theorem martingalePart_terminal_integrable
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    [SigmaFiniteFiltration mu F]
    {M : Process Omega} (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu)
    (n : Nat) :
    Integrable (martingalePart M T n T) mu :=
  (martingalePart_isMartingale hM hMRight T hMT n).integrable T

/-- The terminal squared-increment approximation is integrable under the
terminal `L²` assumption alone. -/
theorem squaredIncrementPart_terminal_integrable
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    [SigmaFiniteFiltration mu F]
    {M : Process Omega} (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu)
    (n : Nat) :
    Integrable (squaredIncrementPart M T n T) mu := by
  have hXT : MemLp (deterministicallyStoppedProcess M T T) (2 : ENNReal) mu :=
    stoppedProcess_const_memLp_two hM T hMT T
  have hXZero : MemLp (deterministicallyStoppedProcess M T 0) (2 : ENNReal) mu :=
    stoppedProcess_const_memLp_two hM T hMT 0
  have hSquareDiff : Integrable (fun omega =>
      deterministicallyStoppedProcess M T T omega ^ 2 -
        deterministicallyStoppedProcess M T 0 omega ^ 2) mu :=
    hXT.integrable_sq.sub hXZero.integrable_sq
  have hNIntegrable : Integrable (martingalePart M T n T) mu :=
    martingalePart_terminal_integrable hM hMRight T hMT n
  have hEq : squaredIncrementPart M T n T = fun omega =>
      (deterministicallyStoppedProcess M T T omega ^ 2 -
        deterministicallyStoppedProcess M T 0 omega ^ 2) -
          martingalePart M T n T omega := by
    funext omega
    have hIdentity :=
      martingalePart_add_squaredIncrementPart M T T n omega
    linarith
  rw [hEq]
  exact hSquareDiff.sub hNIntegrable

omit [MeasurableSpace Omega] in
/-- At the horizon, the quadratic approximation is the ordinary discrete
squared-increment sum on its factorial grid. -/
theorem squaredIncrementPart_terminal_eq_discreteSquaredIncrementSum
    (M : Process Omega) (T : NNReal) (n : Nat) :
    squaredIncrementPart M T n T =
      discreteSquaredIncrementSum
        ((grid T n).natSample (deterministicallyStoppedProcess M T))
        ((level T n) * (level T n).factorial) := by
  let G := grid T n
  let X := deterministicallyStoppedProcess M T
  let N := (level T n) * (level T n).factorial
  funext omega
  have hLast : G.sampledTime N = T := by
    simpa only [G, N] using grid_sampledTime_last T n
  calc
    squaredIncrementPart M T n T omega =
        G.squaredIncrementProcess X (G.sampledTime N) omega := by
      exact congrArg (fun t => G.squaredIncrementProcess X t omega) hLast.symm
    _ = ∑ k ∈ Finset.range N,
        (X (G.sampledTime (k + 1)) omega -
          X (G.sampledTime k) omega) ^ 2 :=
      G.squaredIncrementProcess_sampledTime_eq_prefixSum X le_rfl omega
    _ = discreteSquaredIncrementSum (G.natSample X) N omega := rfl

/-- The common expectation of the terminal quadratic sums is the centered
terminal variance.  This makes the energy identity invariant under constant
shifts of the martingale. -/
theorem integral_squaredIncrementPart_terminal_eq_centeredVariance
    {mu : Measure Omega} [IsFiniteMeasure mu]
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    [SigmaFiniteFiltration mu F]
    {M : Process Omega} (hM : Martingale M F mu)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) (hMT : MemLp (M T) (2 : ENNReal) mu)
    (n : Nat) :
    (∫ omega, squaredIncrementPart M T n T omega ∂mu) =
      ∫ omega, (M T omega - M 0 omega) ^ 2 ∂mu := by
  let G := grid T n
  let X := deterministicallyStoppedProcess M T
  let N := (level T n) * (level T n).factorial
  have hX : Martingale X F mu := martingale_deterministicallyStopped hM hMRight T
  have hXSample : Martingale (G.natSample X) (G.sampledFiltration F) mu :=
    ChronologicalGrid.Martingale.natSample (G := G) hX
  have hXLp : forall k,
      MemLp (G.natSample X k) (2 : ENNReal) mu := by
    intro k
    exact stoppedProcess_const_memLp_two hM T hMT (G.sampledTime k)
  rw [squaredIncrementPart_terminal_eq_discreteSquaredIncrementSum]
  rw [DiscreteMartingaleSquaredIncrement.integral_eq_terminalIncrement_sq
    hXSample hXLp N]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun omega => by
    have hLast : G.sampledTime N = T := by
      simpa only [G, N] using grid_sampledTime_last T n
    have hZero : G.sampledTime 0 = 0 := by
      simpa only [G] using grid_sampledTime_zero T n
    simp only [ChronologicalGrid.natSample, X, deterministicallyStoppedProcess_apply,
      hLast, hZero, min_self]
    rw [show min (0 : NNReal) T = 0 from min_eq_left bot_le]

end SquareIntegrableMartingaleQuadraticApproximation

end FTAPTheorem42
