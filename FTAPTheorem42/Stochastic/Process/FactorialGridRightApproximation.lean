/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Regularization.ConditionalExpectationL2RightContinuous
import FTAPTheorem42.Stochastic.Martingale.Regularization.MartingaleFactorialGridRightLimit

/-!
# A strict right approximation inside the factorial grids

We first move strictly to the right by the canonical positive gap, clamp at
the horizon, and then round upward on the factorial mesh of the same level.
For a preterminal time this stays strictly to the right, belongs to the union
of the grids, and converges to the original time.
-/

open Filter Set Topology
open scoped NNReal

namespace FTAPTheorem42

namespace HorizonFactorialGrid

/-- The pre-grid target used for strict right approximation. -/
noncomputable def factorialGridRightTarget
    (T t : NNReal) (n : Nat) : NNReal :=
  min (condExpRightApproxTime t n) T

theorem factorialGridRightTarget_le (T t : NNReal) (n : Nat) :
    factorialGridRightTarget T t n ≤ T := by
  unfold factorialGridRightTarget
  exact min_le_right _ _

/-- A strict right approximation represented on the level-`n` fixed-horizon
factorial grid. -/
noncomputable def factorialGridRightApproxTime
  (T t : NNReal) (n : Nat) : NNReal :=
  (grid T n).time
    (approxIndex T (factorialGridRightTarget T t n)
      (factorialGridRightTarget_le T t n) n)

theorem lt_factorialGridRightTarget
    {T t : NNReal} (ht : t < T) (n : Nat) :
    t < factorialGridRightTarget T t n := by
  apply lt_min
  · unfold condExpRightApproxTime
    exact lt_add_of_pos_right t
      (PredictableIntervalAlgebra.rightApproxZero_pos n)
  · exact ht

theorem factorialGridRightTarget_le_factorialGridRightApproxTime
    (T t : NNReal) (n : Nat) :
    factorialGridRightTarget T t n ≤ factorialGridRightApproxTime T t n := by
  rw [factorialGridRightApproxTime, grid_time_approxIndex]
  exact le_min
    (FactorialChronologicalGrid.le_approx n _)
    (min_le_right _ _)

theorem lt_factorialGridRightApproxTime
    {T t : NNReal} (ht : t < T) (n : Nat) :
    t < factorialGridRightApproxTime T t n :=
  (lt_factorialGridRightTarget ht n).trans_le
    (factorialGridRightTarget_le_factorialGridRightApproxTime T t n)

theorem factorialGridRightApproxTime_mem
    (T t : NNReal) (n : Nat) :
    factorialGridRightApproxTime T t n ∈ factorialGridTimes T := by
  exact mem_factorialGridTimes_iff.2 ⟨n, ⟨_, rfl⟩⟩

theorem tendsto_factorialGridRightTarget (T t : NNReal) (ht : t ≤ T) :
    Tendsto (factorialGridRightTarget T t) atTop (nhds t) := by
  unfold factorialGridRightTarget
  simpa [min_eq_left ht] using
    (tendsto_condExpRightApproxTime t).min
      (tendsto_const_nhds : Tendsto (fun _ : Nat => T) atTop (nhds T))

theorem tendsto_inv_factorial_nnreal :
    Tendsto (fun n : Nat => (n.factorial : NNReal)⁻¹) atTop (nhds 0) := by
  exact tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop.comp factorial_tendsto_atTop)

theorem tendsto_factorialGridRightApproxTime
    (T t : NNReal) (ht : t ≤ T) :
    Tendsto (factorialGridRightApproxTime T t) atTop (nhds t) := by
  have hLower := tendsto_factorialGridRightTarget T t ht
  have hUpper : Tendsto (fun n =>
      factorialGridRightTarget T t n + (n.factorial : NNReal)⁻¹)
      atTop (nhds t) := by
    simpa only [add_zero] using hLower.add tendsto_inv_factorial_nnreal
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hLower hUpper
  · exact Filter.Eventually.of_forall fun n =>
      factorialGridRightTarget_le_factorialGridRightApproxTime T t n
  · refine Filter.Eventually.of_forall fun n => ?_
    rw [factorialGridRightApproxTime, grid_time_approxIndex]
    exact (min_le_left _ _).trans
      (FactorialChronologicalGrid.approx_le_add_inv_factorial n _)

end HorizonFactorialGrid

end FTAPTheorem42
