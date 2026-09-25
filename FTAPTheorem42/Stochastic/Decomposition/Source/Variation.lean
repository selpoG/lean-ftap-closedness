/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Decomposition.FiniteGrid.DoobVariationTightness
import FTAPTheorem42.Foundations.FactorialChronologicalGrid

/-!
# Predictable Doob variation on fixed-horizon factorial grids

For a fixed horizon `T`, the level-`r` grid uses factorial mesh `1 / r!`
and clamps all points after `T` to `T`.  Its terminal time is therefore
exactly `T`, allowing the grid-uniform variation estimate to be applied at
every level.  The resulting sequence of terminal predictable variations is
bounded in probability.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace HorizonFactorialGrid

/-- Number of increments in the level-`r` fixed-horizon factorial grid. -/
noncomputable def size (T : NNReal) (r : Nat) : Nat :=
  Nat.ceil T * r.factorial

/-- The factorial grid clamped at a fixed terminal horizon. -/
noncomputable def grid (T : NNReal) (r : Nat) :
    ChronologicalGrid NNReal (size T r) where
  time k := min ((k : NNReal) / (r.factorial : NNReal)) T
  monotone_time := by
    intro k l hkl
    apply min_le_min
    · exact div_le_div_of_nonneg_right (by exact_mod_cast hkl) (by positivity)
    · exact le_rfl

@[simp]
theorem grid_time (T : NNReal) (r : Nat)
    (k : Fin (size T r + 1)) :
    (grid T r).time k =
      min ((k : NNReal) / (r.factorial : NNReal)) T :=
  rfl

/-- The final point of every fixed-horizon factorial grid is exactly the
horizon. -/
@[simp]
theorem sampledTime_size (T : NNReal) (r : Nat) :
    (grid T r).sampledTime (size T r) = T := by
  rw [ChronologicalGrid.sampledTime, ChronologicalGrid.natIndex_last]
  change min (((size T r : Nat) : NNReal) / (r.factorial : NNReal)) T = T
  rw [min_eq_right]
  unfold size
  rw [Nat.cast_mul, mul_div_cancel_right₀]
  · exact_mod_cast Nat.le_ceil T
  · positivity

/-- Every sampled point is at or before the fixed horizon. -/
theorem sampledTime_le_horizon {T : NNReal}
    (r i : Nat) : (grid T r).sampledTime i ≤ T := by
  unfold ChronologicalGrid.sampledTime
  rw [grid_time]
  exact min_le_right _ _

/-- The constantly extended grid stays at the horizon after its last index. -/
theorem sampledTime_eq_terminal_of_le {T : NNReal}
    (r i : Nat) (hi : size T r ≤ i) :
    (grid T r).sampledTime i = T := by
  have hLower : T ≤ (grid T r).sampledTime i := by
    have hmono := (grid T r).sampledTime_mono hi
    rw [sampledTime_size] at hmono
    exact hmono
  exact le_antisymm (sampledTime_le_horizon r i) hLower

/-- Every time in a fixed-horizon factorial grid also occurs at the next
level. -/
theorem range_grid_subset_succ (T : NNReal) (r : Nat) :
    Set.range (grid T r).time ⊆ Set.range (grid T (r + 1)).time := by
  rintro _ ⟨k, rfl⟩
  have hkLe : k.1 ≤ size T r := Nat.le_of_lt_succ k.2
  have hIndexLe : (r + 1) * k.1 ≤ size T (r + 1) := by
    calc
      (r + 1) * k.1 ≤ (r + 1) * size T r :=
        Nat.mul_le_mul_left (r + 1) hkLe
      _ = size T (r + 1) := by
        simp only [size, Nat.factorial_succ]
        ac_rfl
  let l : Fin (size T (r + 1) + 1) :=
    ⟨(r + 1) * k.1, Nat.lt_succ_of_le hIndexLe⟩
  refine ⟨l, ?_⟩
  change min
      ((((r + 1) * k.1 : Nat) : NNReal) /
        (((r + 1).factorial : Nat) : NNReal)) T =
    min ((k.1 : NNReal) / (r.factorial : NNReal)) T
  congr 1
  simp only [Nat.cast_mul, Nat.factorial_succ]
  rw [mul_div_mul_left]
  positivity

/-- Fixed-horizon factorial-grid ranges are nested. -/
theorem range_grid_mono (T : NNReal) :
    Monotone (fun r => Set.range (grid T r).time) :=
  monotone_nat_of_le_succ (range_grid_subset_succ T)

/-- The factorial right approximation of `t ≤ T` is represented on the
fixed-horizon grid after clamping at `T`. -/
noncomputable def approxIndex
    (T t : NNReal) (ht : t ≤ T) (r : Nat) :
    Fin (size T r + 1) :=
  ⟨Nat.ceil (t * (r.factorial : NNReal)), Nat.lt_succ_of_le (by
    unfold size
    apply Nat.ceil_le.mpr
    have hTCeil : T ≤ (Nat.ceil T : NNReal) := Nat.le_ceil T
    simpa only [Nat.cast_mul, Nat.cast_factorial] using
      mul_le_mul_of_nonneg_right (ht.trans hTCeil) (by positivity))⟩

@[simp]
theorem grid_time_approxIndex
    (T t : NNReal) (ht : t ≤ T) (r : Nat) :
    (grid T r).time (approxIndex T t ht r) =
      min (FactorialChronologicalGrid.approx r t) T :=
  rfl

/-- Fixed-horizon factorial approximations converge to every time in the
horizon. -/
theorem tendsto_grid_time_approxIndex
    (T t : NNReal) (ht : t ≤ T) :
    Tendsto (fun r => (grid T r).time (approxIndex T t ht r))
      Filter.atTop (nhds t) := by
  simp only [grid_time_approxIndex]
  simpa [min_eq_left ht] using
    (FactorialChronologicalGrid.tendsto_approx t).min
      (tendsto_const_nhds : Tendsto (fun _ : Nat => T) atTop (nhds T))

/-- If the target already occurs on a fixed-horizon factorial grid, its right
approximation on that grid is exactly the target. -/
theorem grid_time_approxIndex_eq_of_mem_range
    (T t : NNReal) (ht : t ≤ T) (r : Nat)
    (hmem : t ∈ Set.range (grid T r).time) :
    (grid T r).time (approxIndex T t ht r) = t := by
  obtain ⟨k, rfl⟩ := hmem
  rw [grid_time_approxIndex]
  change min (FactorialChronologicalGrid.approx r
      (min ((k.1 : NNReal) / (r.factorial : NNReal)) T)) T =
    min ((k.1 : NNReal) / (r.factorial : NNReal)) T
  by_cases hk :
      ((k.1 : NNReal) / (r.factorial : NNReal)) ≤ T
  · rw [min_eq_left hk]
    have hApprox : FactorialChronologicalGrid.approx r
        ((k.1 : NNReal) / (r.factorial : NNReal)) =
        (k.1 : NNReal) / (r.factorial : NNReal) := by
      unfold FactorialChronologicalGrid.approx
      have hFactorial : (r.factorial : NNReal) ≠ 0 := by positivity
      rw [div_mul_cancel₀ _ hFactorial, Nat.ceil_natCast]
    rw [hApprox, min_eq_left hk]
  · have hTk : T ≤ (k.1 : NNReal) / (r.factorial : NNReal) :=
      le_of_not_ge hk
    rw [min_eq_right hTk]
    exact min_eq_right (FactorialChronologicalGrid.le_approx r T)

/-- Terminal predictable variation on the level-`r` fixed-horizon grid. -/
noncomputable def terminalDoobVariation
    (T : NNReal) (r : Nat)
    (S : Process Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (mu : Measure Omega) : Omega → Real :=
  (grid T r).doobPredictableVariation S F mu (size T r)

/-- The sequence of terminal predictable variations on fixed-horizon
factorial grids is bounded in probability. -/
theorem boundedInProbability_terminalDoobVariation
    {S : Process Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (hS : IsSemimartingale S F mu)
    (source : BoundedSemimartingaleSource S F mu) (T : NNReal) :
    BoundedInProbability mu
      (fun r => terminalDoobVariation T r S F mu) := by
  intro epsilon hepsilon
  obtain ⟨R, hR, hTail⟩ :=
    hS.uniformly_boundedInProbability_doobPredictableVariations
      source T epsilon hepsilon
  refine ⟨R, hR, ?_⟩
  intro r
  exact hTail (grid T r) (sampledTime_size T r)

end HorizonFactorialGrid

end FTAPTheorem42
