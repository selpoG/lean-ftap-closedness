/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Martingale.Quadratic.BoundedMartingaleQuadraticConvexification
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationFactorialApproximation

/-!
# Increasing quadratic-variation limits for bounded martingales

The squared-increment approximations are not increasing between their own
grid points.  They are, however, increasing on each grid range.  Nested
factorial grids and the tail support of the Hilbert convex weights imply
eventual monotonicity on every fixed coarse grid.  Uniform convergence then
passes this order to the right-continuous limit, first on the factorial
skeleton and finally at all times.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace BoundedMartingaleQuadraticVariation

namespace Approximation

open BoundedMartingaleQuadraticApproximation
open BoundedMartingaleQuadraticConvexification

omit [MeasurableSpace Omega] in
/-- A convexified squared-increment approximation is constant after the
common horizon. -/
theorem squaredIncrementPart_constantAfter
    (M : Process Omega) (T : NNReal) {n : Nat}
    (w : TailConvexWeights n) {t : NNReal} (ht : T <= t) :
    BoundedMartingaleQuadraticConvexification.squaredIncrementPart
        M T w t =
      BoundedMartingaleQuadraticConvexification.squaredIncrementPart
        M T w T := by
  funext omega
  rw [BoundedMartingaleQuadraticConvexification.squaredIncrementPart_apply,
    BoundedMartingaleQuadraticConvexification.squaredIncrementPart_apply]
  unfold TailConvexWeights.apply
  apply Finset.sum_congr rfl
  intro i _hi
  change w.weight i *
      BoundedMartingaleQuadraticApproximation.squaredIncrementPart
        M T i t omega =
    w.weight i *
      BoundedMartingaleQuadraticApproximation.squaredIncrementPart
        M T i T omega
  rw [BoundedMartingaleQuadraticApproximation.squaredIncrementPart_constantAfter
    M T i ht]

omit [MeasurableSpace Omega] in
/-- Once a coarse stopped factorial grid is contained in every active tail
grid, the convexified squared-increment approximation is monotone between
two times of that coarse grid. -/
theorem squaredIncrementPart_mono_on_stoppedGrid_range
    (M : Process Omega) (T : NNReal) {n r : Nat}
    (w : TailConvexWeights n) (hr : r <= level T n)
    {s t : NNReal}
    (hs : s ∈ Set.range (FactorialChronologicalGrid.stoppedGrid T r).time)
    (ht : t ∈ Set.range (FactorialChronologicalGrid.stoppedGrid T r).time)
    (hst : s <= t) (omega : Omega) :
    BoundedMartingaleQuadraticConvexification.squaredIncrementPart
        M T w s omega <=
      BoundedMartingaleQuadraticConvexification.squaredIncrementPart
        M T w t omega := by
  rw [BoundedMartingaleQuadraticConvexification.squaredIncrementPart_apply,
    BoundedMartingaleQuadraticConvexification.squaredIncrementPart_apply]
  unfold TailConvexWeights.apply
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (w.nonneg i hi)
  have hni : n <= i := w.tail i hi
  have hri : r <= level T i :=
    hr.trans (BoundedMartingaleQuadraticApproximation.level_mono T hni)
  have hs' : s ∈ Set.range
      (BoundedMartingaleQuadraticApproximation.grid T i).time := by
    simpa only [BoundedMartingaleQuadraticApproximation.grid] using
      (FactorialChronologicalGrid.range_stoppedGrid_mono T hri hs)
  have ht' : t ∈ Set.range
      (BoundedMartingaleQuadraticApproximation.grid T i).time := by
    simpa only [BoundedMartingaleQuadraticApproximation.grid] using
      (FactorialChronologicalGrid.range_stoppedGrid_mono T hri ht)
  exact (BoundedMartingaleQuadraticApproximation.grid T i)
    |>.squaredIncrementProcess_mono_of_mem_range
      (deterministicallyStoppedProcess M T)
      hs' ht' hst omega

end Approximation

open BoundedMartingaleQuadraticApproximation
open BoundedMartingaleQuadraticConvexification

/-- Uniform convergence of the selected squared-increment convexifications,
together with their tail support and the nested factorial grids, makes the
right-continuous limit increasing at all times. -/
theorem quadraticLimit_monotone
    {mu : Measure Omega} (M : Process Omega) (T : NNReal)
    (w : forall n, TailConvexWeights n) (cutoff : Nat -> Nat)
    (hCutoff : StrictMono cutoff) (Y : Process Omega)
    (hUniform : ∀ᵐ omega ∂mu, TendstoUniformly
      (fun k t =>
        BoundedMartingaleQuadraticConvexification.squaredIncrementPart
          M T (w (cutoff k)) t omega)
      (fun t => deterministicallyStoppedProcess M T t omega ^ 2 -
        deterministicallyStoppedProcess M T 0 omega ^ 2 - Y t omega) atTop)
    (hRight : forall omega t, ContinuousWithinAt
      (fun u => deterministicallyStoppedProcess M T u omega ^ 2 -
        deterministicallyStoppedProcess M T 0 omega ^ 2 - Y u omega) (Ici t) t) :
    ∀ᵐ omega ∂mu, Monotone (fun t =>
      deterministicallyStoppedProcess M T t omega ^ 2 -
        deterministicallyStoppedProcess M T 0 omega ^ 2 - Y t omega) := by
  let Q : Process Omega := fun t omega =>
    deterministicallyStoppedProcess M T t omega ^ 2 -
      deterministicallyStoppedProcess M T 0 omega ^ 2 - Y t omega
  filter_upwards [hUniform] with omega hUniformOmega
  have hConstant : forall t, T <= t -> Q t omega = Q T omega := by
    intro t ht
    have htLimit := hUniformOmega.tendsto_at t
    have hTLimit := hUniformOmega.tendsto_at T
    have hSequenceEq :
        (fun k =>
          BoundedMartingaleQuadraticConvexification.squaredIncrementPart
            M T (w (cutoff k)) t omega) =
        fun k =>
          BoundedMartingaleQuadraticConvexification.squaredIncrementPart
            M T (w (cutoff k)) T omega := by
      funext k
      exact congrFun
        (Approximation.squaredIncrementPart_constantAfter
          M T (w (cutoff k)) ht) omega
    have htLimit' : Tendsto
        (fun k =>
          BoundedMartingaleQuadraticConvexification.squaredIncrementPart
            M T (w (cutoff k)) t omega)
        atTop (𝓝 (Q T omega)) := by
      rw [hSequenceEq]
      exact hTLimit
    exact tendsto_nhds_unique htLimit htLimit'
  have hWithin : forall {s t : NNReal}, s <= t -> t <= T ->
      Q s omega <= Q t omega := by
    intro s t hst htT
    have hsT : s <= T := hst.trans htT
    have hsLimit : Tendsto
        (fun r => Q (min (FactorialChronologicalGrid.approx r s) T) omega)
        atTop (𝓝 (Q s omega)) :=
      FiniteVariationFactorialApproximation.tendsto_apply_min_approx
        (fun u => Q u omega) (hRight omega) hsT
    have htLimit : Tendsto
        (fun r => Q (min (FactorialChronologicalGrid.approx r t) T) omega)
        atTop (𝓝 (Q t omega)) :=
      FiniteVariationFactorialApproximation.tendsto_apply_min_approx
        (fun u => Q u omega) (hRight omega) htT
    apply le_of_tendsto_of_tendsto hsLimit htLimit
    filter_upwards [eventually_ge_atTop (Nat.ceil T)] with r hrT
    let u : NNReal := min (FactorialChronologicalGrid.approx r s) T
    let v : NNReal := min (FactorialChronologicalGrid.approx r t) T
    have hsr : Nat.ceil s <= r :=
      (Nat.ceil_mono hsT).trans hrT
    have htr : Nat.ceil t <= r :=
      (Nat.ceil_mono htT).trans hrT
    have huMem : u ∈ Set.range
        (FactorialChronologicalGrid.stoppedGrid T r).time := by
      refine ⟨FactorialChronologicalGrid.approxIndex s hsr, ?_⟩
      simp only [FactorialChronologicalGrid.stoppedGrid_time,
        FactorialChronologicalGrid.grid_time_approxIndex, u]
    have hvMem : v ∈ Set.range
        (FactorialChronologicalGrid.stoppedGrid T r).time := by
      refine ⟨FactorialChronologicalGrid.approxIndex t htr, ?_⟩
      simp only [FactorialChronologicalGrid.stoppedGrid_time,
        FactorialChronologicalGrid.grid_time_approxIndex, v]
    have huv : u <= v := by
      exact min_le_min
        (FactorialChronologicalGrid.approx_mono r hst) le_rfl
    have huLimit := hUniformOmega.tendsto_at u
    have hvLimit := hUniformOmega.tendsto_at v
    apply le_of_tendsto_of_tendsto huLimit hvLimit
    filter_upwards [eventually_ge_atTop r] with k hrk
    have hrCutoff : r <= cutoff k :=
      hrk.trans (hCutoff.id_le k)
    have hrLevel : r <= level T (cutoff k) :=
      hrCutoff.trans (self_le_level T (cutoff k))
    exact Approximation.squaredIncrementPart_mono_on_stoppedGrid_range
      M T (w (cutoff k)) hrLevel huMem hvMem huv omega
  have hMin (t : NNReal) : Q t omega = Q (min t T) omega := by
    by_cases ht : t <= T
    · rw [min_eq_left ht]
    · exact (hConstant t (le_of_not_ge ht)).trans (by rw [min_eq_right (le_of_not_ge ht)])
  intro s t hst
  change Q s omega <= Q t omega
  rw [hMin s, hMin t]
  exact hWithin (min_le_min hst le_rfl) (min_le_right t T)

end BoundedMartingaleQuadraticVariation

end FTAPTheorem42
