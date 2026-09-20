/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Martingale.Quadratic.BoundedMartingaleQuadraticApproximation
import FTAPTheorem42.Stochastic.Martingale.Basic.FiniteGridMartingaleProcessCompletion
import FTAPTheorem42.Foundations.HilbertConvexification

/-!
# Forward convex limits of bounded-martingale quadratic approximations

The martingale terms in the factorial-grid square decompositions have a
uniform terminal `L²` bound.  Hilbert forward convexification therefore gives
one terminal-Cauchy sequence.  The same finite-tail weights are applied to the
whole martingale and squared-increment processes.  Process-level martingale
completion then yields a right-continuous true martingale limit, while the
exact square decomposition identifies the uniform limit of the corresponding
squared-increment terms.

Monotonicity of the squared-increment limit is proved in
`BoundedMartingaleQuadraticVariation` using nested factorial grids at
deterministic skeleton times.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace BoundedMartingaleQuadraticConvexification

open BoundedMartingaleQuadraticApproximation

/-- Apply one finite-tail convex weight to the martingale terms of the
quadratic grid decompositions. -/
noncomputable def martingalePart
    (M : Process Omega) (T : NNReal) {n : Nat}
    (w : TailConvexWeights n) : Process Omega :=
  ∑ i ∈ w.support, w.weight i •
    BoundedMartingaleQuadraticApproximation.martingalePart M T i

/-- Apply the same finite-tail convex weight to the squared-increment terms. -/
noncomputable def squaredIncrementPart
    (M : Process Omega) (T : NNReal) {n : Nat}
    (w : TailConvexWeights n) : Process Omega :=
  ∑ i ∈ w.support, w.weight i •
    BoundedMartingaleQuadraticApproximation.squaredIncrementPart M T i

omit [MeasurableSpace Omega] in
@[simp]
theorem martingalePart_apply
    (M : Process Omega) (T t : NNReal) {n : Nat}
    (w : TailConvexWeights n) (omega : Omega) :
    martingalePart M T w t omega =
      w.apply (fun i omega' =>
        BoundedMartingaleQuadraticApproximation.martingalePart
          M T i t omega') omega := by
  simp [martingalePart, TailConvexWeights.apply]

omit [MeasurableSpace Omega] in
@[simp]
theorem squaredIncrementPart_apply
    (M : Process Omega) (T t : NNReal) {n : Nat}
    (w : TailConvexWeights n) (omega : Omega) :
    squaredIncrementPart M T w t omega =
      w.apply (fun i omega' =>
        BoundedMartingaleQuadraticApproximation.squaredIncrementPart
          M T i t omega') omega := by
  simp [squaredIncrementPart, TailConvexWeights.apply]

omit [MeasurableSpace Omega] in
/-- Convexifying both terms preserves the exact square decomposition. -/
theorem martingalePart_add_squaredIncrementPart
    (M : Process Omega) (T t : NNReal) {n : Nat}
    (w : TailConvexWeights n) (omega : Omega) :
    martingalePart M T w t omega + squaredIncrementPart M T w t omega =
      deterministicallyStoppedProcess M T t omega ^ 2
        - deterministicallyStoppedProcess M T 0 omega ^ 2 := by
  rw [martingalePart_apply, squaredIncrementPart_apply]
  unfold TailConvexWeights.apply
  rw [← Finset.sum_add_distrib]
  calc
    (∑ i ∈ w.support,
        (w.weight i *
            BoundedMartingaleQuadraticApproximation.martingalePart
              M T i t omega +
          w.weight i *
            BoundedMartingaleQuadraticApproximation.squaredIncrementPart
              M T i t omega)) =
        ∑ i ∈ w.support, w.weight i *
          (deterministicallyStoppedProcess M T t omega ^ 2 -
            deterministicallyStoppedProcess M T 0 omega ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [← mul_add,
        BoundedMartingaleQuadraticApproximation.martingalePart_add_squaredIncrementPart]
    _ = _ := by
      rw [← Finset.sum_mul, w.sum_eq_one, one_mul]

omit [MeasurableSpace Omega] in
/-- A convexified squared-increment term remains pointwise nonnegative. -/
theorem squaredIncrementPart_nonneg
    (M : Process Omega) (T t : NNReal) {n : Nat}
    (w : TailConvexWeights n) (omega : Omega) :
    0 <= squaredIncrementPart M T w t omega := by
  rw [squaredIncrementPart_apply]
  unfold TailConvexWeights.apply
  exact Finset.sum_nonneg fun i hi => mul_nonneg (w.nonneg i hi)
    (BoundedMartingaleQuadraticApproximation.squaredIncrementPart_nonneg
      M T t i omega)

omit [MeasurableSpace Omega] in
/-- Convexified martingale terms remain right-continuous pathwise. -/
theorem martingalePart_rightContinuous
    (M : Process Omega)
    (hMRight : forall omega t,
      ContinuousWithinAt (M · omega) (Ici t) t)
    (T : NNReal) {n : Nat} (w : TailConvexWeights n) :
    forall omega t, ContinuousWithinAt
      (martingalePart M T w · omega) (Ici t) t := by
  classical
  intro omega t
  unfold martingalePart
  change Tendsto
    (fun u =>
      (∑ i ∈ w.support, w.weight i •
        BoundedMartingaleQuadraticApproximation.martingalePart M T i) u omega)
    (nhdsWithin t (Ici t))
    (𝓝 ((∑ i ∈ w.support, w.weight i •
      BoundedMartingaleQuadraticApproximation.martingalePart M T i) t omega))
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
    (tendsto_finsetSum w.support fun i _hi =>
      (BoundedMartingaleQuadraticApproximation.martingalePart_rightContinuous
        M hMRight T i omega t).const_smul (w.weight i))

omit [MeasurableSpace Omega] in
/-- Convexified martingale terms are constant after the common horizon. -/
theorem martingalePart_constantAfter
    (M : Process Omega) (T : NNReal) {n : Nat}
    (w : TailConvexWeights n) {t : NNReal} (ht : T <= t) :
    martingalePart M T w t = martingalePart M T w T := by
  funext omega
  simp only [martingalePart_apply, TailConvexWeights.apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [BoundedMartingaleQuadraticApproximation.martingalePart_constantAfter
    M T i ht]

end BoundedMartingaleQuadraticConvexification

end FTAPTheorem42
