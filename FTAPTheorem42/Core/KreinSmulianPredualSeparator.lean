/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Core.C0DualCoefficients
import FTAPTheorem42.Core.KreinSmulianC0Separation
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Returning the `c₀` separator to the predual

The coefficients of a functional on the finite-polar `c₀` space are
absolutely summable.  Multiplying them by the corresponding finite-polar
points therefore gives an unconditionally convergent series in the Banach
predual.  Evaluation of its sum is exactly the original `c₀` separator
applied to the finite-polar evaluation map.
-/

open Topology

namespace FTAPTheorem42

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]
variable {C : Set (WeakDual ℝ E)}

namespace KreinSmulianFinitePolarTower

variable (T : KreinSmulianFinitePolarTower C)

private abbrev C0 :=
  ZeroAtInftyContinuousMap (KreinSmulianPolarIndex T) ℝ

/-- The coefficient-weighted finite-polar points form a summable family in
the Banach predual. -/
theorem summable_c0DualCoefficient_smul_point
    (Λ : StrongDual ℝ (C0 T)) :
    Summable
      (fun i : KreinSmulianPolarIndex T =>
        c0DualCoefficient Λ i • i.point) := by
  apply (summable_abs_c0DualCoefficient Λ).of_norm_bounded
  intro i
  rw [norm_smul, Real.norm_eq_abs]
  exact
    mul_le_of_le_one_right (abs_nonneg _)
      (KreinSmulianPolarIndex.point_norm_le_one T i)

/-- The predual vector represented by the coefficient-weighted
finite-polar series. -/
noncomputable def predualSeparator
    (Λ : StrongDual ℝ (C0 T)) : E :=
  ∑' i : KreinSmulianPolarIndex T,
    c0DualCoefficient Λ i • i.point

/-- Evaluation of the predual series agrees with applying the `c₀`
functional to the finite-polar evaluation map. -/
theorem apply_predualSeparator
    (Λ : StrongDual ℝ (C0 T))
    (φ : StrongDual ℝ E) :
    φ (T.predualSeparator Λ) =
      Λ (T.polarEvaluationCLM φ) := by
  calc
    φ (T.predualSeparator Λ) =
        ∑' i : KreinSmulianPolarIndex T,
          φ (c0DualCoefficient Λ i • i.point) := by
      exact φ.map_tsum
        (T.summable_c0DualCoefficient_smul_point Λ)
    _ =
        ∑' i : KreinSmulianPolarIndex T,
          c0DualCoefficient Λ i * φ i.point := by
      congr 1
      funext i
      simp
    _ = Λ (T.polarEvaluationCLM φ) := by
      rw [c0Dual_eq_tsum_coefficient_mul]
      congr 1

/-- The norm of the predual separator is bounded by the total variation of
the coefficient family. -/
theorem norm_predualSeparator_le
    (Λ : StrongDual ℝ (C0 T)) :
    ‖T.predualSeparator Λ‖ ≤
      ∑' i : KreinSmulianPolarIndex T,
        |c0DualCoefficient Λ i| := by
  apply
    (T.summable_c0DualCoefficient_smul_point Λ).hasSum.norm_le_of_bounded
      (summable_abs_c0DualCoefficient Λ).hasSum
  intro i
  rw [norm_smul, Real.norm_eq_abs]
  exact
    mul_le_of_le_one_right (abs_nonneg _)
      (KreinSmulianPolarIndex.point_norm_le_one T i)

/-- Consequently, the predual separator has norm at most the operator norm
of the original `c₀` functional. -/
theorem norm_predualSeparator_le_opNorm
    (Λ : StrongDual ℝ (C0 T)) :
    ‖T.predualSeparator Λ‖ ≤ ‖Λ‖ :=
  (T.norm_predualSeparator_le Λ).trans
    ((summable_abs_c0DualCoefficient Λ).tsum_le_of_sum_le
      (sum_abs_c0DualCoefficient_le_norm Λ))

omit [CompleteSpace E] in
/-- A functional that is strictly below `u` on the open unit ball has
operator norm at most `u`. -/
theorem opNorm_le_of_lt_on_unit_ball
    (Λ : StrongDual ℝ (C0 T)) {u : ℝ}
    (hu : 0 < u)
    (hball : ∀ z : C0 T, ‖z‖ < 1 → Λ z < u) :
    ‖Λ‖ ≤ u := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hu.le
  intro z hz
  have hclosed :
      IsClosed {w : C0 T | Λ w ≤ u} :=
    isClosed_le Λ.continuous continuous_const
  have hball_subset :
      Metric.ball (0 : C0 T) 1 ⊆
        {w : C0 T | Λ w ≤ u} := by
    intro w hw
    exact (hball w (by
      simpa only [mem_ball_zero_iff] using hw)).le
  have hclosedBall_subset :
      Metric.closedBall (0 : C0 T) 1 ⊆
        {w : C0 T | Λ w ≤ u} := by
    rw [← closure_ball (0 : C0 T) one_ne_zero]
    exact closure_minimal hball_subset hclosed
  have hzmem :
      z ∈ Metric.closedBall (0 : C0 T) 1 := by
    simp [hz]
  have hnegmem :
      -z ∈ Metric.closedBall (0 : C0 T) 1 := by
    simp [hz]
  have hupper := hclosedBall_subset hzmem
  have hlower := hclosedBall_subset hnegmem
  change Λ z ≤ u at hupper
  change Λ (-z) ≤ u at hlower
  rw [map_neg] at hlower
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith, hupper⟩

/-- The `c₀` separator produces a point of the closed unit ball of the
predual on which every member of `C` has value at least one. -/
theorem exists_predual_unit_separator
    (T : KreinSmulianFinitePolarTower C)
    (hC : Convex ℝ C) :
    ∃ x : E, ‖x‖ ≤ 1 ∧
      ∀ φ : WeakDual ℝ E, φ ∈ C → 1 ≤ φ x := by
  obtain ⟨Λ, u, hu, hball, himage⟩ :=
    KreinSmulianFinitePolarTower.exists_c0_separator
      (T := T) hC
  let x : E := u⁻¹ • T.predualSeparator Λ
  have hΛnorm : ‖Λ‖ ≤ u :=
    T.opNorm_le_of_lt_on_unit_ball Λ hu hball
  have hxnorm : ‖x‖ ≤ 1 := by
    calc
      ‖x‖ = u⁻¹ * ‖T.predualSeparator Λ‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hu)]
      _ ≤ u⁻¹ * ‖Λ‖ :=
        mul_le_mul_of_nonneg_left
          (T.norm_predualSeparator_le_opNorm Λ)
          (inv_nonneg.mpr hu.le)
      _ ≤ u⁻¹ * u :=
        mul_le_mul_of_nonneg_left hΛnorm
          (inv_nonneg.mpr hu.le)
      _ = 1 := inv_mul_cancel₀ hu.ne'
  refine ⟨x, hxnorm, ?_⟩
  intro φ hφ
  have himageφ :
      u ≤
        Λ
          (T.polarEvaluationCLM
            (WeakDual.toStrongDual φ)) := by
    apply himage
    simpa using hφ
  have happly :
      (WeakDual.toStrongDual φ)
          (T.predualSeparator Λ) =
        Λ
          (T.polarEvaluationCLM
            (WeakDual.toStrongDual φ)) :=
    T.apply_predualSeparator Λ (WeakDual.toStrongDual φ)
  have happly' :
      φ (T.predualSeparator Λ) =
        Λ
          (T.polarEvaluationCLM
            (WeakDual.toStrongDual φ)) := by
    exact happly
  change 1 ≤ φ x
  simp only [x, map_smul, smul_eq_mul]
  rw [happly']
  exact (le_inv_mul_iff₀ hu).mpr (by simpa using himageφ)

end KreinSmulianFinitePolarTower

/-- Closed bounded slices and separation from the dual unit ball yield a
separator belonging to the Banach predual itself.  This is the central
separation lemma in the Krein--Šmulian argument. -/
theorem exists_predual_unit_separator_of_closedSlices
    {C : Set (WeakDual ℝ E)}
    (hC : Convex ℝ C)
    (hclosed :
      ∀ r : ℝ, 0 ≤ r →
        IsClosed (weakDualNormSlice C r))
    (hunit :
      Disjoint C
        (WeakDual.toStrongDual ⁻¹'
          Metric.closedBall
            (0 : StrongDual ℝ E) 1)) :
    ∃ x : E, ‖x‖ ≤ 1 ∧
      ∀ φ : WeakDual ℝ E, φ ∈ C → 1 ≤ φ x := by
  let T :=
    kreinSmulianFinitePolarTower C hclosed hunit
  exact T.exists_predual_unit_separator hC

end FTAPTheorem42
