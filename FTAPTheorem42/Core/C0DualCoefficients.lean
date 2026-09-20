/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import Mathlib.Analysis.Normed.Group.ZeroAtInfty
import Mathlib.Basic.Real.Sign
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Coefficients of a functional on a discrete `c₀` space

For a discrete index type, evaluation of a continuous linear functional on
the coordinate vectors gives an absolutely summable coefficient family.  This
is the coefficient estimate needed in the Krein--Šmulian separation proof.
-/

open Filter Topology

namespace FTAPTheorem42

variable {I : Type*} [TopologicalSpace I] [DiscreteTopology I]

noncomputable local instance : DecidableEq I :=
  Classical.decEq I

/-- The coordinate vector at `i` in a discrete `c₀` space. -/
noncomputable def c0BasisVector (i : I) :
    ZeroAtInftyContinuousMap I ℝ where
  toFun j := if j = i then 1 else 0
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [Filter.cocompact_eq_cofinite]
    apply tendsto_def.mpr
    intro s hs
    filter_upwards [Filter.eventually_cofinite_ne i] with j hj
    change (if j = i then 1 else 0) ∈ s
    rw [ite_eq_right hj]
    exact mem_of_mem_nhds hs

/-- The coefficient of a functional on the coordinate `i`. -/
noncomputable def c0DualCoefficient
    (Λ : StrongDual ℝ (ZeroAtInftyContinuousMap I ℝ))
    (i : I) : ℝ :=
  Λ (c0BasisVector i)

/-- The finite sign combination used to estimate the absolute sum of the
coordinate coefficients. -/
noncomputable def c0SignedCombination
    (Λ : StrongDual ℝ (ZeroAtInftyContinuousMap I ℝ))
    (s : Finset I) :
    ZeroAtInftyContinuousMap I ℝ :=
  ∑ i ∈ s, Real.sign (c0DualCoefficient Λ i) • c0BasisVector i

@[simp]
theorem c0SignedCombination_apply
    (Λ : StrongDual ℝ (ZeroAtInftyContinuousMap I ℝ))
    (s : Finset I) (j : I) :
    c0SignedCombination Λ s j =
      if j ∈ s then Real.sign (c0DualCoefficient Λ j) else 0 := by
  classical
  let ev :
      ZeroAtInftyContinuousMap I ℝ →ₗ[ℝ] ℝ :=
    {
    toFun f := f j
    map_add' f g := rfl
    map_smul' a f := rfl }
  change
    ev (∑ i ∈ s,
      Real.sign (c0DualCoefficient Λ i) • c0BasisVector i) =
      if j ∈ s then Real.sign (c0DualCoefficient Λ j) else 0
  rw [map_sum]
  simp only [map_smul]
  change
    (∑ i ∈ s,
      Real.sign (c0DualCoefficient Λ i) *
        (if j = i then 1 else 0)) =
      if j ∈ s then Real.sign (c0DualCoefficient Λ j) else 0
  by_cases hj : j ∈ s
  · rw [ite_eq_left hj]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i hi hij
      rw [ite_eq_right (Ne.symm hij)]
      simp
    · exact fun h => (h hj).elim
  · rw [ite_eq_right hj]
    apply Finset.sum_eq_zero
    intro i hi
    have hji : j ≠ i := by
      intro h
      apply hj
      simpa [h] using hi
    rw [ite_eq_right hji]
    simp

theorem abs_sign_le_one (x : ℝ) :
    |Real.sign x| ≤ 1 := by
  obtain hx | hx | hx := lt_trichotomy x 0
  · rw [Real.sign_of_neg hx]
    norm_num
  · subst x
    simp
  · rw [Real.sign_of_pos hx]
    norm_num

theorem norm_c0SignedCombination_le_one
    (Λ : StrongDual ℝ (ZeroAtInftyContinuousMap I ℝ))
    (s : Finset I) :
    ‖c0SignedCombination Λ s‖ ≤ 1 := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  apply
    (BoundedContinuousFunction.norm_le zero_le_one).mpr
  intro j
  change ‖c0SignedCombination Λ s j‖ ≤ 1
  rw [c0SignedCombination_apply]
  split_ifs
  · simpa only [Real.norm_eq_abs] using
      abs_sign_le_one (c0DualCoefficient Λ j)
  · simp

theorem sign_mul_self_eq_abs (x : ℝ) :
    Real.sign x * x = |x| := by
  obtain hx | hx | hx := lt_trichotomy x 0
  · rw [Real.sign_of_neg hx, neg_one_mul, abs_of_neg hx]
  · subst x
    simp
  · rw [Real.sign_of_pos hx, one_mul, abs_of_pos hx]

/-- Every finite sum of absolute coordinate coefficients is bounded by the
operator norm of the functional. -/
theorem sum_abs_c0DualCoefficient_le_norm
    (Λ : StrongDual ℝ (ZeroAtInftyContinuousMap I ℝ))
    (s : Finset I) :
    ∑ i ∈ s, |c0DualCoefficient Λ i| ≤ ‖Λ‖ := by
  have heval :
      Λ (c0SignedCombination Λ s) =
        ∑ i ∈ s, |c0DualCoefficient Λ i| := by
    simp only [c0SignedCombination, map_sum, map_smul,
      smul_eq_mul, c0DualCoefficient]
    apply Finset.sum_congr rfl
    intro i hi
    exact sign_mul_self_eq_abs (Λ (c0BasisVector i))
  calc
    ∑ i ∈ s, |c0DualCoefficient Λ i|
        = ‖Λ (c0SignedCombination Λ s)‖ := by
          rw [heval]
          exact (Real.norm_of_nonneg
            (Finset.sum_nonneg fun i _ => abs_nonneg _)).symm
    _ ≤ ‖Λ‖ * ‖c0SignedCombination Λ s‖ :=
      Λ.le_opNorm _
    _ ≤ ‖Λ‖ * 1 :=
      mul_le_mul_of_nonneg_left
        (norm_c0SignedCombination_le_one Λ s)
        (norm_nonneg Λ)
    _ = ‖Λ‖ := mul_one _

/-- The coordinate coefficients of a continuous linear functional on a
discrete `c₀` space are absolutely summable. -/
theorem summable_abs_c0DualCoefficient
    (Λ : StrongDual ℝ (ZeroAtInftyContinuousMap I ℝ)) :
    Summable (fun i => |c0DualCoefficient Λ i|) := by
  apply summable_of_sum_le
  · exact fun i => abs_nonneg _
  · intro s
    simpa only [Finset.sum_filter, Finset.filter_true_of_mem] using
      sum_abs_c0DualCoefficient_le_norm Λ s

/-- The finite coordinate truncation of a function in a discrete `c₀`
space. -/
noncomputable def c0Truncation
    (f : ZeroAtInftyContinuousMap I ℝ) (s : Finset I) :
    ZeroAtInftyContinuousMap I ℝ :=
  ∑ i ∈ s, f i • c0BasisVector i

@[simp]
theorem c0Truncation_apply
    (f : ZeroAtInftyContinuousMap I ℝ)
    (s : Finset I) (j : I) :
    c0Truncation f s j = if j ∈ s then f j else 0 := by
  classical
  let ev :
      ZeroAtInftyContinuousMap I ℝ →ₗ[ℝ] ℝ :=
    {
      toFun g := g j
      map_add' g h := rfl
      map_smul' a g := rfl }
  change
    ev (∑ i ∈ s, f i • c0BasisVector i) =
      if j ∈ s then f j else 0
  rw [map_sum]
  simp only [map_smul]
  change
    (∑ i ∈ s, f i * (if j = i then 1 else 0)) =
      if j ∈ s then f j else 0
  by_cases hj : j ∈ s
  · rw [ite_eq_left hj, Finset.sum_eq_single j]
    · simp
    · intro i hi hij
      rw [ite_eq_right (Ne.symm hij)]
      simp
    · exact fun h => (h hj).elim
  · rw [ite_eq_right hj]
    apply Finset.sum_eq_zero
    intro i hi
    have hji : j ≠ i := by
      intro h
      apply hj
      simpa [h] using hi
    rw [ite_eq_right hji]
    simp

/-- Finite coordinate truncations converge uniformly to a function in a
discrete `c₀` space. -/
theorem tendsto_c0Truncation
    (f : ZeroAtInftyContinuousMap I ℝ) :
    Tendsto (c0Truncation f) atTop (𝓝 f) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hsmall :
      ∀ᶠ i in cofinite, ‖f i‖ < ε / 2 := by
    have h :=
      (zero_at_infty f).eventually
        (Metric.ball_mem_nhds (0 : ℝ) hhalf)
    rw [Filter.cocompact_eq_cofinite] at h
    simpa only [mem_ball_zero_iff, dist_zero_right] using h
  have hbad :
      {i : I | ¬ ‖f i‖ < ε / 2}.Finite :=
    Filter.eventually_cofinite.mp hsmall
  let s : Finset I := hbad.toFinset
  refine ⟨s, ?_⟩
  intro t hst
  rw [dist_eq_norm, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  have hle :
      ‖(c0Truncation f t - f).toBCF‖ ≤ ε / 2 := by
    apply
      (BoundedContinuousFunction.norm_le hhalf.le).mpr
    intro j
    change ‖c0Truncation f t j - f j‖ ≤ ε / 2
    rw [c0Truncation_apply]
    by_cases hj : j ∈ t
    · rw [ite_eq_left hj, sub_self, norm_zero]
      exact hhalf.le
    · rw [ite_eq_right hj, zero_sub, norm_neg]
      have hjnot :
          j ∉ {i : I | ¬ ‖f i‖ < ε / 2} := by
        intro hnot
        exact hj (hst (by simpa [s] using hnot))
      exact (not_not.mp hjnot).le
  exact hle.trans_lt (half_lt_self hε)

/-- The coordinate vectors give the unconditional basis expansion of a
function in a discrete `c₀` space. -/
theorem hasSum_c0BasisExpansion
    (f : ZeroAtInftyContinuousMap I ℝ) :
    HasSum (fun i => f i • c0BasisVector i) f := by
  exact tendsto_c0Truncation f

/-- A continuous linear functional on a discrete `c₀` space is represented
by its coordinate coefficient series. -/
theorem hasSum_c0DualCoefficient_mul
    (Λ : StrongDual ℝ (ZeroAtInftyContinuousMap I ℝ))
    (f : ZeroAtInftyContinuousMap I ℝ) :
    HasSum
      (fun i => c0DualCoefficient Λ i * f i)
      (Λ f) := by
  have h := Λ.hasSum (hasSum_c0BasisExpansion f)
  simpa only [map_smul, smul_eq_mul, c0DualCoefficient,
    mul_comm] using h

theorem c0Dual_eq_tsum_coefficient_mul
    (Λ : StrongDual ℝ (ZeroAtInftyContinuousMap I ℝ))
    (f : ZeroAtInftyContinuousMap I ℝ) :
    Λ f = ∑' i, c0DualCoefficient Λ i * f i :=
  (hasSum_c0DualCoefficient_mul Λ f).tsum_eq.symm

end FTAPTheorem42
