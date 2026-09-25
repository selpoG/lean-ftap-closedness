/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Core.KreinSmulian
import Mathlib.Analysis.Normed.Group.ZeroAtInfty
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.TendstoCofinite

/-!
# The `c₀` evaluation map in the Krein--Šmulian proof

This module turns the finite-polar tower into a discrete family of predual
vectors tending to zero.  Evaluation on that family therefore defines a
bounded linear map from the strong dual into a `c₀` space.
-/

open Filter Topology

namespace FTAPTheorem42

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {C : Set (WeakDual ℝ E)}

/-- A coordinate in the disjoint union of the finite predual sets of a
finite-polar tower. -/
structure KreinSmulianPolarIndex
    (T : KreinSmulianFinitePolarTower C) where
  level : ℕ
  point : E
  point_mem : point ∈ T.family level

namespace KreinSmulianPolarIndex

variable (T : KreinSmulianFinitePolarTower C)

instance : TopologicalSpace (KreinSmulianPolarIndex T) := ⊥

instance : DiscreteTopology (KreinSmulianPolarIndex T) :=
  ⟨rfl⟩

/-- The fiber at level `n` is equivalent to the finite set `Fₙ`. -/
noncomputable def levelFiberEquiv (n : ℕ) :
    {i : KreinSmulianPolarIndex T // i.level = n} ≃ T.family n where
  toFun i :=
    ⟨i.1.point, by
      simpa [i.2] using i.1.point_mem⟩
  invFun x :=
    ⟨⟨n, x.1, x.2⟩, rfl⟩
  left_inv i := by
    rcases i with ⟨⟨level, point, hpoint⟩, hlevel⟩
    subst n
    rfl
  right_inv x := rfl

theorem finite_level_fiber (n : ℕ) :
    Set.Finite {i : KreinSmulianPolarIndex T | i.level = n} := by
  rw [Set.finite_def]
  let : Fintype (T.family n) :=
    (T.family_finite n).fintype
  exact
    ⟨Fintype.ofEquiv (T.family n)
      (levelFiberEquiv T n).symm⟩

/-- The level tends to infinity along the cofinite filter because every level
has only finitely many coordinates. -/
theorem level_tendsto_atTop :
    Tendsto
      (fun i : KreinSmulianPolarIndex T => i.level)
      cofinite atTop := by
  rw [← Nat.cofinite_eq_atTop]
  apply Filter.Tendsto.cofinite_of_finite_preimage_singleton
  intro n
  have hfinite :
      Set.Finite
        ((fun i : KreinSmulianPolarIndex T => i.level) ⁻¹' {n}) := by
    convert finite_level_fiber T n using 1
    ext i
    simp
  exact hfinite.to_subtype

theorem point_norm_le (i : KreinSmulianPolarIndex T) :
    ‖i.point‖ ≤ (((i.level + 1 : ℕ) : ℝ)⁻¹) := by
  have hi :=
    T.family_subset_closedBall i.level i.point_mem
  simpa only [mem_closedBall_zero_iff] using hi

theorem point_norm_le_one (i : KreinSmulianPolarIndex T) :
    ‖i.point‖ ≤ 1 := by
  exact (point_norm_le T i).trans (by
    rw [inv_le_one₀ (by positivity)]
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.zero_lt_succ i.level))

end KreinSmulianPolarIndex

namespace KreinSmulianFinitePolarTower

variable (T : KreinSmulianFinitePolarTower C)

/-- Raw evaluation of a weak-dual functional on the finite-polar
coordinates. -/
noncomputable def polarEvaluation (φ : WeakDual ℝ E) :
    KreinSmulianPolarIndex T → ℝ :=
  fun i => φ i.point

theorem norm_polarEvaluation_le
    (φ : WeakDual ℝ E) (i : KreinSmulianPolarIndex T) :
    ‖T.polarEvaluation φ i‖ ≤
      ‖WeakDual.toStrongDual φ‖ *
        (((i.level + 1 : ℕ) : ℝ)⁻¹) := by
  calc
    ‖T.polarEvaluation φ i‖
        ≤ ‖WeakDual.toStrongDual φ‖ * ‖i.point‖ :=
      (WeakDual.toStrongDual φ).le_opNorm i.point
    _ ≤
        ‖WeakDual.toStrongDual φ‖ *
          (((i.level + 1 : ℕ) : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left
        (KreinSmulianPolarIndex.point_norm_le T i)
        (norm_nonneg _)

/-- Evaluation tends to zero along the cofinite filter. -/
theorem polarEvaluation_tendsto_zero (φ : WeakDual ℝ E) :
    Tendsto (T.polarEvaluation φ) cofinite (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero
  · intro i
    exact norm_nonneg _
  · intro i
    exact T.norm_polarEvaluation_le φ i
  · have hscalar :
        Tendsto
          (fun n : ℕ =>
            ‖WeakDual.toStrongDual φ‖ *
              (1 / ((n : ℝ) + 1)))
          atTop (𝓝 0) := by
      simpa using
        ((tendsto_const_nhds :
            Tendsto
              (fun _ : ℕ => ‖WeakDual.toStrongDual φ‖)
              atTop (𝓝 ‖WeakDual.toStrongDual φ‖)).mul
          tendsto_one_div_add_atTop_nhds_zero_nat)
    have hcomp :=
      hscalar.comp
        (KreinSmulianPolarIndex.level_tendsto_atTop T)
    convert hcomp using 1
    funext i
    simp

/-- Evaluation as an element of the discrete `c₀` space associated with the
finite-polar tower. -/
noncomputable def polarEvaluationC0 (φ : WeakDual ℝ E) :
    ZeroAtInftyContinuousMap (KreinSmulianPolarIndex T) ℝ where
  toFun := T.polarEvaluation φ
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [Filter.cocompact_eq_cofinite]
    exact T.polarEvaluation_tendsto_zero φ

/-- The `c₀` evaluation map as a linear map on the strong dual. -/
noncomputable def polarEvaluationLinearMap :
    StrongDual ℝ E →ₗ[ℝ]
      ZeroAtInftyContinuousMap (KreinSmulianPolarIndex T) ℝ where
  toFun φ :=
    T.polarEvaluationC0 (StrongDual.toWeakDual φ)
  map_add' φ ψ := by
    apply ZeroAtInftyContinuousMap.ext
    intro i
    change (φ + ψ) i.point = φ i.point + ψ i.point
    simp
  map_smul' a φ := by
    apply ZeroAtInftyContinuousMap.ext
    intro i
    change (a • φ) i.point = a * φ i.point
    simp

theorem norm_polarEvaluationC0_le (φ : StrongDual ℝ E) :
    ‖T.polarEvaluationC0 (StrongDual.toWeakDual φ)‖ ≤ ‖φ‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  apply
    (BoundedContinuousFunction.norm_le (norm_nonneg φ)).mpr
  intro i
  calc
    ‖T.polarEvaluationC0 (StrongDual.toWeakDual φ) i‖
        ≤ ‖φ‖ * ‖i.point‖ :=
      φ.le_opNorm i.point
    _ ≤ ‖φ‖ * 1 :=
      mul_le_mul_of_nonneg_left
        (KreinSmulianPolarIndex.point_norm_le_one T i)
        (norm_nonneg φ)
    _ = ‖φ‖ := mul_one _

/-- The bounded `c₀` evaluation operator used in the separation argument. -/
noncomputable def polarEvaluationCLM :
    StrongDual ℝ E →L[ℝ]
      ZeroAtInftyContinuousMap (KreinSmulianPolarIndex T) ℝ :=
  T.polarEvaluationLinearMap.mkContinuous 1 fun φ => by
    change
      ‖T.polarEvaluationC0 (StrongDual.toWeakDual φ)‖
        ≤ 1 * ‖φ‖
    simpa using T.norm_polarEvaluationC0_le φ

/-- A member of `C` is sent strictly outside the closed unit ball of the
coordinate `c₀` space. -/
theorem one_lt_norm_polarEvaluationC0_of_mem
    {φ : WeakDual ℝ E} (hφ : φ ∈ C) :
    1 < ‖T.polarEvaluationC0 φ‖ := by
  have hnot :
      φ ∉ ⋂ n, WeakDual.polar ℝ (T.family n) := by
    exact fun hmem =>
      Set.disjoint_left.mp T.disjoint_iInter_polar_family
        hφ hmem
  simp only [Set.mem_iInter] at hnot
  push Not at hnot
  obtain ⟨n, hn⟩ := hnot
  have hn' :
      ¬ ∀ x ∈ T.family n, ‖φ x‖ ≤ 1 := by
    simpa only [WeakDual.polar_def, Set.mem_ofPred_eq] using hn
  push Not at hn'
  obtain ⟨x, hx, hnorm⟩ := hn'
  let i : KreinSmulianPolarIndex T :=
    ⟨n, x, hx⟩
  have hle :
      ‖T.polarEvaluationC0 φ i‖ ≤
        ‖T.polarEvaluationC0 φ‖ := by
    calc
      ‖T.polarEvaluationC0 φ i‖ =
          ‖(T.polarEvaluationC0 φ).toBCF i‖ := rfl
      _ ≤ ‖(T.polarEvaluationC0 φ).toBCF‖ :=
        (T.polarEvaluationC0 φ).toBCF.norm_coe_le_norm i
      _ = ‖T.polarEvaluationC0 φ‖ :=
        ZeroAtInftyContinuousMap.norm_toBCF_eq_norm
  exact hnorm.trans_le hle

end KreinSmulianFinitePolarTower

end FTAPTheorem42
