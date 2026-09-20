/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import Mathlib.Analysis.LocallyConvex.Basic
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.LinearAlgebra.Prod

/-! # The Baire step of open mapping for real topological vector spaces -/

namespace FTAPTheorem42.FSpace

section Topological

open Filter Set Topology
open scoped Pointwise

variable {E G : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module Real E] [ContinuousSMul Real E]
  [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [Module Real G] [ContinuousSMul Real G] [BaireSpace G]

omit [IsTopologicalAddGroup E] [IsTopologicalAddGroup G] in
/-- Scalar dilation gives the countable cover needed by Baire, without any
separability or local convexity assumption. -/
theorem closure_image_interior_nonempty (f : E →ₗ[Real] G)
    (hf : Function.Surjective f) {U : Set E} (hU : U ∈ 𝓝 0) :
    (interior (closure (f '' U))).Nonempty := by
  let A := closure (f '' U)
  have hCover : (⋃ n : Nat, ((n : Real) + 1) • A) = univ := by
    apply eq_univ_of_forall
    intro y
    obtain ⟨x, rfl⟩ := hf y
    have hLim : Tendsto (fun n : Nat => (1 / ((n : Real) + 1)) • x) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real)).smul_const x
    obtain ⟨n, hn⟩ := (hLim.eventually hU).exists
    refine mem_iUnion.mpr ⟨n, ?_⟩
    refine ⟨f ((1 / ((n : Real) + 1)) • x), subset_closure ⟨_, hn, rfl⟩, ?_⟩
    change ((n : Real) + 1) • f ((1 / ((n : Real) + 1)) • x) = f x
    rw [map_smul, smul_smul]
    simp [show (n : Real) + 1 ≠ 0 by positivity]
  obtain ⟨n, y, hy⟩ := nonempty_interior_of_iUnion_of_closed
    (fun n : Nat => (Homeomorph.smulOfNeZero ((n : Real) + 1)
      (by positivity)).isClosedMap _ isClosed_closure) hCover
  have hne : (n : Real) + 1 ≠ 0 := by positivity
  change y ∈ interior (((n : Real) + 1) • A) at hy
  rw [interior_smul₀ hne] at hy
  obtain ⟨z, hz, _⟩ := hy
  exact ⟨z, hz⟩

/-- The closure of every zero-neighborhood image is a zero-neighborhood.
Completeness will be used separately to remove the closure. -/
theorem closure_image_mem_nhds (f : E →ₗ[Real] G)
    (hf : Function.Surjective f) {U : Set E} (hU : U ∈ 𝓝 0) :
    closure (f '' U) ∈ 𝓝 0 := by
  obtain ⟨V, hV, _, hNeg, hAdd⟩ := exists_closed_nhds_zero_neg_eq_add_subset hU
  obtain ⟨a, ha⟩ := closure_image_interior_nonempty f hf hV
  have hN := (Homeomorph.subRight a).isOpenMap.image_mem_nhds
    (isOpen_interior.mem_nhds ha)
  simp only [Homeomorph.subRight_apply, sub_self] at hN
  apply mem_of_superset hN
  rintro _ ⟨b, hb, rfl⟩
  apply map_mem_closure₂ continuous_sub (interior_subset hb) (interior_subset ha)
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  refine ⟨x - y, ?_, map_sub f x y⟩
  apply hAdd
  refine ⟨x, hx, -y, ?_, (sub_eq_add_neg x y).symm⟩
  rw [← hNeg]
  simpa using hy

end Topological

section OpenMapping

/-! ## Removing closure from neighborhood images by complete metric approximation -/

open Filter Set Topology Metric

variable {E G : Type*} [AddCommGroup E] [MetricSpace E] [IsTopologicalAddGroup E]
  [Module Real E] [ContinuousSMul Real E] [IsIsometricVAdd E E] [CompleteSpace E]
  [AddCommGroup G] [MetricSpace G] [IsTopologicalAddGroup G]
  [Module Real G] [ContinuousSMul Real G] [IsIsometricVAdd G G] [BaireSpace G]

/-- Baire's neighborhood-closure estimate yields exact small preimages by
successive corrections in a complete translation-invariant metric. -/
theorem image_ball_mem_nhds (f : E →L[Real] G) (hf : Function.Surjective f)
    {ε : Real} (hε : 0 < ε) : f '' ball 0 ε ∈ 𝓝 0 := by
  have hRadius : ∀ n : Nat, ∃ δ > (0 : Real), δ ≤ (1 / 2 : Real) ^ n ∧
      ball 0 δ ⊆ closure (f '' ball 0 (ε / 4 * (1 / 2 : Real) ^ n)) := by
    intro n
    obtain ⟨δ, hδ, hSub⟩ := Metric.mem_nhds_iff.mp
      (closure_image_mem_nhds f.toLinearMap hf
        (U := ball 0 (ε / 4 * (1 / 2 : Real) ^ n)) (ball_mem_nhds _ (by positivity)))
    exact ⟨min δ ((1 / 2 : Real) ^ n), lt_min hδ (by positivity),
      min_le_right _ _, (ball_subset_ball (min_le_left _ _)).trans hSub⟩
  choose δ hδ hδle hSub using hRadius
  apply mem_of_superset (ball_mem_nhds 0 (hδ 0))
  intro y hy
  have hStep : ∀ n x, dist (f x) y < δ n → ∃ z,
      dist (f z) y < δ (n + 1) ∧ dist x z ≤ ε / 4 * (1 / 2 : Real) ^ n := by
    intro n x hx
    have hRes : y - f x ∈ closure (f '' ball 0 (ε / 4 * (1 / 2 : Real) ^ n)) := by
      apply hSub n
      rw [mem_ball]
      have heq : dist (y - f x) 0 = dist y (f x) := by
        simpa [sub_eq_add_neg, add_comm] using dist_add_left (-f x) y (f x)
      rw [heq, dist_comm]
      exact hx
    obtain ⟨_, ⟨v, hv, rfl⟩, hClose⟩ := Metric.mem_closure_iff.mp hRes _ (hδ (n + 1))
    refine ⟨x + v, ?_, ?_⟩
    · have heq := dist_add_left (f x) (f v) (y - f x)
      rw [show f x + (y - f x) = y by abel] at heq
      rw [map_add, heq, dist_comm]
      exact hClose
    · have heq := dist_add_left x 0 v
      rw [add_zero] at heq
      rw [heq, dist_comm]
      exact hv.le
  choose step hStepClose hStepDist using hStep
  let s : ∀ n : Nat, {x : E // dist (f x) y < δ n} :=
    fun n => Nat.rec ⟨0, by simpa [dist_comm] using hy⟩
      (fun n x => ⟨step n x.val x.property, hStepClose n x.val x.property⟩) n
  have hDist : ∀ n, dist (s n).val (s (n + 1)).val ≤ ε / 4 * (1 / 2 : Real) ^ n :=
    fun n => hStepDist n (s n).val (s n).property
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric (1 / 2) (ε / 4) (by norm_num : (1 / 2 : Real) < 1) hDist)
  have hBound := dist_le_of_le_geometric_of_tendsto₀ (1 / 2) (ε / 4)
    (by norm_num : (1 / 2 : Real) < 1) hDist hx
  have hfx : Tendsto (fun n => f (s n).val) atTop (𝓝 y) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ => dist_nonneg)
      (fun n => (s n).property.le.trans (hδle n))
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  refine ⟨x, ?_, tendsto_nhds_unique (f.continuous.tendsto x |>.comp hx) hfx⟩
  change dist x 0 < ε
  have : dist x 0 ≤ ε / 2 := by norm_num [s, dist_comm] at hBound ⊢; linarith
  linarith

/-- Open mapping for complete real vector spaces equipped with invariant
metrics. The target only needs the Baire property. -/
theorem isOpenMap (f : E →L[Real] G) (hf : Function.Surjective f) : IsOpenMap f := by
  apply IsTopologicalAddGroup.isOpenMap_iff_nhds_zero.mpr
  intro U hU
  obtain ⟨ε, hε, hSub⟩ := Metric.mem_nhds_iff.mp (show f ⁻¹' U ∈ 𝓝 0 from hU)
  apply mem_of_superset (image_ball_mem_nhds f hf hε)
  rintro _ ⟨x, hx, rfl⟩
  exact hSub hx

end OpenMapping

section ClosedGraph

/-! ## Closed graph for complete real vector spaces with invariant metrics -/

open Set Topology

variable {E G : Type*} [AddCommGroup E] [MetricSpace E] [IsTopologicalAddGroup E]
  [Module Real E] [ContinuousSMul Real E] [IsIsometricVAdd E E] [CompleteSpace E]
  [AddCommGroup G] [MetricSpace G] [IsTopologicalAddGroup G]
  [Module Real G] [ContinuousSMul Real G] [IsIsometricVAdd G G] [CompleteSpace G]

/-- Apply open mapping to the first projection of the closed graph. -/
theorem continuous_of_isClosed_graph (f : E →ₗ[Real] G)
    (hf : IsClosed (f.graph : Set (E × G))) : Continuous f := by
  let : CompleteSpace f.graph := completeSpace_coe_iff_isComplete.mpr hf.isComplete
  let : IsIsometricVAdd f.graph f.graph := ⟨fun a b c => by
    change edist (a.val + b.val) (a.val + c.val) = edist b.val c.val
    exact (isometry_vadd (E × G) a.val) b.val c.val⟩
  let φ₀ : E →ₗ[Real] E × G := LinearMap.id.prod f
  have hLeft : Function.LeftInverse Prod.fst φ₀ := fun _ => rfl
  let φ : E ≃ₗ[Real] f.graph :=
    (LinearEquiv.ofLeftInverse hLeft).trans (LinearEquiv.ofEq _ _ f.graph_eq_range_prod.symm)
  let ψ : f.graph →L[Real] E := ⟨φ.symm.toLinearMap, continuous_subtype_val.fst⟩
  have hOpen := isOpenMap ψ φ.symm.surjective
  have hφ : Continuous φ := by
    apply continuous_def.mpr
    intro U hU
    have heq : φ ⁻¹' U = ψ '' U := by
      ext x
      exact ⟨fun hx => ⟨φ x, hx, φ.symm_apply_apply x⟩,
        fun ⟨y, hy, hxy⟩ => by
          rw [← hxy]
          change φ (φ.symm y) ∈ U
          simpa using hy⟩
    rw [heq]
    exact hOpen U hU
  exact (continuous_subtype_val.comp hφ).snd

end ClosedGraph

end FTAPTheorem42.FSpace
