/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Core.KreinSmulianPredualSeparator

/-!
# The Krein--Šmulian closedness criterion

This module applies the predual separation lemma to a translated and rescaled
convex set.  It proves that a convex subset of a real Banach dual is
weak-star closed as soon as every norm-bounded slice is weak-star closed.
-/

open Topology

namespace FTAPTheorem42

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Translate by `ψ` and rescale by `a` before testing membership in `C`. -/
def weakDualTranslatedRescaling
    (C : Set (WeakDual ℝ E))
    (ψ : WeakDual ℝ E) (a : ℝ) :
    Set (WeakDual ℝ E) :=
  {δ | ψ + a • δ ∈ C}

theorem convex_weakDualTranslatedRescaling
    {C : Set (WeakDual ℝ E)}
    (hC : Convex ℝ C)
    (ψ : WeakDual ℝ E) (a : ℝ) :
    Convex ℝ (weakDualTranslatedRescaling C ψ a) := by
  intro δ hδ η hη p q hp hq hpq
  change
    ψ + a • (p • δ + q • η) ∈ C
  have hcomb :=
    hC hδ hη hp hq hpq
  convert hcomb using 1
  calc
    ψ + a • (p • δ + q • η) =
        (p + q) • ψ + a • (p • δ + q • η) := by
          rw [hpq, one_smul]
    _ = p • (ψ + a • δ) + q • (ψ + a • η) := by
          module

/-- A positive translated rescaling preserves weak-star closedness of all
norm-bounded slices. -/
theorem isClosed_weakDualNormSlice_translatedRescaling
    {C : Set (WeakDual ℝ E)}
    (hclosed :
      ∀ r : ℝ, 0 ≤ r →
        IsClosed (weakDualNormSlice C r))
    (ψ : WeakDual ℝ E) {a : ℝ} (ha : 0 ≤ a)
    (r : ℝ) (hr : 0 ≤ r) :
    IsClosed
      (weakDualNormSlice
        (weakDualTranslatedRescaling C ψ a) r) := by
  let F : WeakDual ℝ E → WeakDual ℝ E :=
    fun δ => ψ + a • δ
  let R : ℝ :=
    ‖WeakDual.toStrongDual ψ‖ + a * r
  have hR : 0 ≤ R :=
    add_nonneg (norm_nonneg _) (mul_nonneg ha hr)
  have hFcontinuous : Continuous F :=
    continuous_const.add (continuous_id.const_smul a)
  have heq :
      weakDualNormSlice
          (weakDualTranslatedRescaling C ψ a) r =
        F ⁻¹' weakDualNormSlice C R ∩
          WeakDual.toStrongDual ⁻¹'
            Metric.closedBall
              (0 : StrongDual ℝ E) r := by
    ext δ
    constructor
    · intro hδ
      refine ⟨⟨hδ.1, ?_⟩, hδ.2⟩
      change
        WeakDual.toStrongDual (F δ) ∈
          Metric.closedBall
            (0 : StrongDual ℝ E) R
      rw [mem_closedBall_zero_iff]
      calc
        ‖WeakDual.toStrongDual (F δ)‖
            ≤ ‖WeakDual.toStrongDual ψ‖ +
                ‖a • WeakDual.toStrongDual δ‖ := by
              simpa [F] using
                norm_add_le
                  (WeakDual.toStrongDual ψ)
                  (a • WeakDual.toStrongDual δ)
        _ = ‖WeakDual.toStrongDual ψ‖ +
              |a| * ‖WeakDual.toStrongDual δ‖ := by
              rw [norm_smul, Real.norm_eq_abs]
        _ ≤ ‖WeakDual.toStrongDual ψ‖ + a * r := by
              rw [abs_of_nonneg ha]
              gcongr
              simpa only [Set.mem_preimage,
                mem_closedBall_zero_iff] using hδ.2
        _ = R := rfl
    · intro hδ
      exact ⟨hδ.1.1, hδ.2⟩
  rw [heq]
  exact
    ((hclosed R hR).preimage hFcontinuous).inter
      (WeakDual.isClosed_closedBall
        (𝕜 := ℝ) (0 : StrongDual ℝ E) r)

/-- Krein--Šmulian criterion for a convex subset of a real Banach dual. -/
theorem isClosed_of_isClosed_weakDualNormSlice
    [CompleteSpace E]
    {C : Set (WeakDual ℝ E)}
    (hC : Convex ℝ C)
    (hclosed :
      ∀ r : ℝ, 0 ≤ r →
        IsClosed (weakDualNormSlice C r)) :
    IsClosed C := by
  apply isClosed_of_closure_subset
  intro ψ hψclosure
  by_contra hψC
  have hstrongClosed :
      IsClosed (StrongDual.toWeakDual ⁻¹' C) :=
    isClosed_strongDual_preimage_of_isClosed_weakDualNormSlice
      hclosed
  have hψstrong :
      WeakDual.toStrongDual ψ ∉
        StrongDual.toWeakDual ⁻¹' C := by
    simpa using hψC
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp hstrongClosed.isOpen_compl
      (WeakDual.toStrongDual ψ) hψstrong
  let a : ℝ := ε / 2
  have ha : 0 < a := half_pos hε
  let D : Set (WeakDual ℝ E) :=
    weakDualTranslatedRescaling C ψ a
  have hDconvex : Convex ℝ D :=
    convex_weakDualTranslatedRescaling hC ψ a
  have hDclosed :
      ∀ r : ℝ, 0 ≤ r →
        IsClosed (weakDualNormSlice D r) := by
    intro r hr
    exact
      isClosed_weakDualNormSlice_translatedRescaling
        hclosed ψ ha.le r hr
  have hDunit :
      Disjoint D
        (WeakDual.toStrongDual ⁻¹'
          Metric.closedBall
            (0 : StrongDual ℝ E) 1) := by
    rw [Set.disjoint_left]
    intro δ hδD hδball
    have hnear :
        WeakDual.toStrongDual (ψ + a • δ) ∈
          Metric.ball (WeakDual.toStrongDual ψ) ε := by
      change
        dist (WeakDual.toStrongDual (ψ + a • δ))
          (WeakDual.toStrongDual ψ) < ε
      rw [dist_eq_norm]
      have hδnorm :
          ‖WeakDual.toStrongDual δ‖ ≤ 1 := by
        simpa only [Set.mem_preimage,
          mem_closedBall_zero_iff] using hδball
      calc
        ‖WeakDual.toStrongDual (ψ + a • δ) -
            WeakDual.toStrongDual ψ‖ =
            a * ‖WeakDual.toStrongDual δ‖ := by
              rw [map_add, map_smul, add_sub_cancel_left,
                norm_smul, Real.norm_eq_abs,
                abs_of_pos ha]
        _ ≤ a * 1 :=
          mul_le_mul_of_nonneg_left hδnorm ha.le
        _ < ε := by
          simpa [a] using half_lt_self hε
    exact (hball hnear) hδD
  obtain ⟨x, hxnorm, hxsep⟩ :=
    exists_predual_unit_separator_of_closedSlices
      hDconvex hDclosed hDunit
  have hCsep :
      ∀ φ : WeakDual ℝ E, φ ∈ C →
        ψ x + a ≤ φ x := by
    intro φ hφ
    let δ : WeakDual ℝ E :=
      a⁻¹ • (φ - ψ)
    have hδD : δ ∈ D := by
      change ψ + a • δ ∈ C
      simpa [δ, ha.ne'] using hφ
    have hsep := hxsep δ hδD
    change 1 ≤ a⁻¹ * (φ x - ψ x) at hsep
    linarith [((le_inv_mul_iff₀ ha).mp hsep)]
  let H : Set (WeakDual ℝ E) :=
    {φ | ψ x + a ≤ φ x}
  have hHclosed : IsClosed H := by
    exact isClosed_le continuous_const
      (WeakDual.eval_continuous x)
  have hCsub : C ⊆ H := by
    intro φ hφ
    exact hCsep φ hφ
  have hψH : ψ ∈ H :=
    closure_minimal hCsub hHclosed hψclosure
  change ψ x + a ≤ ψ x at hψH
  linarith

end FTAPTheorem42
