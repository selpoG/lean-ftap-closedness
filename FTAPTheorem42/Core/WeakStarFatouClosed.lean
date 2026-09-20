/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Core.WeakStarBoundedSlice
import FTAPTheorem42.Core.KreinSmulianCriterion

/-!
# Fatou closed claim cones are weak-star closed

This module combines the topological closedness of every norm-bounded claim
slice with the Krein--Šmulian criterion.  It discharges the functional-
analytic boundary used by the theorem 4.2 assembly.
-/

open MeasureTheory Topology

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

theorem norm_toStrongDual_linftyWeakStarEquivWeakDual
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : LinftyWeakStar μ) :
    ‖WeakDual.toStrongDual
        (linftyWeakStarEquivWeakDual μ F)‖ =
      ‖(toLinftyWeakStar μ).symm F‖ := by
  exact
    norm_linftyL1PairingCLM_apply μ
      ((toLinftyWeakStar μ).symm F)

theorem weakDualNormSlice_linftyClaims_eq
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (D : Set (Ω → ℝ)) (R : ℝ) :
    weakDualNormSlice
        (linftyWeakStarEquivWeakDual μ ''
          ((toLinftyWeakStar μ) '' LinftyClaims μ D)) R =
      linftyWeakStarEquivWeakDual μ ''
        ((toLinftyWeakStar μ) '' LinftyClaimSlice μ D R) := by
  ext φ
  constructor
  · rintro ⟨⟨F, hF, rfl⟩, hnorm⟩
    rcases hF with ⟨u, hu, rfl⟩
    refine ⟨toLinftyWeakStar μ u, ⟨u, ?_, rfl⟩, rfl⟩
    refine ⟨hu, ?_⟩
    rw [mem_closedBall_zero_iff]
    have hnorm' :
        ‖WeakDual.toStrongDual
          (linftyWeakStarEquivWeakDual μ
            (toLinftyWeakStar μ u))‖ ≤ R := by
      simpa only [Set.mem_preimage, mem_closedBall_zero_iff] using hnorm
    rw [norm_toStrongDual_linftyWeakStarEquivWeakDual] at hnorm'
    exact hnorm'
  · rintro ⟨F, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨⟨toLinftyWeakStar μ u, ⟨u, hu.1, rfl⟩, rfl⟩, ?_⟩
    simp only [Set.mem_preimage, mem_closedBall_zero_iff]
    rw [norm_toStrongDual_linftyWeakStarEquivWeakDual]
    exact mem_closedBall_zero_iff.mp hu.2

theorem linftyWeakStarClosed_of_fatouCone
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {D : Set (Ω → ℝ)}
    (hFatou : FatouClosed μ D)
    (hCone : ClaimCone D)
    (hSolid : Solid μ D) :
    LinftyWeakStarClosed μ D := by
  let e :=
    linftyWeakStarEquivWeakDual μ
  let C : Set (WeakDual ℝ (Lp ℝ 1 μ)) :=
    e '' ((toLinftyWeakStar μ) '' LinftyClaims μ D)
  have hCconvex : Convex ℝ C := by
    have hweak :
        Convex ℝ
          ((toLinftyWeakStar μ) '' LinftyClaims μ D) :=
      (LinftyClaims_convex hCone.convex).linear_image
        (toLinftyWeakStar μ).toLinearMap
    exact hweak.linear_image
      (linftyWeakStarEquivWeakDual μ).toLinearEquiv.toLinearMap
  have hCslices :
      ∀ R : ℝ, 0 ≤ R →
        IsClosed (weakDualNormSlice C R) := by
    intro R hR
    change
      IsClosed
        (weakDualNormSlice
          (linftyWeakStarEquivWeakDual μ ''
            ((toLinftyWeakStar μ) '' LinftyClaims μ D)) R)
    rw [weakDualNormSlice_linftyClaims_eq]
    exact
      (linftyWeakStarEquivWeakDual μ).isClosed_image.mpr
        (isClosed_linftyWeakStar_claimSlice
          hFatou hCone hSolid hR)
  have hCclosed : IsClosed C :=
    isClosed_of_isClosed_weakDualNormSlice hCconvex hCslices
  change
    IsClosed
      ((toLinftyWeakStar μ) '' LinftyClaims μ D)
  exact
    (linftyWeakStarEquivWeakDual μ).isClosed_image.mp hCclosed

theorem linftyWeakStarClosedFromFatouCone_impl
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (D : Set (Ω → ℝ)) :
    LinftyWeakStarClosedFromFatouCone μ D :=
  fun hFatou hCone hSolid =>
    linftyWeakStarClosed_of_fatouCone hFatou hCone hSolid

end FTAPTheorem42
