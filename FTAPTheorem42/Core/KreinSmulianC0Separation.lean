/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Core.KreinSmulianC0
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Separation of the Krein--Šmulian `c₀` image

The finite-polar evaluation sends the convex set under consideration outside
the closed unit ball of a `c₀` space.  This module separates that image from
the open unit ball by a continuous linear functional.  The resulting
functional is the input to the coefficient representation step.
-/

open Topology

namespace FTAPTheorem42

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {C : Set (WeakDual ℝ E)}

namespace KreinSmulianFinitePolarTower

variable (T : KreinSmulianFinitePolarTower C)

private abbrev C0 :=
  ZeroAtInftyContinuousMap (KreinSmulianPolarIndex T) ℝ

/-- The strong-dual realization of `C` is convex. -/
theorem convex_strongDual_preimage
    (hC : Convex ℝ C) :
    Convex ℝ (StrongDual.toWeakDual ⁻¹' C) := by
  exact hC.linear_preimage
    (NormedSpace.Dual.continuousLinearMapToWeakDual
      (𝕜 := ℝ) (E := E)).toLinearMap

/-- The image of `C` under the finite-polar evaluation operator is convex. -/
theorem convex_polarEvaluation_image
    (hC : Convex ℝ C) :
    Convex ℝ
      (T.polarEvaluationCLM ''
        (StrongDual.toWeakDual ⁻¹' C)) := by
  exact (convex_strongDual_preimage hC).linear_image
    T.polarEvaluationCLM.toLinearMap

/-- The open unit ball of `c₀` is disjoint from the finite-polar evaluation
image of `C`. -/
theorem disjoint_ball_polarEvaluation_image :
    Disjoint
      (Metric.ball (0 : C0 T) 1)
      (T.polarEvaluationCLM ''
        (StrongDual.toWeakDual ⁻¹' C)) := by
  rw [Set.disjoint_left]
  intro z hz hzimage
  obtain ⟨φ, hφC, rfl⟩ := hzimage
  have hφC' :
      StrongDual.toWeakDual φ ∈ C :=
    hφC
  have hout :
      1 <
        ‖T.polarEvaluationC0
          (StrongDual.toWeakDual φ)‖ :=
    T.one_lt_norm_polarEvaluationC0_of_mem hφC'
  have hin :
      ‖T.polarEvaluationCLM φ‖ < 1 := by
    simpa only [mem_ball_zero_iff] using hz
  exact (not_lt_of_ge hout.le) hin

/-- Hahn--Banach separation of the open unit ball from the finite-polar
evaluation image.  The separator has a strictly positive threshold because
the open ball contains zero. -/
theorem exists_c0_separator
    (hC : Convex ℝ C) :
    ∃ (Λ : StrongDual ℝ (C0 T)) (u : ℝ),
      0 < u ∧
      (∀ z : C0 T, ‖z‖ < 1 → Λ z < u) ∧
      ∀ φ : StrongDual ℝ E,
        StrongDual.toWeakDual φ ∈ C →
          u ≤ Λ (T.polarEvaluationCLM φ) := by
  obtain ⟨Λ, u, hball, himage⟩ :=
    geometric_hahn_banach_open
      (convex_ball (0 : C0 T) 1)
      Metric.isOpen_ball
      (T.convex_polarEvaluation_image hC)
      T.disjoint_ball_polarEvaluation_image
  have hzero :
      (0 : C0 T) ∈ Metric.ball (0 : C0 T) 1 := by
    simp
  refine ⟨Λ, u, ?_, ?_, ?_⟩
  · simpa using hball 0 hzero
  · intro z hz
    exact hball z (by simpa only [mem_ball_zero_iff] using hz)
  · intro φ hφ
    exact himage (T.polarEvaluationCLM φ)
      ⟨φ, hφ, rfl⟩

end KreinSmulianFinitePolarTower

end FTAPTheorem42
