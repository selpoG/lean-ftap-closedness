/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.HilbertConvexification
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # Common Hilbert convexification

Convexify once in a Hilbert direct sum and evaluate the same weights in every
coordinate. Geometric normalization embeds countably many bounded coordinate
sequences without requiring their original bounds to be square summable. -/

namespace FTAPTheorem42

open Filter Topology
open scoped BigOperators ENNReal lp

variable {ι : Type*} {E : ι → Type*}

namespace TailConvexWeights

@[simp]
theorem applyVector_lp_coordinate
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)]
    {n : ℕ} (w : TailConvexWeights n)
    (X : ℕ → lp E (2 : ℝ≥0∞)) (i : ι) :
    (w.applyVector X) i =
      w.applyVector (fun k => X k i) := by
  simp only [TailConvexWeights.applyVector]
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.coeFn_smul, Pi.smul_apply]

/--
One common family of fixed-tail weights convexifies a bounded sequence in the
Hilbert sum `lp E 2` and converges there.  Evaluating the resulting limit at
any coordinate gives coordinatewise convergence under those same weights.

The hypotheses on `E` are exactly the ones used by mathlib's Hilbert-sum
instance and its completeness theorem; no countability assumption on `ι` is
needed by the `lp` construction.
-/
theorem exists_commonLp_tailConvexification
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, CompleteSpace (E i)]
    {X : ℕ → lp E (2 : ℝ≥0∞)} {C : ℝ}
    (hbound : ∀ n, ‖X n‖ ≤ C) (hC : 0 ≤ C) :
    ∃ (w : ∀ n, TailConvexWeights n) (y : lp E (2 : ℝ≥0∞)),
      Tendsto (fun n => (w n).applyVector X) atTop (𝓝 y) ∧
      ∀ i : ι,
        Tendsto (fun n =>
          (w n).applyVector (fun k => X k i)) atTop (𝓝 (y i)) := by
  let w : ∀ n, TailConvexWeights n :=
    TailConvexWeights.tailNormSqNearMinimizers X
  obtain ⟨y, hy⟩ :=
    TailConvexWeights.exists_tendsto_tailNormSqNearMinimizers
      (x := X) hbound hC
  have hy_w :
      Tendsto (fun n => (w n).applyVector X) atTop (𝓝 y) := by
    simpa [w] using hy
  refine ⟨w, y, hy_w, ?_⟩
  intro i
  let proj : lp E (2 : ℝ≥0∞) →L[ℝ] E i :=
    lp.evalCLM (𝕜 := ℝ) (E := E) (p := (2 : ℝ≥0∞)) i
  have hcoord :
      Tendsto
        (fun n => proj ((w n).applyVector X)) atTop (𝓝 (proj y)) := by
    exact proj.continuous.continuousAt.tendsto.comp hy_w
  have h_eval_apply (z : lp E (2 : ℝ≥0∞)) :
      proj z = z i := by
    rfl
  simpa only [h_eval_apply, applyVector_lp_coordinate] using hcoord

end TailConvexWeights

namespace DirectSumCoordinateControl

/-! ### Explicit normalization for countably many coordinates

The common-weight compactness theorem works with one `lp` envelope.  For a
countable family, the following geometric envelope lets us remove the need to
assume that the original coordinate bounds are square-summable.  The factor
`geometricNormalization B i` absorbs the (finite) bound `B i`, while the
remaining envelope decays geometrically in `i`.
-/

noncomputable def geometricScale (i : ℕ) : ℝ := ((1 : ℝ) / 2) ^ i

theorem geometricScale_nonneg (i : ℕ) : 0 ≤ geometricScale i := by
  unfold geometricScale
  positivity

theorem geometricScale_pos (i : ℕ) : 0 < geometricScale i := by
  unfold geometricScale
  positivity

theorem geometricScale_summable : Summable geometricScale := by
  change Summable (fun n : ℕ => ((1 : ℝ) / 2) ^ n)
  exact summable_geometric_two

theorem geometricScale_memℓp :
    Memℓp geometricScale (2 : ℝ≥0∞) := by
  apply memℓp_gen
  refine geometricScale_summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_)
  · positivity
  · have hsq : geometricScale i ^ 2 ≤ geometricScale i := by
      have hi0 := geometricScale_nonneg i
      have hi1 : geometricScale i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    simpa [Real.norm_eq_abs, abs_of_nonneg (geometricScale_nonneg i)] using hsq

noncomputable def geometricLpEnvelope : lp (fun _ : ℕ => ℝ) (2 : ℝ≥0∞) :=
  ⟨geometricScale, geometricScale_memℓp⟩

noncomputable def geometricNormalization (B : ℕ → ℝ) (i : ℕ) : ℝ :=
  geometricScale i / (B i + 1)

theorem geometricNormalization_pos (B : ℕ → ℝ) (hB : ∀ i, 0 ≤ B i)
    (i : ℕ) : 0 < geometricNormalization B i := by
  unfold geometricNormalization
  have hden : 0 < B i + 1 := by linarith [hB i]
  exact div_pos (geometricScale_pos i) hden

theorem geometricNormalization_ne_zero (B : ℕ → ℝ) (hB : ∀ i, 0 ≤ B i)
    (i : ℕ) : geometricNormalization B i ≠ 0 :=
  (geometricNormalization_pos B hB i).ne'

noncomputable def normalizeCoordinates {E : ℕ → Type*} [∀ i, AddCommMonoid (E i)]
    [∀ i, Module ℝ (E i)] (B : ℕ → ℝ)
    (Z : ℕ → ∀ i, E i) :
    ℕ → ∀ i, E i :=
  fun n i => geometricNormalization B i • Z n i

theorem normalizeCoordinates_norm_le
    {E : ℕ → Type*}
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)]
    (B : ℕ → ℝ) (Z : ℕ → ∀ i, E i)
    (hB : ∀ i, 0 ≤ B i)
    (hZ : ∀ n i, ‖Z n i‖ ≤ B i) (n i : ℕ) :
    ‖normalizeCoordinates B Z n i‖ ≤ geometricScale i := by
  have hα : 0 < geometricNormalization B i := geometricNormalization_pos B hB i
  have hα0 : 0 ≤ geometricNormalization B i := hα.le
  have hden : 0 < B i + 1 := by linarith [hB i]
  have hscaled :
      geometricScale i * B i / (B i + 1) ≤ geometricScale i := by
    apply (div_le_iff₀ hden).2
    exact mul_le_mul_of_nonneg_left (by linarith [hB i])
      (geometricScale_nonneg i)
  calc
    ‖normalizeCoordinates B Z n i‖ =
        ‖geometricNormalization B i‖ * ‖Z n i‖ := by
          rw [normalizeCoordinates, norm_smul]
    _ = geometricNormalization B i * ‖Z n i‖ := by
          rw [Real.norm_eq_abs, abs_of_pos hα]
    _ ≤ geometricNormalization B i * B i :=
          mul_le_mul_of_nonneg_left (hZ n i) hα0
    _ = geometricScale i * B i / (B i + 1) := by
          unfold geometricNormalization
          ring
    _ ≤ geometricScale i := hscaled

/- The finite-sum convexification commutes with multiplication by one fixed
scalar.  This is the bridge from normalized coordinates back to the original
coordinates. -/
theorem TailConvexWeights.applyVector_const_smul
    {F : Type*} [AddCommMonoid F] [Module ℝ F]
    (w : TailConvexWeights n) (a : ℝ) (x : ℕ → F) :
    w.applyVector (fun k => a • x k) = a • w.applyVector x := by
  classical
  simp only [TailConvexWeights.applyVector]
  calc
    (∑ i ∈ w.support, w.weight i • (a • x i)) =
        ∑ i ∈ w.support, a • (w.weight i • x i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [smul_smul, smul_smul, mul_comm]
    _ = a • ∑ i ∈ w.support, w.weight i • x i := by
      rw [Finset.smul_sum]

/--
Turn raw coordinates into a genuine `lp E 2` sequence using a scalar `lp`
envelope.  The pointwise domination hypothesis is the only integrability input
needed by `Memℓp.mono`.
-/
def coordinateToLp
    [∀ i, NormedAddCommGroup (E i)]
    (b : lp (fun _ : ι => ℝ) (2 : ℝ≥0∞))
    (Z : ℕ → ∀ i, E i)
    (hZ : ∀ n i, ‖Z n i‖ ≤ b i) :
    ℕ → lp E (2 : ℝ≥0∞) :=
  fun n => ⟨Z n, (lp.memℓp b).mono (fun i => hZ n i)⟩

@[simp]
theorem coordinateToLp_apply
    [∀ i, NormedAddCommGroup (E i)]
    (b : lp (fun _ : ι => ℝ) (2 : ℝ≥0∞))
    (Z : ℕ → ∀ i, E i)
    (hZ : ∀ n i, ‖Z n i‖ ≤ b i) (n : ℕ) (i : ι) :
    coordinateToLp b Z hZ n i = Z n i :=
  rfl

/-- The scalar envelope bounds every direct-sum term in norm. -/
theorem coordinateToLp_norm_le
    [∀ i, NormedAddCommGroup (E i)]
    (b : lp (fun _ : ι => ℝ) (2 : ℝ≥0∞))
    (Z : ℕ → ∀ i, E i)
    (hb : ∀ i, 0 ≤ b i)
    (hZ : ∀ n i, ‖Z n i‖ ≤ b i) (n : ℕ) :
    ‖coordinateToLp b Z hZ n‖ ≤ ‖b‖ := by
  refine lp.norm_mono (E := E) (F := fun _ : ι => ℝ)
    (p := (2 : ℝ≥0∞)) (by norm_num) ?_
  intro i
  rw [coordinateToLp_apply]
  calc
    ‖Z n i‖ ≤ b i := hZ n i
    _ = ‖b i‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (hb i)]

/--
Construct one coordinate-independent convexification from a scalar `lp`
envelope.  The output gives convergence in the direct sum and, under the same
weights, convergence of every raw coordinate sequence to the corresponding
coordinate of the direct-sum limit.
-/
theorem exists_commonLp_tailConvexification_of_coordinateEnvelope
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, CompleteSpace (E i)]
    (b : lp (fun _ : ι => ℝ) (2 : ℝ≥0∞))
    (Z : ℕ → ∀ i, E i)
    (hb : ∀ i, 0 ≤ b i)
    (hZ : ∀ n i, ‖Z n i‖ ≤ b i) :
    ∃ (w : ∀ n, TailConvexWeights n)
      (y : lp E (2 : ℝ≥0∞)),
      Tendsto
          (fun n =>
            (w n).applyVector (coordinateToLp b Z hZ))
          atTop (𝓝 y) ∧
      ∀ i : ι,
        Tendsto
          (fun n => (w n).applyVector (fun k => Z k i))
          atTop (𝓝 (y i)) := by
  let X : ℕ → lp E (2 : ℝ≥0∞) := coordinateToLp b Z hZ
  obtain ⟨w, y, hX, hcoord⟩ :=
    TailConvexWeights.exists_commonLp_tailConvexification
      (X := X) (C := ‖b‖)
      (fun n => coordinateToLp_norm_le b Z hb hZ n)
      (norm_nonneg b)
  refine ⟨w, y, ?_, ?_⟩
  · simpa [X] using hX
  · intro i
    simpa [X] using hcoord i

/-!
The normalized coordinates have one common sequence of tail convex weights.
After applying the inverse of the positive coordinate factor, those same
weights converge in every original coordinate to the explicitly rescaled
limit.  No square-summability assumption is made on `B`.
-/
theorem exists_common_tailConvexification_of_finite_coordinateBounds
    {E : ℕ → Type*}
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, CompleteSpace (E i)]
    (B : ℕ → ℝ) (Z : ℕ → ∀ i, E i)
    (hB : ∀ i, 0 ≤ B i)
    (hZ : ∀ n i, ‖Z n i‖ ≤ B i) :
    ∃ (w : ∀ n, TailConvexWeights n)
      (y : lp E (2 : ℝ≥0∞)),
      Tendsto
          (fun n =>
            (w n).applyVector
              (coordinateToLp geometricLpEnvelope (normalizeCoordinates B Z)
                (fun n i => by
                  exact
                    normalizeCoordinates_norm_le B Z hB hZ n i)))
          atTop (𝓝 y) ∧
      ∀ i : ℕ,
        Tendsto
          (fun n => (w n).applyVector (fun k => Z k i))
          atTop
          (𝓝 ((geometricNormalization B i)⁻¹ • y i)) := by
  have hnorm :
      ∀ n i, ‖normalizeCoordinates B Z n i‖ ≤ geometricLpEnvelope i := by
    intro n i
    exact
      normalizeCoordinates_norm_le B Z hB hZ n i
  obtain ⟨w, y, hX, hcoord⟩ :=
    exists_commonLp_tailConvexification_of_coordinateEnvelope
      (b := geometricLpEnvelope) (Z := normalizeCoordinates B Z)
      (hb := fun i => (geometricScale_nonneg i)) hnorm
  refine ⟨w, y, hX, ?_⟩
  intro i
  have hscaled :
      Tendsto
        (fun n => geometricNormalization B i •
          (w n).applyVector (fun k => Z k i))
        atTop (𝓝 (y i)) := by
    simpa only [normalizeCoordinates,
      TailConvexWeights.applyVector_const_smul] using hcoord i
  have hinv := hscaled.const_smul (geometricNormalization B i)⁻¹
  simpa only [smul_smul,
    inv_mul_cancel₀ (geometricNormalization_ne_zero B hB i), one_smul] using hinv

end DirectSumCoordinateControl

end FTAPTheorem42
