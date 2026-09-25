/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.FiniteVariationStoppedPath
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-!
# Stieltjes measures under pathwise stopping

Stopping a right-continuous finite-variation path at a finite time restricts
its signed Stieltjes measure, and hence its Jordan total variation, to the
stochastic interval `(0, τ]`.  These pathwise identities transfer both
integrability and signed-density representations to a stopped path.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace FTAPTheorem42.FiniteVariationStoppedPath

/-- Restriction commutes with a vector-valued density. -/
theorem restrict_withDensityᵥ
    {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ν : Measure X) {f : X → E} (hf : Integrable f ν)
    {s : Set X} (hs : MeasurableSet s) :
    (ν.withDensityᵥ f).restrict s = (ν.restrict s).withDensityᵥ f := by
  ext t ht
  rw [VectorMeasure.restrict_apply _ hs ht,
    withDensityᵥ_apply hf (ht.inter hs),
    withDensityᵥ_apply hf.restrict ht]
  rw [Measure.restrict_restrict ht]

/-- The signed Stieltjes measure of a stopped right-continuous path is the
restriction of the original measure to `(0, τ]`. -/
theorem signedMeasure_stopAt_eq_restrict_Ioc
    (A : ℝ≥0 → ℝ) (hA : BoundedVariationOn A Set.univ)
    (hRight : ∀ t, ContinuousWithinAt A (Set.Ici t) t)
    (τ : ℝ≥0) :
    FiniteVariationPath.signedMeasure (boundedVariationOn_stopAt hA τ) =
      (FiniteVariationPath.signedMeasure hA).restrict (Set.Ioc 0 τ) := by
  apply FiniteVariationPath.signedMeasure_ext_of_Ioc_univ
  · intro a b hab
    rw [FiniteVariationPath.signedMeasure_Ioc
      (boundedVariationOn_stopAt hA τ)
      (rightContinuous_stopAt A hRight τ) hab]
    rw [VectorMeasure.restrict_apply _ measurableSet_Ioc measurableSet_Ioc]
    by_cases hτa : τ ≤ a
    · have hInter : Set.Ioc a b ∩ Set.Ioc 0 τ = ∅ := by
        ext t
        simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_empty_iff_false,
          iff_false]
        exact fun ht => (not_lt_of_ge hτa) (ht.1.1.trans_le ht.2.2)
      rw [hInter]
      simp [stopAt, min_eq_right hτa, min_eq_right (hτa.trans hab)]
    · have haτ : a ≤ τ := (lt_of_not_ge hτa).le
      have hInter : Set.Ioc a b ∩ Set.Ioc 0 τ = Set.Ioc a (min b τ) := by
        ext t
        simp only [Set.mem_inter_iff, Set.mem_Ioc]
        constructor
        · rintro ⟨⟨hat, htb⟩, ⟨_h0t, htτ⟩⟩
          exact ⟨hat, le_min htb htτ⟩
        · rintro ⟨hat, ht⟩
          exact ⟨⟨hat, ht.trans (min_le_left b τ)⟩,
            ⟨(bot_le : (0 : ℝ≥0) ≤ a).trans_lt hat,
              ht.trans (min_le_right b τ)⟩⟩
      rw [hInter, FiniteVariationPath.signedMeasure_Ioc hA hRight
        (le_min hab haτ)]
      simp only [stopAt, min_eq_left haτ]
  · rw [signedMeasure_univ_stopAt A τ (boundedVariationOn_stopAt hA τ)]
    rw [VectorMeasure.restrict_apply _ measurableSet_Ioc MeasurableSet.univ,
      Set.univ_inter]
    exact (FiniteVariationPath.signedMeasure_Ioc hA hRight bot_le).symm

/-- Jordan total variation is restricted by the same stopped interval. -/
theorem totalVariation_stopAt_eq_restrict_Ioc
    (A : ℝ≥0 → ℝ) (hA : BoundedVariationOn A Set.univ)
    (hRight : ∀ t, ContinuousWithinAt A (Set.Ici t) t)
    (τ : ℝ≥0) :
    (FiniteVariationPath.signedMeasure
      (boundedVariationOn_stopAt hA τ)).totalVariation =
        (FiniteVariationPath.signedMeasure hA).totalVariation.restrict
          (Set.Ioc 0 τ) := by
  rw [signedMeasure_totalVariation_eq_variation,
    signedMeasure_stopAt_eq_restrict_Ioc A hA hRight τ,
    VectorMeasure.variation_restrict measurableSet_Ioc,
    ← signedMeasure_totalVariation_eq_variation]

/-- Integrability against path variation is preserved by stopping. -/
theorem integrable_totalVariation_stopAt
    (A : ℝ≥0 → ℝ) (hA : BoundedVariationOn A Set.univ)
    (hRight : ∀ t, ContinuousWithinAt A (Set.Ici t) t)
    (τ : ℝ≥0) {f : ℝ≥0 → ℝ}
    (hf : Integrable f
      (FiniteVariationPath.signedMeasure hA).totalVariation) :
    Integrable f (FiniteVariationPath.signedMeasure
      (boundedVariationOn_stopAt hA τ)).totalVariation := by
  rw [totalVariation_stopAt_eq_restrict_Ioc A hA hRight τ]
  exact hf.restrict

/-- A Stieltjes density identity is preserved when both paths are stopped
at the same finite time. -/
theorem withDensityᵥ_stopAt_eq
    (A B : ℝ≥0 → ℝ)
    (hA : BoundedVariationOn A Set.univ)
    (hB : BoundedVariationOn B Set.univ)
    (hARight : ∀ t, ContinuousWithinAt A (Set.Ici t) t)
    (hBRight : ∀ t, ContinuousWithinAt B (Set.Ici t) t)
    (τ : ℝ≥0) {f : ℝ≥0 → ℝ}
    (hf : Integrable f
      (FiniteVariationPath.signedMeasure hA).totalVariation)
    (hDensity :
      (FiniteVariationPath.signedMeasure hA).totalVariation.withDensityᵥ f =
        FiniteVariationPath.signedMeasure hB) :
    (FiniteVariationPath.signedMeasure
      (boundedVariationOn_stopAt hA τ)).totalVariation.withDensityᵥ f =
        FiniteVariationPath.signedMeasure
          (boundedVariationOn_stopAt hB τ) := by
  rw [totalVariation_stopAt_eq_restrict_Ioc A hA hARight τ,
    signedMeasure_stopAt_eq_restrict_Ioc B hB hBRight τ,
    ← restrict_withDensityᵥ
      (FiniteVariationPath.signedMeasure hA).totalVariation hf
        measurableSet_Ioc,
    hDensity]

end FTAPTheorem42.FiniteVariationStoppedPath
