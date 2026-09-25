/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.Process
import FTAPTheorem42.Foundations.FiniteVariationStoppedPath

/-! # Variation shared by the analytic interface and its implementation -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal ProbabilityTheory BigOperators

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Cumulative path variation on each finite time interval. -/
noncomputable def localVariation (Q : Process Ω) : Process Ω :=
  fun t omega => variationOnFromTo (Q · omega) univ 0 t

/-! ## Pathwise bounded-variation negation -/

/-- Negation preserves path variation. -/
theorem pathVariation_neg {Time : Type*} [LinearOrder Time]
    (f : Time → ℝ) (s : Set Time) :
    eVariationOn (fun t => -f t) s = eVariationOn f s := by
  simp only [eVariationOn, edist_neg_neg]

/-- Subtracting a constant preserves path variation. -/
theorem pathVariation_sub_const {Time : Type*} [LinearOrder Time]
    (f : Time → ℝ) (c : ℝ) (s : Set Time) :
    eVariationOn (fun t => f t - c) s = eVariationOn f s := by
  simp only [eVariationOn, edist_sub_right]

/-- Adding a constant preserves path variation. -/
theorem pathVariation_add_const {Time : Type*} [LinearOrder Time]
    {f : Time → ℝ} (c : ℝ) (s : Set Time) :
    eVariationOn (fun t => f t + c) s = eVariationOn f s := by
  simp only [eVariationOn, edist_add_right]

theorem boundedVariationOn_neg
    {Time : Type*} [LinearOrder Time]
    {f : Time → ℝ} {s : Set Time}
    (hf : BoundedVariationOn f s) :
    BoundedVariationOn (fun t => -f t) s := by
  change eVariationOn (fun t => -f t) s ≠ ∞
  rw [pathVariation_neg]
  exact hf

theorem boundedVariationOn_add
    {Time : Type*} [LinearOrder Time]
    {f g : Time → ℝ} {s : Set Time}
    (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (fun t => f t + g t) s := by
  change eVariationOn f s ≠ ∞ at hf
  change eVariationOn g s ≠ ∞ at hg
  change eVariationOn (fun t => f t + g t) s ≠ ∞
  apply ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩)
  rw [eVariationOn]
  apply iSup_le
  rintro ⟨n, u, hu, us⟩
  calc
    (∑ i ∈ Finset.range n,
        edist (f (u (i + 1)) + g (u (i + 1)))
          (f (u i) + g (u i)))
        ≤ ∑ i ∈ Finset.range n,
          (edist (f (u (i + 1))) (f (u i)) +
            edist (g (u (i + 1))) (g (u i))) := by
      apply Finset.sum_le_sum
      intro i hi
      exact edist_add_add_le _ _ _ _
    _ = (∑ i ∈ Finset.range n,
          edist (f (u (i + 1))) (f (u i))) +
        ∑ i ∈ Finset.range n,
          edist (g (u (i + 1))) (g (u i)) := by
      rw [Finset.sum_add_distrib]
    _ ≤ eVariationOn f s + eVariationOn g s := by
      exact add_le_add (eVariationOn.sum_le hu us)
        (eVariationOn.sum_le hu us)

/-- Total variation up to a finite horizon, defined by stopping a locally
finite-variation path. No bound on variation over the infinite time axis is required. -/
noncomputable def finiteHorizonPathVariation
    (A : Process Ω) (hA : ∀ w, LocallyBoundedVariationOn (A · w) univ)
    (T : NNReal) (w : Ω) : Real :=
  (FiniteVariationPath.signedMeasure
    (FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn
      (hA w) T)).totalVariation.real univ

omit [MeasurableSpace Ω] in
/-- Identify the stopped Stieltjes variation with the original path variation
on the same compact horizon. -/
theorem finiteHorizonPathVariation_eq_eVariationOn
    (A : Process Ω) (hA : ∀ ω, LocallyBoundedVariationOn (A · ω) univ)
    (hAR : ∀ ω t, ContinuousWithinAt (A · ω) (Ici t) t)
    (T : NNReal) (ω : Ω) :
    finiteHorizonPathVariation A hA T ω = (eVariationOn (A · ω) (Icc 0 T)).toReal := by
  let B := FiniteVariationStoppedPath.stopAt (A · ω) T
  have hB : BoundedVariationOn B univ :=
    FiniteVariationStoppedPath.boundedVariationOn_stopAt_of_locallyBoundedVariationOn (hA ω) T
  have hBR := FiniteVariationStoppedPath.rightContinuous_stopAt (A · ω) (hAR ω) T
  have hTotal := FiniteVariationStoppedPath.totalVariation_univ_stopAt B hB hBR T
  have hBStop : FiniteVariationStoppedPath.stopAt B T = B := by
    funext t
    simp only [B, FiniteVariationStoppedPath.stopAt, min_assoc, min_self]
  have hCongr (f g : NNReal → Real) (hf : BoundedVariationOn f univ)
      (hg : BoundedVariationOn g univ) (heq : f = g) :
      FiniteVariationPath.signedMeasure hf = FiniteVariationPath.signedMeasure hg := by
    subst g
    rfl
  rw [hCongr _ _ _ hB hBStop,
    variationOnFromTo.eq_of_le B univ (show (0 : NNReal) ≤ T from zero_le), univ_inter] at hTotal
  unfold finiteHorizonPathVariation
  change ((FiniteVariationPath.signedMeasure hB).totalVariation univ).toReal = _
  rw [hTotal, ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
  congr 1
  apply eVariationOn.congr
  intro t ht
  exact congrArg (A · ω) (min_eq_left ht.2)

end FTAPTheorem42
