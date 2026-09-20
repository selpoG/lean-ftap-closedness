/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import Mathlib.Probability.Process.Predictable

/-!
# Restricting predictable processes

Lemma 4.7 restricts integrands to predictable sets and uses the sign of a
predictable finite-variation density.  This file proves the measurable part
of those operations directly in mathlib's predictable sigma algebra.
-/

open MeasureTheory

namespace FTAPTheorem42

variable {Ω Time : Type*}

namespace PredictableProcess

/-- The constant-one predictable process. -/
def unit : Time → Ω → ℝ := fun _ _ => 1

/-- The constant-one process is predictable. -/
theorem isStronglyPredictable_unit
    [MeasurableSpace Ω] [Preorder Time] [OrderBot Time]
    {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)} :
    IsStronglyPredictable ℱ (unit : Time → Ω → ℝ) := by
  exact stronglyMeasurable_const

/-- Restrict a process to a subset of time--sample space. -/
noncomputable def restrict
    (B : Set (Time × Ω)) (H : Time → Ω → ℝ) : Time → Ω → ℝ :=
  fun t ω => B.indicator (Function.uncurry H) (t, ω)

/-- The predictable indicator process of a time--sample set. -/
noncomputable def indicator (B : Set (Time × Ω)) : Time → Ω → ℝ :=
  restrict B unit

@[simp]
theorem restrict_apply_of_mem
    {B : Set (Time × Ω)} {H : Time → Ω → ℝ}
    {t : Time} {ω : Ω} (h : (t, ω) ∈ B) :
    restrict B H t ω = H t ω := by
  simp [restrict, h]

@[simp]
theorem restrict_apply_of_notMem
    {B : Set (Time × Ω)} {H : Time → Ω → ℝ}
    {t : Time} {ω : Ω} (h : (t, ω) ∉ B) :
    restrict B H t ω = 0 := by
  simp [restrict, h]

/-- Restriction to a predictable set preserves predictability. -/
theorem isStronglyPredictable_restrict
    {Ω Time : Type*} [MeasurableSpace Ω]
    [Preorder Time] [OrderBot Time]
    {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}
    {B : Set (Time × Ω)} (hB : MeasurableSet[ℱ.predictable] B)
    {H : Time → Ω → ℝ} (hH : IsStronglyPredictable ℱ H) :
    IsStronglyPredictable ℱ (restrict B H) := by
  change StronglyMeasurable[ℱ.predictable]
    (B.indicator (Function.uncurry H))
  exact hH.indicator hB

/-- A predictable set has a strongly predictable indicator process. -/
theorem isStronglyPredictable_indicator
    {Time : Type*} [MeasurableSpace Ω]
    [Preorder Time] [OrderBot Time]
    {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}
    {B : Set (Time × Ω)} (hB : MeasurableSet[ℱ.predictable] B) :
    IsStronglyPredictable ℱ (indicator B) :=
  isStronglyPredictable_restrict hB isStronglyPredictable_unit

@[simp]
theorem indicator_apply_of_mem
    {B : Set (Time × Ω)} {t : Time} {ω : Ω}
    (h : (t, ω) ∈ B) :
    indicator B t ω = 1 := by
  simp [indicator, unit, h]

@[simp]
theorem indicator_apply_of_notMem
    {B : Set (Time × Ω)} {t : Time} {ω : Ω}
    (h : (t, ω) ∉ B) :
    indicator B t ω = 0 := by
  simp [indicator, h]

theorem abs_indicator_le_one
    (B : Set (Time × Ω)) (t : Time) (ω : Ω) :
    |indicator B t ω| ≤ 1 := by
  classical
  by_cases h : (t, ω) ∈ B <;> simp [indicator, restrict, unit, h]

theorem restrict_add
    (B : Set (Time × Ω)) (H K : Time → Ω → ℝ) :
    restrict B (fun t ω => H t ω + K t ω) =
      fun t ω => restrict B H t ω + restrict B K t ω := by
  funext t ω
  by_cases h : (t, ω) ∈ B <;> simp [restrict, h]

theorem restrict_smul
    (B : Set (Time × Ω)) (c : ℝ) (H : Time → Ω → ℝ) :
    restrict B (fun t ω => c * H t ω) =
      fun t ω => c * restrict B H t ω := by
  funext t ω
  by_cases h : (t, ω) ∈ B <;> simp [restrict, h]

end PredictableProcess

end FTAPTheorem42
