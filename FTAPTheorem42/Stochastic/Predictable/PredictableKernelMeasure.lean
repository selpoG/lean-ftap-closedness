/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Predictable.PredictableHahnDecomposition
import Mathlib.MeasureTheory.Measure.Trim
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Predictable signed measures from finite kernels

A random finite measure on time is represented by a finite kernel from the
sample space to time.  This file integrates such kernels against the base
measure, swaps the coordinates into time--sample order, and trims the result
to the predictable sigma algebra.  Taking the difference of two finite
kernels then gives the predictable signed measure to which the Hahn
decomposition applies.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω Time : Type*} [MeasurableSpace Ω]
  [MeasurableSpace Time] [LinearOrder Time] [OrderBot Time]
  [TopologicalSpace Time] [OpensMeasurableSpace Time]
  [OrderClosedTopology Time]

namespace PredictableKernelMeasure

/-- The predictable sigma algebra is contained in the product sigma algebra. -/
theorem predictable_le_prod
    (ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)) :
    ℱ.predictable ≤
      (inferInstance : MeasurableSpace (Time × Ω)) := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro B (⟨A, hA, rfl⟩ | ⟨t, A, hA, rfl⟩)
  · exact isClosed_singleton.measurableSet.prod (ℱ.le ⊥ A hA)
  · exact isOpen_Ioi.measurableSet.prod (ℱ.le t A hA)

/-- Integrate a time-valued kernel against the base measure and put time in
the first coordinate. -/
noncomputable def swappedCompProd
    (μ : Measure Ω) (κ : Kernel Ω Time) : Measure (Time × Ω) :=
  (μ ⊗ₘ κ).map Prod.swap

omit [LinearOrder Time] [OrderBot Time] [TopologicalSpace Time]
  [OpensMeasurableSpace Time] [OrderClosedTopology Time] in
/-- Evaluation of the swapped composition-product on a measurable set. -/
theorem swappedCompProd_apply
    {μ : Measure Ω} {κ : Kernel Ω Time}
    [SFinite μ] [IsSFiniteKernel κ]
    {B : Set (Time × Ω)} (hB : MeasurableSet B) :
    swappedCompProd μ κ B =
      ∫⁻ ω, κ ω ((fun t => (t, ω)) ⁻¹' B) ∂μ := by
  rw [swappedCompProd, Measure.map_apply measurable_swap hB,
    Measure.compProd_apply (measurable_swap hB)]
  rfl

/-- The joint kernel measure restricted to the predictable sigma algebra. -/
noncomputable def predictableMeasure
    (ℱ : Filtration Time (inferInstance : MeasurableSpace Ω))
    (μ : Measure Ω) (κ : Kernel Ω Time) :
    @Measure (Time × Ω) ℱ.predictable :=
  (swappedCompProd μ κ).trim (predictable_le_prod ℱ)

noncomputable instance predictableMeasure.instIsFiniteMeasure
    (ℱ : Filtration Time (inferInstance : MeasurableSpace Ω))
    (μ : Measure Ω) (κ : Kernel Ω Time)
    [IsFiniteMeasure μ] [IsFiniteKernel κ] :
    IsFiniteMeasure (predictableMeasure ℱ μ κ) := by
  unfold predictableMeasure swappedCompProd
  infer_instance

/-- Evaluation of a predictable kernel measure before taking real parts. -/
theorem predictableMeasure_apply
    {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} {κ : Kernel Ω Time}
    [SFinite μ] [IsSFiniteKernel κ]
    {B : Set (Time × Ω)} (hB : MeasurableSet[ℱ.predictable] B) :
    predictableMeasure ℱ μ κ B =
      ∫⁻ ω, κ ω ((fun t => (t, ω)) ⁻¹' B) ∂μ := by
  rw [predictableMeasure, trim_measurableSet_eq (predictable_le_prod ℱ) hB]
  exact swappedCompProd_apply ((predictable_le_prod ℱ) B hB)

/-- A nonnegative predictable integral against an integrated kernel is the
corresponding iterated path integral. -/
theorem lintegral_predictableMeasure_eq_lintegral_kernel
    {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} {κ : Kernel Ω Time}
    [SFinite μ] [IsSFiniteKernel κ]
    {f : Time × Ω → ℝ≥0∞} (hf : Measurable[ℱ.predictable] f) :
    (∫⁻ p, f p ∂predictableMeasure ℱ μ κ) =
      ∫⁻ ω, ∫⁻ t, f (t, ω) ∂κ ω ∂μ := by
  have hfProd : Measurable f :=
    hf.mono (predictable_le_prod ℱ) le_rfl
  have hfSwap : Measurable (fun p : Ω × Time => f p.swap) :=
    hfProd.comp measurable_swap
  rw [predictableMeasure,
    lintegral_trim (predictable_le_prod ℱ) hf,
    swappedCompProd, lintegral_map hfProd measurable_swap,
    Measure.lintegral_compProd hfSwap]
  rfl

/-- The predictable measure construction preserves addition of kernels. -/
theorem predictableMeasure_add
    {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} (κ η : Kernel Ω Time)
    [SFinite μ] [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    predictableMeasure ℱ μ (κ + η) =
      predictableMeasure ℱ μ κ + predictableMeasure ℱ μ η := by
  unfold predictableMeasure swappedCompProd
  rw [Measure.compProd_add_right,
    Measure.map_add (μ ⊗ₘ κ) (μ ⊗ₘ η) measurable_swap, trim_add]

/-- The predictable signed measure obtained from the difference of two finite
random time measures. -/
noncomputable def signedMeasure
    (ℱ : Filtration Time (inferInstance : MeasurableSpace Ω))
    (μ : Measure Ω) (κp κn : Kernel Ω Time)
    [IsFiniteMeasure μ] [IsFiniteKernel κp] [IsFiniteKernel κn] :
    PredictableSignedMeasure.Measure ℱ :=
  (predictableMeasure ℱ μ κp).toSignedMeasure -
    (predictableMeasure ℱ μ κn).toSignedMeasure

end PredictableKernelMeasure

end FTAPTheorem42
