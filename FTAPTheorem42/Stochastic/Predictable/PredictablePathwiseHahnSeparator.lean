/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableDoleansRigidity

/-!
# Predictable pathwise Hahn separators

The Lemma 4.7 restriction argument only needs a predictable set whose time
sections separate the positive and negative Jordan parts of the
finite-variation path measure.  This file isolates that data from the
stronger normalized finite-kernel bridge used to construct one.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A predictable set whose time sections are Hahn positive sets for the
finite-variation component, outside one common null set. -/
structure PredictablePathwiseHahnSeparator
    {S : Process Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω}
    {D : SpecialSemimartingaleDecomposition S ℱ μ}
    (L : SIntegrableStrategy D) where
  positiveSet : Set (ℝ≥0 × Ω)
  measurableSet_positiveSet : MeasurableSet[ℱ.predictable] positiveSet
  separatesJordan_ae :
    ∀ᵐ ω ∂μ,
      FiniteVariationKernel.negativePathMeasure
          L.finiteVariationPart_isBoundedVariation ω
          (PredictableFiniteVariationRestriction.timeSection positiveSet ω) = 0 ∧
        FiniteVariationKernel.positivePathMeasure
          L.finiteVariationPart_isBoundedVariation ω
          (PredictableFiniteVariationRestriction.timeSection positiveSet ω)ᶜ = 0

namespace SIntegrableFiniteVariationBridge

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}
  {L : SIntegrableStrategy D}

/-- The normalized Doléans--Dade construction supplies the pathwise Hahn data
consumed by the Lemma 4.7 restriction argument. -/
noncomputable def toPredictablePathwiseHahnSeparator
    (E : SIntegrableFiniteVariationBridge L) :
    PredictablePathwiseHahnSeparator L where
  positiveSet := E.predictableHahnDecomposition.positiveSet
  measurableSet_positiveSet :=
    E.predictableHahnDecomposition.measurableSet_positiveSet
  separatesJordan_ae := by
    filter_upwards [
      E.predictableHahnDecomposition_separates_canonicalKernels_ae
        E.canonicalMeasure_totalVariationMass_eq_kernelMass] with ω hω
    have hDensity : (E.referenceDensity ω : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (E.referenceDensity_pos ω).ne'
    constructor
    · have hScaled := hω.1
      rw [canonicalNegativeKernel_apply, Measure.smul_apply] at hScaled
      exact (mul_eq_zero.mp hScaled).resolve_left hDensity
    · have hScaled := hω.2
      rw [canonicalPositiveKernel_apply, Measure.smul_apply] at hScaled
      exact (mul_eq_zero.mp hScaled).resolve_left hDensity

end SIntegrableFiniteVariationBridge

namespace SIntegrableStrategy

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- Every realized finite-variation component supplies the predictable
pathwise Hahn separator used by Lemma 4.7.  The construction internally
normalizes path variation by a strictly positive sample density; it requires
no deterministic common variation bound. -/
noncomputable def predictablePathwiseHahnSeparator
    (L : SIntegrableStrategy D) :
    PredictablePathwiseHahnSeparator L :=
  (SIntegrableFiniteVariationBridge.ofCumulativeVariationNormalized
    L.finiteVariationPart_isRightContinuous).toPredictablePathwiseHahnSeparator

end SIntegrableStrategy

end FTAPTheorem42
