/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableDoleansResidual
import FTAPTheorem42.Stochastic.Predictable.PredictableIntervalElementaryLinearization
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableCumulativeVariationBridge
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableDoleansDensity

/-! # Canonical variation control

The predictable variation measure satisfies a nonnegative Fubini formula
for the weighted pathwise Jordan variation and gives no mass to time zero. -/

namespace FTAPTheorem42

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrableFiniteVariationBridge

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}
  {H : SIntegrableStrategy D}

/-- A nonnegative predictable integral against the canonical variation
measure is the weighted iterated integral against pathwise Jordan variation. -/
theorem lintegral_canonicalVariationMeasure_eq_lintegral_pathVariation
    (E : SIntegrableFiniteVariationBridge H)
    {g : ℝ≥0 × Ω → ℝ≥0∞}
    (hg : Measurable[ℱ.predictable] g) :
    (∫⁻ p, g p ∂canonicalVariationMeasure E) =
      ∫⁻ ω, (E.referenceDensity ω : ℝ≥0∞) *
        ∫⁻ t, g (t, ω)
          ∂(FiniteVariationPath.signedMeasure
            (H.finiteVariationPart_isBoundedVariation ω)).totalVariation ∂μ := by
  let κ := canonicalTotalVariationKernel E
  let : IsFiniteKernel κ :=
    canonicalTotalVariationKernel.instIsFiniteKernel E
  have hgProduct : Measurable g :=
    hg.mono (PredictableKernelMeasure.predictable_le_prod ℱ) le_rfl
  rw [← predictableMeasure_canonicalTotalVariationKernel_eq E]
  change (∫⁻ p, g p ∂
      (PredictableKernelMeasure.swappedCompProd μ κ).trim
        (PredictableKernelMeasure.predictable_le_prod ℱ)) = _
  rw [lintegral_trim (PredictableKernelMeasure.predictable_le_prod ℱ) hg]
  change (∫⁻ p, g p ∂Measure.map Prod.swap (μ ⊗ₘ κ)) = _
  rw [lintegral_map hgProduct measurable_swap]
  have hSwap : Measurable (fun p : Ω × ℝ≥0 => g p.swap) :=
    hgProduct.comp measurable_swap
  calc
    (∫⁻ p : Ω × ℝ≥0, g p.swap ∂μ ⊗ₘ κ) =
        ∫⁻ ω, ∫⁻ t, g (t, ω) ∂κ ω ∂μ := by
      simpa only [Prod.swap_prod_mk] using
        (Measure.lintegral_compProd hSwap)
    _ = ∫⁻ ω, (E.referenceDensity ω : ℝ≥0∞) *
        ∫⁻ t, g (t, ω)
          ∂(FiniteVariationPath.signedMeasure
            (H.finiteVariationPart_isBoundedVariation ω)).totalVariation ∂μ := by
      apply lintegral_congr
      intro ω
      rw [canonicalTotalVariationKernel_apply, lintegral_smul_measure]
      rfl

end SIntegrableFiniteVariationBridge

end FTAPTheorem42

namespace FTAPTheorem42

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega]

namespace SIntegrableFiniteVariationBridge

variable {S : Process Omega}
  {F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsFiniteMeasure mu]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {H : SIntegrableStrategy D}

private theorem canonicalPositiveKernel_singleton_zero
    (E : SIntegrableFiniteVariationBridge H) (omega : Omega) :
    canonicalPositiveKernel E omega ({0} : Set ℝ≥0) = 0 := by
  have hTotal := totalVariation_singleton_zero H E.rightContinuous omega
  have hPositive :
      FiniteVariationKernel.positivePathMeasure
          H.finiteVariationPart_isBoundedVariation omega
          ({0} : Set ℝ≥0) = 0 := by
    apply le_antisymm
    · exact (FiniteVariationKernel.positivePathMeasure_le_totalVariation
        H.finiteVariationPart_isBoundedVariation omega
        ({0} : Set ℝ≥0)).trans_eq hTotal
    · exact bot_le
  rw [canonicalPositiveKernel_apply]
  simp [hPositive]

private theorem canonicalNegativeKernel_singleton_zero
    (E : SIntegrableFiniteVariationBridge H) (omega : Omega) :
    canonicalNegativeKernel E omega ({0} : Set ℝ≥0) = 0 := by
  have hTotal := totalVariation_singleton_zero H E.rightContinuous omega
  have hNegative :
      FiniteVariationKernel.negativePathMeasure
          H.finiteVariationPart_isBoundedVariation omega
          ({0} : Set ℝ≥0) = 0 := by
    apply le_antisymm
    · exact (FiniteVariationKernel.negativePathMeasure_le_totalVariation
        H.finiteVariationPart_isBoundedVariation omega
        ({0} : Set ℝ≥0)).trans_eq hTotal
    · exact bot_le
  rw [canonicalNegativeKernel_apply]
  simp [hNegative]

/-- The integrated canonical path-variation measure gives zero mass to
the predictable time-zero slice. -/
theorem canonicalVariationMeasure_timeZeroSlice
    (E : SIntegrableFiniteVariationBridge H) :
    canonicalVariationMeasure E
      (PredictableIntervalAlgebra.Interval.timeZeroSlice :
        Set (ℝ≥0 × Omega)) = 0 := by
  let : IsFiniteKernel (canonicalPositiveKernel E) :=
    isFiniteKernel_canonicalPositiveKernel E
  let : IsFiniteKernel (canonicalNegativeKernel E) :=
    isFiniteKernel_canonicalNegativeKernel E
  have hSection (omega : Omega) :
      ((fun t : ℝ≥0 => (t, omega)) ⁻¹'
          (PredictableIntervalAlgebra.Interval.timeZeroSlice :
            Set (ℝ≥0 × Omega))) = ({0} : Set ℝ≥0) := by
    ext t
    simp [PredictableIntervalAlgebra.Interval.mem_timeZeroSlice_iff]
  rw [canonicalVariationMeasure, Measure.add_apply,
    PredictableKernelMeasure.predictableMeasure_apply
      PredictableIntervalAlgebra.Interval.measurableSet_timeZeroSlice,
    PredictableKernelMeasure.predictableMeasure_apply
      PredictableIntervalAlgebra.Interval.measurableSet_timeZeroSlice]
  simp_rw [hSection, canonicalPositiveKernel_singleton_zero E,
    canonicalNegativeKernel_singleton_zero E]
  simp

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
