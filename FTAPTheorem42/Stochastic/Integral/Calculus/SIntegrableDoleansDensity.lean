/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableVariationBackwardRatio
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-!
# Predictable Radon--Nikodym density of finite variation

The two pathwise Jordan kernels define a positive predictable measure `λ`,
while their difference is the canonical signed predictable measure `ν`.
This module records the dominated representation `ν = h · λ` with a
predictable density in `[-1, 1]`.  The remaining Doléans--Dade step is to
show that this density has unit absolute value for `λ`-almost every point.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrableFiniteVariationBridge

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}
  {H : SIntegrableStrategy D}

/-- The integrated pathwise total-variation measure on predictable
time--sample space. -/
noncomputable def canonicalVariationMeasure
    (E : SIntegrableFiniteVariationBridge H) :
    @Measure (ℝ≥0 × Ω) ℱ.predictable :=
  let : IsFiniteKernel (canonicalPositiveKernel E) :=
    isFiniteKernel_canonicalPositiveKernel E
  let : IsFiniteKernel (canonicalNegativeKernel E) :=
    isFiniteKernel_canonicalNegativeKernel E
  PredictableKernelMeasure.predictableMeasure ℱ μ
      (canonicalPositiveKernel E) +
    PredictableKernelMeasure.predictableMeasure ℱ μ
      (canonicalNegativeKernel E)

noncomputable instance canonicalVariationMeasure.instIsFiniteMeasure
    (E : SIntegrableFiniteVariationBridge H) :
    IsFiniteMeasure (canonicalVariationMeasure E) := by
  let : IsFiniteKernel (canonicalPositiveKernel E) :=
    isFiniteKernel_canonicalPositiveKernel E
  let : IsFiniteKernel (canonicalNegativeKernel E) :=
    isFiniteKernel_canonicalNegativeKernel E
  unfold canonicalVariationMeasure
  infer_instance

/-- The variation of the canonical signed predictable measure is dominated
by integrated pathwise total variation. -/
theorem totalVariation_canonicalMeasure_le_canonicalVariationMeasure
    (E : SIntegrableFiniteVariationBridge H) :
    PredictableSignedMeasure.totalVariation E.canonicalMeasure ≤
      canonicalVariationMeasure E := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let : IsFiniteKernel (canonicalPositiveKernel E) :=
    isFiniteKernel_canonicalPositiveKernel E
  let : IsFiniteKernel (canonicalNegativeKernel E) :=
    isFiniteKernel_canonicalNegativeKernel E
  let νp := PredictableKernelMeasure.predictableMeasure ℱ μ
    (canonicalPositiveKernel E)
  let νn := PredictableKernelMeasure.predictableMeasure ℱ μ
    (canonicalNegativeKernel E)
  change (νp.toSignedMeasure - νn.toSignedMeasure).totalVariation ≤ νp + νn
  rw [signedMeasure_totalVariation_eq_variation]
  exact VectorMeasure.variation_sub_le.trans_eq (by simp [νp, νn])

/-- The canonical signed predictable measure is absolutely continuous with
respect to integrated pathwise total variation. -/
theorem canonicalMeasure_absolutelyContinuous_canonicalVariationMeasure
    (E : SIntegrableFiniteVariationBridge H) :
    E.canonicalMeasure ≪ᵥ
      (canonicalVariationMeasure E).toENNRealVectorMeasure := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  rw [SignedMeasure.absolutelyContinuous_ennreal_iff,
    VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure]
  exact Measure.absolutelyContinuous_of_le
    (totalVariation_canonicalMeasure_le_canonicalVariationMeasure E)

/-- The predictable Radon--Nikodym density of the signed finite-variation
measure with respect to integrated pathwise total variation. -/
noncomputable def canonicalVariationDensity
    (E : SIntegrableFiniteVariationBridge H) : ℝ≥0 × Ω → ℝ :=
  E.canonicalMeasure.rnDeriv (canonicalVariationMeasure E)

/-- The Radon--Nikodym density is measurable on predictable time--sample
space. -/
theorem canonicalVariationDensity_stronglyMeasurable
    (E : SIntegrableFiniteVariationBridge H) :
    StronglyMeasurable[ℱ.predictable] (canonicalVariationDensity E) := by
  exact (SignedMeasure.measurable_rnDeriv E.canonicalMeasure
    (canonicalVariationMeasure E)).stronglyMeasurable

/-- The canonical signed measure is represented by its predictable density
against integrated pathwise variation. -/
theorem withDensity_canonicalVariationDensity_eq_canonicalMeasure
    (E : SIntegrableFiniteVariationBridge H) :
    (canonicalVariationMeasure E).withDensityᵥ
        (canonicalVariationDensity E) = E.canonicalMeasure := by
  exact SignedMeasure.withDensityᵥ_rnDeriv_eq _ _
    (canonicalMeasure_absolutelyContinuous_canonicalVariationMeasure E)

/-- The predictable Radon--Nikodym density has absolute value at most one
almost everywhere for integrated pathwise variation. -/
theorem abs_canonicalVariationDensity_ae_le_one
    (E : SIntegrableFiniteVariationBridge H) :
    (fun p => |canonicalVariationDensity E p|) ≤ᵐ[canonicalVariationMeasure E]
      (fun _ => (1 : ℝ)) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let rho := canonicalVariationMeasure E
  let h := canonicalVariationDensity E
  have hInt : Integrable h rho :=
    SignedMeasure.integrable_rnDeriv E.canonicalMeasure rho
  have hVariation :
      rho.withDensity (fun p => ‖h p‖ₑ) =
        PredictableSignedMeasure.totalVariation E.canonicalMeasure := by
    have hEq := congrArg VectorMeasure.variation
      (withDensity_canonicalVariationDensity_eq_canonicalMeasure E)
    rw [Measure.variation_withDensityᵥ hInt,
      ← signedMeasure_totalVariation_eq_variation] at hEq
    exact hEq
  have hMeasureLe : rho.withDensity (fun p => ‖h p‖ₑ) ≤ rho := by
    rw [hVariation]
    exact totalVariation_canonicalMeasure_le_canonicalVariationMeasure E
  have hRnLe :
      (rho.withDensity (fun p => ‖h p‖ₑ)).rnDeriv rho ≤ᵐ[rho]
        (fun _ => (1 : ℝ≥0∞)) :=
    Measure.rnDeriv_le_one_of_le hMeasureLe
  have hRnEq :
      (rho.withDensity (fun p => ‖h p‖ₑ)).rnDeriv rho =ᵐ[rho]
        fun p => ‖h p‖ₑ :=
    Measure.rnDeriv_withDensity rho
      ((SignedMeasure.measurable_rnDeriv E.canonicalMeasure rho).enorm)
  filter_upwards [hRnEq, hRnLe] with p hp hple
  have henorm : ‖h p‖ₑ ≤ (1 : ℝ≥0∞) := hp ▸ hple
  simpa only [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_le_one] using henorm

/-- Pointwise clipping of the Radon--Nikodym density to the closed unit
interval.  This removes irrelevant values on a variation-null set before
constructing pathwise cumulative integrals. -/
noncomputable def clippedCanonicalVariationDensity
    (E : SIntegrableFiniteVariationBridge H) : ℝ≥0 × Ω → ℝ :=
  fun p => max (-1) (min 1 (canonicalVariationDensity E p))

/-- The clipped density is predictable. -/
theorem clippedCanonicalVariationDensity_stronglyMeasurable
    (E : SIntegrableFiniteVariationBridge H) :
    StronglyMeasurable[ℱ.predictable]
      (clippedCanonicalVariationDensity E) := by
  apply Measurable.stronglyMeasurable
  exact Measurable.max measurable_const
    (Measurable.min measurable_const
      (canonicalVariationDensity_stronglyMeasurable E).measurable)

/-- Clipping gives a pointwise unit bound. -/
theorem abs_clippedCanonicalVariationDensity_le_one
    (E : SIntegrableFiniteVariationBridge H) (p : ℝ≥0 × Ω) :
    |clippedCanonicalVariationDensity E p| ≤ 1 := by
  unfold clippedCanonicalVariationDensity
  rw [abs_le]
  constructor <;> simp

/-- Clipping changes the Radon--Nikodym density only on a variation-null
set. -/
theorem clippedCanonicalVariationDensity_ae_eq
    (E : SIntegrableFiniteVariationBridge H) :
    clippedCanonicalVariationDensity E =ᵐ[canonicalVariationMeasure E]
      canonicalVariationDensity E := by
  filter_upwards [abs_canonicalVariationDensity_ae_le_one E] with p hp
  have hp' : -1 ≤ canonicalVariationDensity E p ∧
      canonicalVariationDensity E p ≤ 1 := abs_le.mp hp
  simp [clippedCanonicalVariationDensity, hp'.1, hp'.2]

/-- The bounded predictable density still represents the canonical signed
measure. -/
theorem withDensity_clippedCanonicalVariationDensity_eq_canonicalMeasure
    (E : SIntegrableFiniteVariationBridge H) :
    (canonicalVariationMeasure E).withDensityᵥ
        (clippedCanonicalVariationDensity E) = E.canonicalMeasure := by
  rw [← withDensity_canonicalVariationDensity_eq_canonicalMeasure E]
  exact WithDensityᵥEq.congr_ae
    (clippedCanonicalVariationDensity_ae_eq E)

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
