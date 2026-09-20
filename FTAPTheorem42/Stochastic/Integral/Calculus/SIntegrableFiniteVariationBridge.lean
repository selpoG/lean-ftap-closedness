/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Predictable.PredictableKernelMeasure
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationKernel
import FTAPTheorem42.Foundations.FiniteVariationPathMeasure
import FTAPTheorem42.Stochastic.Predictable.PredictableHahnVariationMass
import FTAPTheorem42.Stochastic.Integral.Calculus.SemimartingaleStrategy

/-!
# Finite-variation bridge for a realized stochastic-integrable strategy

This file attaches the existing pathwise finite-variation and predictable
kernel API to the finite-variation component carried by one
`SIntegrableStrategy`.  A strictly positive sample density normalizes the
path kernels.  The associated equivalent reference measure is used by the
Doléans residual; the original uniformly finite construction is the special
case of density one.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Component data and its canonical predictable measure -/

structure SIntegrableFiniteVariationBridge
    {S : Process Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {D : SpecialSemimartingaleDecomposition S ℱ μ}
    (H : SIntegrableStrategy D) where
  rightContinuous : ∀ ω t,
    ContinuousWithinAt (fun u => H.finiteVariationPart u ω) (Set.Ici t) t
  fixedTimeMeasurable : ∀ t, Measurable (H.finiteVariationPart t)
  variationProcess : ℝ≥0 → Ω → ℝ
  variationProcess_measurable : ∀ t, Measurable (variationProcess t)
  variation_Ioc : ∀ ω a b, a ≤ b →
    (FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.real (Ioc a b) =
      variationProcess b ω - variationProcess a ω
  variationTerminal : Ω → ℝ
  variationInitial : Ω → ℝ
  variationTerminal_measurable : Measurable variationTerminal
  variationInitial_measurable : Measurable variationInitial
  referenceDensity : Ω → ℝ≥0
  referenceDensity_measurable : Measurable referenceDensity
  referenceDensity_pos : ∀ ω, 0 < referenceDensity ω
  referenceDensity_le_one : ∀ ω, referenceDensity ω ≤ 1
  bound : ℝ≥0∞
  bound_lt_top : bound < ∞
  variation_univ : ∀ ω,
    (FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.real Set.univ =
      variationTerminal ω - variationInitial ω
  weightedVariationBound : ∀ ω,
    (referenceDensity ω : ℝ≥0∞) *
        (FiniteVariationPath.signedMeasure
          (H.finiteVariationPart_isBoundedVariation ω)).totalVariation Set.univ ≤ bound
  variationMemLpTwo :
    MemLp (fun ω =>
      (FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.real Set.univ)
      (2 : ℝ≥0∞)
      (μ.withDensity fun ω => (referenceDensity ω : ℝ≥0∞))

namespace SIntegrableFiniteVariationBridge

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}
  {H : SIntegrableStrategy D}

/-- The finite measure equivalent to the market measure under which the
Doléans residual has a square-integrable random variation bound. -/
noncomputable def referenceMeasure
    (E : SIntegrableFiniteVariationBridge H) : Measure Ω :=
  μ.withDensity fun ω => (E.referenceDensity ω : ℝ≥0∞)

noncomputable instance referenceMeasure.instIsFiniteMeasure
    (E : SIntegrableFiniteVariationBridge H) :
    IsFiniteMeasure E.referenceMeasure := by
  apply isFiniteMeasure_withDensity
  apply ne_of_lt
  calc
    (∫⁻ ω, (E.referenceDensity ω : ℝ≥0∞) ∂μ) ≤
        ∫⁻ _ω : Ω, (1 : ℝ≥0∞) ∂μ := by
      apply lintegral_mono
      intro ω
      exact ENNReal.coe_le_coe.2 (E.referenceDensity_le_one ω)
    _ < ∞ := by simp

/-- The reference density is everywhere nonzero, so the market and
reference measures have exactly the same almost-everywhere relations. -/
theorem referenceMeasure_ae_eq_iff
    (E : SIntegrableFiniteVariationBridge H) {f g : Ω → ℝ} :
    f =ᵐ[E.referenceMeasure] g ↔ f =ᵐ[μ] g := by
  exact withDensity_ae_eq
    E.referenceDensity_measurable.coe_nnreal_ennreal.aemeasurable
    (Filter.Eventually.of_forall fun ω => by
      exact_mod_cast (E.referenceDensity_pos ω).ne')

private theorem measurable_variation_Ioc
    (E : SIntegrableFiniteVariationBridge H) (a b : ℝ≥0) (hab : a < b) :
    Measurable fun ω =>
      (FiniteVariationPath.signedMeasure
          (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.real (Ioc a b) := by
  have hEq :
      (fun ω =>
          (FiniteVariationPath.signedMeasure
              (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.real (Ioc a b)) =
        (fun ω => E.variationProcess b ω - E.variationProcess a ω) := by
    funext ω
    exact E.variation_Ioc ω a b hab.le
  rw [hEq]
  exact (E.variationProcess_measurable b).sub
    (E.variationProcess_measurable a)

private theorem measurable_variation_univ
    (E : SIntegrableFiniteVariationBridge H) :
    Measurable fun ω =>
      (FiniteVariationPath.signedMeasure
          (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.real Set.univ := by
  have hEq :
      (fun ω =>
          (FiniteVariationPath.signedMeasure
              (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.real Set.univ) =
        (fun ω => E.variationTerminal ω - E.variationInitial ω) := by
    funext ω
    exact E.variation_univ ω
  rw [hEq]
  exact E.variationTerminal_measurable.sub E.variationInitial_measurable

/-! ## Explicit Jordan kernels -/

/-- The positive Jordan kernel used by the canonical predictable measure. -/
noncomputable def canonicalPositiveKernel
    (E : SIntegrableFiniteVariationBridge H) : Kernel Ω ℝ≥0 :=
  let hVariation : ∀ a b : ℝ≥0, a < b → Measurable fun ω =>
      (FiniteVariationPath.signedMeasure
          (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.real (Ioc a b) :=
    fun a b hab => measurable_variation_Ioc E a b hab
  let hSigned : Measurable fun ω =>
      FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation ω) Set.univ :=
    FiniteVariationKernel.measurable_signedMeasure_univ_nnreal
      H.finiteVariationPart_isBoundedVariation E.fixedTimeMeasurable
  let hPosIoc := FiniteVariationKernel.measurable_positivePathMeasure_Ioc
    H.finiteVariationPart_isBoundedVariation E.rightContinuous
    E.fixedTimeMeasurable hVariation
  let hPosUniv := FiniteVariationKernel.measurable_positivePathMeasure_univ
    H.finiteVariationPart_isBoundedVariation hSigned (measurable_variation_univ E)
  let ρ : Ω → Measure ℝ≥0 := fun ω =>
    E.referenceDensity ω •
      FiniteVariationKernel.positivePathMeasure
        H.finiteVariationPart_isBoundedVariation ω
  letI (ω : Ω) : IsFiniteMeasure (ρ ω) := by
    dsimp only [ρ]
    infer_instance
  FiniteVariationKernel.ofFiniteMeasuresIoc ρ
    (fun a b hab => by
      change Measurable fun ω => (E.referenceDensity ω : ℝ≥0∞) *
        FiniteVariationKernel.positivePathMeasure
          H.finiteVariationPart_isBoundedVariation ω (Ioc a b)
      exact E.referenceDensity_measurable.coe_nnreal_ennreal.mul
        (hPosIoc a b hab))
    (by
      change Measurable fun ω => (E.referenceDensity ω : ℝ≥0∞) *
        FiniteVariationKernel.positivePathMeasure
          H.finiteVariationPart_isBoundedVariation ω Set.univ
      exact E.referenceDensity_measurable.coe_nnreal_ennreal.mul hPosUniv)

/-- The negative Jordan kernel used by the canonical predictable measure. -/
noncomputable def canonicalNegativeKernel
    (E : SIntegrableFiniteVariationBridge H) : Kernel Ω ℝ≥0 :=
  let hVariation : ∀ a b : ℝ≥0, a < b → Measurable fun ω =>
      (FiniteVariationPath.signedMeasure
          (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.real (Ioc a b) :=
    fun a b hab => measurable_variation_Ioc E a b hab
  let hSigned : Measurable fun ω =>
      FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation ω) Set.univ :=
    FiniteVariationKernel.measurable_signedMeasure_univ_nnreal
      H.finiteVariationPart_isBoundedVariation E.fixedTimeMeasurable
  let hNegIoc := FiniteVariationKernel.measurable_negativePathMeasure_Ioc
    H.finiteVariationPart_isBoundedVariation E.rightContinuous
    E.fixedTimeMeasurable hVariation
  let hNegUniv := FiniteVariationKernel.measurable_negativePathMeasure_univ
    H.finiteVariationPart_isBoundedVariation hSigned (measurable_variation_univ E)
  let ρ : Ω → Measure ℝ≥0 := fun ω =>
    E.referenceDensity ω •
      FiniteVariationKernel.negativePathMeasure
        H.finiteVariationPart_isBoundedVariation ω
  letI (ω : Ω) : IsFiniteMeasure (ρ ω) := by
    dsimp only [ρ]
    infer_instance
  FiniteVariationKernel.ofFiniteMeasuresIoc ρ
    (fun a b hab => by
      change Measurable fun ω => (E.referenceDensity ω : ℝ≥0∞) *
        FiniteVariationKernel.negativePathMeasure
          H.finiteVariationPart_isBoundedVariation ω (Ioc a b)
      exact E.referenceDensity_measurable.coe_nnreal_ennreal.mul
        (hNegIoc a b hab))
    (by
      change Measurable fun ω => (E.referenceDensity ω : ℝ≥0∞) *
        FiniteVariationKernel.negativePathMeasure
          H.finiteVariationPart_isBoundedVariation ω Set.univ
      exact E.referenceDensity_measurable.coe_nnreal_ennreal.mul hNegUniv)

@[simp]
theorem canonicalPositiveKernel_apply
    (E : SIntegrableFiniteVariationBridge H) (ω : Ω) :
    canonicalPositiveKernel E ω =
      E.referenceDensity ω • FiniteVariationKernel.positivePathMeasure
        H.finiteVariationPart_isBoundedVariation ω := by
  unfold canonicalPositiveKernel
  rfl

@[simp]
theorem canonicalNegativeKernel_apply
    (E : SIntegrableFiniteVariationBridge H) (ω : Ω) :
    canonicalNegativeKernel E ω =
      E.referenceDensity ω • FiniteVariationKernel.negativePathMeasure
        H.finiteVariationPart_isBoundedVariation ω := by
  unfold canonicalNegativeKernel
  rfl

theorem isFiniteKernel_canonicalPositiveKernel
    (E : SIntegrableFiniteVariationBridge H) :
    IsFiniteKernel (canonicalPositiveKernel E) := by
  unfold canonicalPositiveKernel
  apply FiniteVariationKernel.isFiniteKernel_ofFiniteMeasuresIoc
  · exact E.bound_lt_top
  · intro ω
    change (E.referenceDensity ω : ℝ≥0∞) *
      (FiniteVariationKernel.positivePathMeasure
        H.finiteVariationPart_isBoundedVariation ω Set.univ) ≤ E.bound
    calc
      (E.referenceDensity ω : ℝ≥0∞) *
          (FiniteVariationKernel.positivePathMeasure
            H.finiteVariationPart_isBoundedVariation ω Set.univ) ≤
          (E.referenceDensity ω : ℝ≥0∞) *
            ((FiniteVariationPath.signedMeasure
              (H.finiteVariationPart_isBoundedVariation ω)).totalVariation Set.univ) := by
        exact mul_le_mul_right
          (FiniteVariationKernel.positivePathMeasure_le_totalVariation
            H.finiteVariationPart_isBoundedVariation ω Set.univ)
          (E.referenceDensity ω : ℝ≥0∞)
      _ ≤ E.bound := E.weightedVariationBound ω

theorem isFiniteKernel_canonicalNegativeKernel
    (E : SIntegrableFiniteVariationBridge H) :
    IsFiniteKernel (canonicalNegativeKernel E) := by
  unfold canonicalNegativeKernel
  apply FiniteVariationKernel.isFiniteKernel_ofFiniteMeasuresIoc
  · exact E.bound_lt_top
  · intro ω
    change (E.referenceDensity ω : ℝ≥0∞) *
      (FiniteVariationKernel.negativePathMeasure
        H.finiteVariationPart_isBoundedVariation ω Set.univ) ≤ E.bound
    calc
      (E.referenceDensity ω : ℝ≥0∞) *
          (FiniteVariationKernel.negativePathMeasure
            H.finiteVariationPart_isBoundedVariation ω Set.univ) ≤
          (E.referenceDensity ω : ℝ≥0∞) *
            ((FiniteVariationPath.signedMeasure
              (H.finiteVariationPart_isBoundedVariation ω)).totalVariation Set.univ) := by
        exact mul_le_mul_right
          (FiniteVariationKernel.negativePathMeasure_le_totalVariation
            H.finiteVariationPart_isBoundedVariation ω Set.univ)
          (E.referenceDensity ω : ℝ≥0∞)
      _ ≤ E.bound := E.weightedVariationBound ω

/-- The canonical predictable signed measure generated by the strategy's
finite-variation component. -/
noncomputable def canonicalMeasure
    (E : SIntegrableFiniteVariationBridge H) :
    PredictableSignedMeasure.Measure ℱ :=
  let : IsFiniteKernel (canonicalPositiveKernel E) :=
    isFiniteKernel_canonicalPositiveKernel E
  let : IsFiniteKernel (canonicalNegativeKernel E) :=
    isFiniteKernel_canonicalNegativeKernel E
  PredictableKernelMeasure.signedMeasure ℱ μ
    (canonicalPositiveKernel E) (canonicalNegativeKernel E)

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
