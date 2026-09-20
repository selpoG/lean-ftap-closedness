/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Memin.EquivalentFiniteVariationMeasure
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableDoleansRigidity

/-!
# Finite-variation bridges for the Mémín reference measure

The common equivalent measure extracted from the Lemma 4.11 successive
variations has enough square integrability to instantiate the existing
Doléans finite-variation machinery.  This module first records the generic
weighted cumulative-variation constructor and the mass identity needed for
that instantiation.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace MeminEquivalentFiniteVariationMeasure

/-- A pointwise positive fallback used only on the null set where the common
summable envelope is infinite. -/
noncomputable def fallbackDensity (V : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ≥0∞ :=
  fun ω => ((1 + ENNReal.ofReal (V n ω)) ^ 2)⁻¹

/-- An everywhere positive `ℝ≥0` version of the common density.  It agrees
with `referenceDensity` away from the exceptional infinite-envelope set and
uses the single-term normalization on that set. -/
noncomputable def repairedReferenceDensity
    (V : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ≥0 := fun ω =>
  (if summableEnvelope V ω = ∞ then fallbackDensity V n ω
    else referenceDensity V ω).toNNReal

omit [MeasurableSpace Ω] in
theorem fallbackDensity_ne_top (V : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    fallbackDensity V n ω ≠ ∞ := by
  apply ENNReal.inv_ne_top.2
  positivity

omit [MeasurableSpace Ω] in
theorem fallbackDensity_ne_zero (V : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    fallbackDensity V n ω ≠ 0 := by
  apply ENNReal.inv_ne_zero.2
  exact ENNReal.pow_ne_top_iff.2 <| Or.inl <|
    ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩

omit [MeasurableSpace Ω] in
theorem fallbackDensity_le_one (V : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    fallbackDensity V n ω ≤ 1 := by
  apply ENNReal.inv_le_one.2
  exact one_le_pow_of_one_le' (le_add_right le_rfl) 2

omit [MeasurableSpace Ω] in
theorem fallbackDensity_mul_term_le_one
    (V : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    fallbackDensity V n ω * ENNReal.ofReal (V n ω) ≤ 1 := by
  have hTerm : ENNReal.ofReal (V n ω) ≤
      (1 + ENNReal.ofReal (V n ω)) ^ 2 := by
    calc
      ENNReal.ofReal (V n ω) ≤ 1 + ENNReal.ofReal (V n ω) :=
        le_add_left le_rfl
      _ = 1 * (1 + ENNReal.ofReal (V n ω)) := (one_mul _).symm
      _ ≤ (1 + ENNReal.ofReal (V n ω)) *
          (1 + ENNReal.ofReal (V n ω)) :=
        mul_le_mul_left (le_add_right le_rfl) _
      _ = (1 + ENNReal.ofReal (V n ω)) ^ 2 := (pow_two _).symm
  calc
    fallbackDensity V n ω * ENNReal.ofReal (V n ω) ≤
        fallbackDensity V n ω *
          (1 + ENNReal.ofReal (V n ω)) ^ 2 :=
      mul_le_mul_right hTerm _
    _ ≤ 1 := ENNReal.inv_mul_le_one _

theorem repairedReferenceDensity_measurable {V : ℕ → Ω → ℝ}
    (hV : ∀ n, Measurable (V n)) (n : ℕ) :
    Measurable (repairedReferenceDensity V n) := by
  apply Measurable.ennreal_toNNReal
  apply Measurable.ite
    (measurableSet_eq_fun (summableEnvelope_measurable hV) measurable_const)
  · exact ((measurable_const.add (hV n).ennreal_ofReal).pow_const 2).inv
  · exact referenceDensity_measurable hV

omit [MeasurableSpace Ω] in
theorem coe_repairedReferenceDensity
    (V : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    (repairedReferenceDensity V n ω : ℝ≥0∞) =
      if summableEnvelope V ω = ∞ then fallbackDensity V n ω
      else referenceDensity V ω := by
  unfold repairedReferenceDensity
  by_cases hω : summableEnvelope V ω = ∞
  · rw [ite_eq_left hω, ENNReal.coe_toNNReal (fallbackDensity_ne_top V n ω)]
  · rw [ite_eq_right hω, ENNReal.coe_toNNReal (referenceDensity_ne_top V ω)]

omit [MeasurableSpace Ω] in
theorem repairedReferenceDensity_pos
    (V : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    0 < repairedReferenceDensity V n ω := by
  apply ENNReal.toNNReal_pos
  · by_cases hω : summableEnvelope V ω = ∞
    · simpa only [ite_eq_left hω] using fallbackDensity_ne_zero V n ω
    · have hFinite : (1 + summableEnvelope V ω) ^ 2 ≠ ∞ :=
        ENNReal.pow_ne_top_iff.2 <| Or.inl <|
          ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hω⟩
      simpa only [ite_eq_right hω, referenceDensity, ENNReal.inv_ne_zero] using hFinite
  · by_cases hω : summableEnvelope V ω = ∞
    · simpa only [ite_eq_left hω] using fallbackDensity_ne_top V n ω
    · simpa only [ite_eq_right hω] using referenceDensity_ne_top V ω

omit [MeasurableSpace Ω] in
theorem repairedReferenceDensity_le_one
    (V : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    repairedReferenceDensity V n ω ≤ 1 := by
  rw [← ENNReal.coe_le_coe, coe_repairedReferenceDensity]
  by_cases hω : summableEnvelope V ω = ∞
  · simpa only [ite_eq_left hω, ENNReal.coe_one] using
      fallbackDensity_le_one V n ω
  · simpa only [ite_eq_right hω, ENNReal.coe_one] using
      referenceDensity_le_one V ω

omit [MeasurableSpace Ω] in
theorem repairedReferenceDensity_mul_term_le_one
    (V : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    (repairedReferenceDensity V n ω : ℝ≥0∞) *
        ENNReal.ofReal (V n ω) ≤ 1 := by
  rw [coe_repairedReferenceDensity]
  by_cases hω : summableEnvelope V ω = ∞
  · simpa only [ite_eq_left hω] using fallbackDensity_mul_term_le_one V n ω
  · rw [ite_eq_right hω]
    calc
      referenceDensity V ω * ENNReal.ofReal (V n ω) ≤
          referenceDensity V ω * summableEnvelope V ω := by
        exact mul_le_mul_right (ENNReal.le_tsum (f := fun k => ENNReal.ofReal (V k ω)) n) _
      _ ≤ 1 := referenceDensity_mul_envelope_le_one V ω

theorem coe_repairedReferenceDensity_ae_eq_referenceDensity
    {μ : Measure Ω} {V : ℕ → Ω → ℝ}
    (hSummable : ∀ᵐ ω ∂μ, Summable (fun n => V n ω)) (n : ℕ) :
    (fun ω => (repairedReferenceDensity V n ω : ℝ≥0∞)) =ᵐ[μ]
      referenceDensity V := by
  filter_upwards [hSummable] with ω hω
  have hFinite : summableEnvelope V ω ≠ ∞ := by
    unfold summableEnvelope
    exact hω.tsum_ofReal_ne_top
  rw [coe_repairedReferenceDensity, ite_eq_right hFinite]

theorem withDensity_repairedReferenceDensity_eq_referenceMeasure
    {μ : Measure Ω} {V : ℕ → Ω → ℝ}
    (hSummable : ∀ᵐ ω ∂μ, Summable (fun n => V n ω)) (n : ℕ) :
    μ.withDensity (fun ω =>
        (repairedReferenceDensity V n ω : ℝ≥0∞)) =
      referenceMeasure μ V := by
  unfold referenceMeasure
  exact withDensity_congr_ae
    (coe_repairedReferenceDensity_ae_eq_referenceDensity hSummable n)

end MeminEquivalentFiniteVariationMeasure

namespace SIntegrableFiniteVariationBridge

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}
  {H : SIntegrableStrategy D}

/-- Construct the standard finite-variation bridge from an arbitrary
strictly positive bounded sample density, a uniform weighted-variation
bound, and square integrability under the corresponding reference measure. -/
noncomputable def ofCumulativeVariationWithDensity
    (ρ : Ω → ℝ≥0) (hρMeasurable : Measurable ρ)
    (hρPositive : ∀ ω, 0 < ρ ω) (hρLeOne : ∀ ω, ρ ω ≤ 1)
    {C : ℝ≥0∞} (hC : C < ∞)
    (hWeightedVariation : ∀ ω,
      (ρ ω : ℝ≥0∞) *
        (FiniteVariationPath.signedMeasure
          (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
            Set.univ ≤ C)
    (hVariationMemLpTwo : MemLp (fun ω =>
      (FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.real
          Set.univ) (2 : ℝ≥0∞)
      (μ.withDensity fun ω => (ρ ω : ℝ≥0∞))) :
    SIntegrableFiniteVariationBridge H where
  rightContinuous := H.finiteVariationPart_isRightContinuous
  fixedTimeMeasurable := finiteVariationPart_measurable H
  variationProcess := cumulativeVariation H
  variationProcess_measurable := measurable_cumulativeVariation H
    H.finiteVariationPart_isRightContinuous
  variation_Ioc := totalVariation_real_Ioc_eq_cumulativeVariation_sub H
  variationTerminal := fun ω =>
    (FiniteVariationPath.signedMeasure
      (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.real
        Set.univ
  variationInitial := fun _ => 0
  variationTerminal_measurable :=
    measurable_totalVariation_univ_of_cumulativeVariation
      H.finiteVariationPart_isRightContinuous
  variationInitial_measurable := measurable_const
  referenceDensity := ρ
  referenceDensity_measurable := hρMeasurable
  referenceDensity_pos := hρPositive
  referenceDensity_le_one := hρLeOne
  bound := C
  bound_lt_top := hC
  variation_univ := by simp
  weightedVariationBound := hWeightedVariation
  variationMemLpTwo := hVariationMemLpTwo

/-- The total mass of the integrated pathwise variation measure is the
reference-measure integral of the whole-axis path variation. -/
theorem canonicalVariationMeasure_univ_eq_lintegral_totalVariation
    (E : SIntegrableFiniteVariationBridge H) :
    canonicalVariationMeasure E Set.univ =
      ∫⁻ ω, ENNReal.ofReal
        ((FiniteVariationPath.signedMeasure
          (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.real
            Set.univ) ∂E.referenceMeasure := by
  let : IsFiniteKernel (canonicalPositiveKernel E) :=
    isFiniteKernel_canonicalPositiveKernel E
  let : IsFiniteKernel (canonicalNegativeKernel E) :=
    isFiniteKernel_canonicalNegativeKernel E
  rw [canonicalVariationMeasure, Measure.add_apply,
    PredictableKernelMeasure.predictableMeasure_apply MeasurableSet.univ,
    PredictableKernelMeasure.predictableMeasure_apply MeasurableSet.univ]
  change _ = ∫⁻ ω, ENNReal.ofReal
    ((FiniteVariationPath.signedMeasure
      (H.finiteVariationPart_isBoundedVariation ω)).totalVariation.real
        Set.univ) ∂(μ.withDensity fun ω =>
          (E.referenceDensity ω : ℝ≥0∞))
  rw [lintegral_withDensity_eq_lintegral_mul μ
    E.referenceDensity_measurable.coe_nnreal_ennreal
    (measurable_totalVariation_univ_of_cumulativeVariation
      E.rightContinuous).ennreal_ofReal]
  simp only [Set.preimage_univ]
  rw [← lintegral_add_left
    (Kernel.measurable_coe (canonicalPositiveKernel E)
      MeasurableSet.univ)]
  apply lintegral_congr
  intro ω
  rw [canonicalPositiveKernel_apply, canonicalNegativeKernel_apply,
    Measure.smul_apply, Measure.smul_apply]
  simp only [ENNReal.smul_def, smul_eq_mul, Pi.mul_apply]
  rw [← mul_add]
  congr 1
  let ν := FiniteVariationPath.signedMeasure
    (H.finiteVariationPart_isBoundedVariation ω)
  let : IsFiniteMeasure ν.totalVariation := by
    dsimp only [ν]
    unfold SignedMeasure.totalVariation
    infer_instance
  have hνTop : ν.totalVariation Set.univ ≠ ∞ := measure_ne_top _ _
  rw [ofReal_measureReal hνTop]
  rfl

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
