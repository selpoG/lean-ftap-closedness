/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Memin.LocalS1Normalization
import FTAPTheorem42.Stochastic.FiniteVariation.CanonicalVariationControl

/-!
# Pathwise Stieltjes identities as Mémin control estimates

An actual finite-variation stochastic integral is naturally specified on
each sample path.  If its signed Stieltjes measure is the source path measure
weighted by the predictable integrand, the total variation of that output
equals the pathwise `L¹` size of the integrand.  The nonnegative Fubini
formula for canonical variation lifts this identity to the predictable
control measure.  Thus the predictable-limit argument needs no independent
product-space density or integrability assumptions.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrablePredictableMultiplierLinearL2Calculus

open SIntegrableFiniteVariationBridge

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

omit [SigmaFiniteFiltration μ ℱ] in
/-- On one sample path, an oriented Stieltjes density identifies the raw
integrand `L¹` size with the output path's Jordan variation. -/
theorem lintegral_meminIntegrandDifference_eq_pathTotalVariation_of_density
    {G R : SIntegrableStrategy D}
    (source : SIntegrableFiniteVariationBridge G)
    (H K : SIntegrableStrategy D)
    (ω : Ω)
    (hIntegrable : Integrable
      (fun t => meminIntegrandDifference H K (t, ω))
      (FiniteVariationPath.signedMeasure
        (G.finiteVariationPart_isBoundedVariation ω)).totalVariation)
    (hDirectionUnit : (fun t =>
      |jumpCorrectedCanonicalVariationDensity source (t, ω)|) =ᵐ[(FiniteVariationPath.signedMeasure
          (G.finiteVariationPart_isBoundedVariation ω)).totalVariation]
        (fun _ => (1 : ℝ)))
    (hDensity :
      (FiniteVariationPath.signedMeasure
        (G.finiteVariationPart_isBoundedVariation ω)).totalVariation.withDensityᵥ
          (fun t => jumpCorrectedCanonicalVariationDensity source (t, ω) *
            meminIntegrandDifference H K (t, ω)) =
        FiniteVariationPath.signedMeasure
          (R.finiteVariationPart_isBoundedVariation ω)) :
    (∫⁻ t, ENNReal.ofReal
      |meminIntegrandDifference H K (t, ω)|
        ∂(FiniteVariationPath.signedMeasure
          (G.finiteVariationPart_isBoundedVariation ω)).totalVariation) =
      (FiniteVariationPath.signedMeasure
        (R.finiteVariationPart_isBoundedVariation ω)).totalVariation Set.univ := by
  let ν := (FiniteVariationPath.signedMeasure
    (G.finiteVariationPart_isBoundedVariation ω)).totalVariation
  let η := FiniteVariationPath.signedMeasure
    (R.finiteVariationPart_isBoundedVariation ω)
  let f : ℝ≥0 → ℝ := fun t => meminIntegrandDifference H K (t, ω)
  let direction : ℝ≥0 → ℝ := fun t =>
    jumpCorrectedCanonicalVariationDensity source (t, ω)
  let g : ℝ≥0 → ℝ := fun t => direction t * f t
  have hDirectionIntegrable : Integrable direction ν :=
    integrable_jumpCorrectedCanonicalVariationDensity_section source ω
  have hgAEStronglyMeasurable : AEStronglyMeasurable g ν :=
    hDirectionIntegrable.aestronglyMeasurable.mul
      hIntegrable.aestronglyMeasurable
  have hgIntegrable : Integrable g ν := by
    apply hIntegrable.mono hgAEStronglyMeasurable
    exact Eventually.of_forall fun t => by
      dsimp only [g, direction, f]
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _)
        (abs_jumpCorrectedCanonicalVariationDensity_le_one source (t, ω))
  have hEnorm : (fun t => ‖g t‖ₑ) =ᵐ[ν] (fun t => ‖f t‖ₑ) := by
    filter_upwards [hDirectionUnit] with t ht
    dsimp only [g, direction]
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_mul, ht,
      one_mul]
  calc
    (∫⁻ t, ENNReal.ofReal |meminIntegrandDifference H K (t, ω)| ∂ν) =
        (ν.withDensity (fun t => ‖f t‖ₑ)) Set.univ := by
      rw [withDensity_apply _ MeasurableSet.univ]
      simp only [Measure.restrict_univ, f, Real.enorm_eq_ofReal_abs]
    _ = (ν.withDensity (fun t => ‖g t‖ₑ)) Set.univ := by
      rw [withDensity_congr_ae hEnorm.symm]
    _ = (ν.withDensityᵥ g).variation Set.univ := by
      rw [Measure.variation_withDensityᵥ hgIntegrable]
    _ = η.variation Set.univ := by
      rw [hDensity]
    _ = η.totalVariation Set.univ := by
      exact congrArg (fun m : Measure ℝ≥0 => m Set.univ)
        (@signedMeasure_totalVariation_eq_variation ℝ≥0 _ η).symm

omit [SigmaFiniteFiltration μ ℱ] in
/-- A pathwise finite-variation density identity lifts to the exact
canonical-control `L¹` identity.  Source and output bridges need only use the
same equivalent reference measure; no product-space density assumption is
required. -/
theorem meminIntegrandDifferenceLIntegral_eq_canonicalVariation_of_pathwiseDensity
    {G R : SIntegrableStrategy D}
    (source : SIntegrableFiniteVariationBridge G)
    (H K : SIntegrableStrategy D)
    (target : SIntegrableFiniteVariationBridge R)
    (hReferenceMeasure : source.referenceMeasure = target.referenceMeasure)
    (hPathIntegrable : ∀ᵐ ω ∂μ, Integrable
      (fun t => meminIntegrandDifference H K (t, ω))
      (FiniteVariationPath.signedMeasure
        (G.finiteVariationPart_isBoundedVariation ω)).totalVariation)
    (hPathDensity : ∀ᵐ ω ∂μ,
      (FiniteVariationPath.signedMeasure
        (G.finiteVariationPart_isBoundedVariation ω)).totalVariation.withDensityᵥ
          (fun t => jumpCorrectedCanonicalVariationDensity source (t, ω) *
            meminIntegrandDifference H K (t, ω)) =
        FiniteVariationPath.signedMeasure
          (R.finiteVariationPart_isBoundedVariation ω)) :
    meminIntegrandDifferenceLIntegral
        (canonicalVariationMeasure source) H K =
      canonicalVariationMeasure target Set.univ := by
  have hPathMass : ∀ᵐ ω ∂μ,
      (∫⁻ t, ENNReal.ofReal |meminIntegrandDifference H K (t, ω)|
        ∂(FiniteVariationPath.signedMeasure
          (G.finiteVariationPart_isBoundedVariation ω)).totalVariation) =
        (FiniteVariationPath.signedMeasure
          (R.finiteVariationPart_isBoundedVariation ω)).totalVariation
            Set.univ := by
    filter_upwards [hPathIntegrable, hPathDensity,
      abs_jumpCorrectedCanonicalVariationDensity_ae_eq_one_pathwise source]
        with ω hInt hDensity hUnit
    exact lintegral_meminIntegrandDifference_eq_pathTotalVariation_of_density
      source H K ω hInt hUnit hDensity
  have hTargetVariationMeasurable : Measurable fun ω =>
      (FiniteVariationPath.signedMeasure
        (R.finiteVariationPart_isBoundedVariation ω)).totalVariation.real
          Set.univ :=
    measurable_totalVariation_univ_of_cumulativeVariation
      target.rightContinuous
  have hControlIntegrandMeasurable : Measurable[ℱ.predictable] (fun p =>
      ENNReal.ofReal |meminIntegrandDifference H K p|) := by
    apply Measurable.ennreal_ofReal
    simpa only [Real.norm_eq_abs] using
      (meminIntegrandDifference_stronglyMeasurable H K).norm.measurable
  rw [meminIntegrandDifferenceLIntegral,
    lintegral_canonicalVariationMeasure_eq_lintegral_pathVariation source
      hControlIntegrandMeasurable]
  calc
    (∫⁻ ω, (source.referenceDensity ω : ℝ≥0∞) *
        ∫⁻ t, ENNReal.ofReal |meminIntegrandDifference H K (t, ω)|
          ∂(FiniteVariationPath.signedMeasure
            (G.finiteVariationPart_isBoundedVariation ω)).totalVariation ∂μ) =
        ∫⁻ ω, (source.referenceDensity ω : ℝ≥0∞) *
          (FiniteVariationPath.signedMeasure
            (R.finiteVariationPart_isBoundedVariation ω)).totalVariation
              Set.univ ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hPathMass] with ω hω
      rw [hω]
    _ = ∫⁻ ω, ENNReal.ofReal
        ((FiniteVariationPath.signedMeasure
          (R.finiteVariationPart_isBoundedVariation ω)).totalVariation.real
            Set.univ) ∂source.referenceMeasure := by
      change _ = ∫⁻ ω, ENNReal.ofReal
        ((FiniteVariationPath.signedMeasure
          (R.finiteVariationPart_isBoundedVariation ω)).totalVariation.real
            Set.univ) ∂μ.withDensity (fun ω =>
              (source.referenceDensity ω : ℝ≥0∞))
      rw [lintegral_withDensity_eq_lintegral_mul μ
        source.referenceDensity_measurable.coe_nnreal_ennreal
        hTargetVariationMeasurable.ennreal_ofReal]
      apply lintegral_congr
      intro ω
      congr 1
      let η := FiniteVariationPath.signedMeasure
        (R.finiteVariationPart_isBoundedVariation ω)
      let : IsFiniteMeasure η.totalVariation := by
        dsimp only [η]
        unfold SignedMeasure.totalVariation
        infer_instance
      exact (ofReal_measureReal (measure_ne_top η.totalVariation Set.univ)).symm
    _ = ∫⁻ ω, ENNReal.ofReal
        ((FiniteVariationPath.signedMeasure
          (R.finiteVariationPart_isBoundedVariation ω)).totalVariation.real
            Set.univ) ∂target.referenceMeasure := by
      rw [hReferenceMeasure]
    _ = canonicalVariationMeasure target Set.univ :=
      (canonicalVariationMeasure_univ_eq_lintegral_totalVariation target).symm

omit [SigmaFiniteFiltration μ ℱ] in
/-- A pathwise Stieltjes identity for one integrand, rather than an
integrand difference, gives its exact canonical-control L¹ mass. -/
theorem integrandLIntegral_eq_canonicalVariation_of_pathwiseDensity
    {G R : SIntegrableStrategy D}
    (source : SIntegrableFiniteVariationBridge G)
    (H : SIntegrableStrategy D)
    (target : SIntegrableFiniteVariationBridge R)
    (hReferenceMeasure : source.referenceMeasure = target.referenceMeasure)
    (hPathIntegrable : ∀ᵐ ω ∂μ, Integrable
      (fun t => H.integrand t ω)
      (FiniteVariationPath.signedMeasure
        (G.finiteVariationPart_isBoundedVariation ω)).totalVariation)
    (hPathDensity : ∀ᵐ ω ∂μ,
      (FiniteVariationPath.signedMeasure
        (G.finiteVariationPart_isBoundedVariation ω)).totalVariation.withDensityᵥ
          (fun t => jumpCorrectedCanonicalVariationDensity source (t, ω) *
            H.integrand t ω) =
        FiniteVariationPath.signedMeasure
          (R.finiteVariationPart_isBoundedVariation ω)) :
    (∫⁻ p, ENNReal.ofReal |H.integrand p.1 p.2|
        ∂canonicalVariationMeasure source) =
      canonicalVariationMeasure target Set.univ := by
  let Z := H.smul 0
  have hDifference :=
    meminIntegrandDifferenceLIntegral_eq_canonicalVariation_of_pathwiseDensity
      source H Z target hReferenceMeasure
        (by
          simpa only [Z, meminIntegrandDifference, SIntegrableStrategy.smul,
            Pi.smul_apply, zero_mul, zero_smul, Pi.zero_apply, sub_zero] using hPathIntegrable)
        (by
          simpa only [Z, meminIntegrandDifference, SIntegrableStrategy.smul,
            Pi.smul_apply, zero_mul, zero_smul, Pi.zero_apply, sub_zero] using hPathDensity)
  simpa only [meminIntegrandDifferenceLIntegral, Z,
    meminIntegrandDifference, SIntegrableStrategy.smul,
    Pi.smul_apply, zero_mul, zero_smul, Pi.zero_apply, sub_zero] using hDifference

end SIntegrablePredictableMultiplierLinearL2Calculus

end FTAPTheorem42
