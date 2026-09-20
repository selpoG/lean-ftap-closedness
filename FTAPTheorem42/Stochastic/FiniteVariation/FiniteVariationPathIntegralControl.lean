import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationIntegralProcessGeneralMeasure
import FTAPTheorem42.Stochastic.FiniteVariation.CanonicalVariationControl

/-! # Measurable pathwise integral control from the canonical variation measure -/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal

namespace FTAPTheorem42.SIntegrableFiniteVariationBridge

variable {Omega : Type*} [MeasurableSpace Omega]
  {S : Process Omega} {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu] [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu} {G : SIntegrableStrategy D}

omit [SigmaFiniteFiltration mu F] in
theorem finiteVariationPathIntegral_toReal_eLpNorm_le
    (E : SIntegrableFiniteVariationBridge G)
    {K L : Process Omega}
    (hK : IsStronglyPredictable F K)
    (hL : IsStronglyPredictable F L) :
    eLpNorm
        (fun omega =>
          (∫⁻ t, ‖K t omega - L t omega‖ₑ
            ∂(FiniteVariationPath.signedMeasure
              (G.finiteVariationPart_isBoundedVariation omega)).totalVariation).toReal)
        1 E.referenceMeasure ≤
      eLpNorm (Function.uncurry K - Function.uncurry L) 1
        (canonicalVariationMeasure E) := by
  let V : Omega → ENNReal := fun omega =>
    ∫⁻ t, ‖K t omega - L t omega‖ₑ
      ∂(FiniteVariationPath.signedMeasure
        (G.finiteVariationPart_isBoundedVariation omega)).totalVariation
  have hVMeas : Measurable V := by
    let kappa := canonicalTotalVariationKernel E
    let : IsFiniteKernel kappa :=
      canonicalTotalVariationKernel.instIsFiniteKernel E
    have hProduct : Measurable fun p : NNReal × Omega =>
        ‖K p.1 p.2 - L p.1 p.2‖ₑ :=
      (hK.sub hL).enorm.mono
        (PredictableKernelMeasure.predictable_le_prod F) le_rfl
    have hKernel : Measurable fun omega =>
        ∫⁻ t, ‖K t omega - L t omega‖ₑ ∂kappa omega := by
      exact (hProduct.comp measurable_swap).lintegral_kernel_prod_right'
    have hWeighted : Measurable (fun omega =>
        (E.referenceDensity omega : ENNReal) * V omega) := by
      convert hKernel using 1
      funext omega
      change (E.referenceDensity omega : ENNReal) *
          (∫⁻ t, ‖K t omega - L t omega‖ₑ
            ∂(FiniteVariationPath.signedMeasure
              (G.finiteVariationPart_isBoundedVariation omega)).totalVariation) = _
      rw [canonicalTotalVariationKernel_apply, lintegral_smul_measure]
      simp only [ENNReal.smul_def, smul_eq_mul]
    have hDensity : Measurable (fun omega =>
        (E.referenceDensity omega : ENNReal)) :=
      E.referenceDensity_measurable.coe_nnreal_ennreal
    have hDiv : Measurable (fun omega =>
        ((E.referenceDensity omega : ENNReal) * V omega) /
          (E.referenceDensity omega : ENNReal)) :=
      hWeighted.div hDensity
    convert hDiv using 1
    funext omega
    rw [div_eq_mul_inv, mul_assoc, mul_comm (V omega), ← mul_assoc,
      ENNReal.mul_inv_cancel]
    · simp
    · exact_mod_cast (E.referenceDensity_pos omega).ne'
    · exact ENNReal.coe_ne_top
  let VtoReal : Omega → Real := fun omega => (V omega).toReal
  have hVtoReal : StronglyMeasurable VtoReal :=
    hVMeas.ennreal_toReal.stronglyMeasurable
  have hVBound : ∀ omega, ‖VtoReal omega‖ₑ ≤ V omega := by
    intro omega
    change ‖(V omega).toReal‖ₑ ≤ V omega
    rw [Real.enorm_eq_ofReal_abs,
      abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal_le
  rw [eLpNorm_one_eq_lintegral_enorm hVtoReal.aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_enorm (hK.sub hL).aestronglyMeasurable]
  change (∫⁻ omega, ‖VtoReal omega‖ₑ ∂E.referenceMeasure) ≤ _
  calc
    (∫⁻ omega, ‖VtoReal omega‖ₑ ∂E.referenceMeasure) =
        ∫⁻ omega, (E.referenceDensity omega : ENNReal) *
          ‖VtoReal omega‖ₑ ∂mu := by
      rw [SIntegrableFiniteVariationBridge.referenceMeasure]
      exact lintegral_withDensity_eq_lintegral_mul mu
        E.referenceDensity_measurable.coe_nnreal_ennreal hVtoReal.measurable.enorm
    _ ≤ ∫⁻ omega, (E.referenceDensity omega : ENNReal) * V omega ∂mu := by
      apply lintegral_mono
      intro omega
      exact mul_le_mul_right (hVBound omega) _
    _ = ∫⁻ p, ‖(Function.uncurry K - Function.uncurry L) p‖ₑ
        ∂canonicalVariationMeasure E := by
      symm
      rw [lintegral_canonicalVariationMeasure_eq_lintegral_pathVariation
        E (hK.sub hL).enorm]
      rfl

omit [SigmaFiniteFiltration mu F] in
theorem finiteVariationPathIntegral_toReal_stronglyMeasurable
    (E : SIntegrableFiniteVariationBridge G)
    {K L : Process Omega}
    (hK : IsStronglyPredictable F K)
    (hL : IsStronglyPredictable F L) :
    StronglyMeasurable (fun omega =>
      (∫⁻ t, ‖K t omega - L t omega‖ₑ
        ∂(FiniteVariationPath.signedMeasure
          (G.finiteVariationPart_isBoundedVariation omega)).totalVariation).toReal) := by
  let V : Omega → ENNReal := fun omega =>
    ∫⁻ t, ‖K t omega - L t omega‖ₑ
      ∂(FiniteVariationPath.signedMeasure
        (G.finiteVariationPart_isBoundedVariation omega)).totalVariation
  have hVMeas : Measurable V := by
    let kappa := canonicalTotalVariationKernel E
    let : IsFiniteKernel kappa :=
      canonicalTotalVariationKernel.instIsFiniteKernel E
    have hProduct : Measurable fun p : NNReal × Omega =>
        ‖K p.1 p.2 - L p.1 p.2‖ₑ :=
      (hK.sub hL).enorm.mono
        (PredictableKernelMeasure.predictable_le_prod F) le_rfl
    have hKernel : Measurable fun omega =>
        ∫⁻ t, ‖K t omega - L t omega‖ₑ ∂kappa omega := by
      exact (hProduct.comp measurable_swap).lintegral_kernel_prod_right'
    have hWeighted : Measurable (fun omega =>
        (E.referenceDensity omega : ENNReal) * V omega) := by
      convert hKernel using 1
      funext omega
      change (E.referenceDensity omega : ENNReal) *
          (∫⁻ t, ‖K t omega - L t omega‖ₑ
            ∂(FiniteVariationPath.signedMeasure
              (G.finiteVariationPart_isBoundedVariation omega)).totalVariation) = _
      rw [canonicalTotalVariationKernel_apply, lintegral_smul_measure]
      simp only [ENNReal.smul_def, smul_eq_mul]
    have hDensity : Measurable (fun omega =>
        (E.referenceDensity omega : ENNReal)) :=
      E.referenceDensity_measurable.coe_nnreal_ennreal
    have hDiv : Measurable (fun omega =>
        ((E.referenceDensity omega : ENNReal) * V omega) /
          (E.referenceDensity omega : ENNReal)) :=
      hWeighted.div hDensity
    convert hDiv using 1
    funext omega
    rw [div_eq_mul_inv, mul_assoc, mul_comm (V omega), ← mul_assoc,
      ENNReal.mul_inv_cancel]
    · simp
    · exact_mod_cast (E.referenceDensity_pos omega).ne'
    · exact ENNReal.coe_ne_top
  have hVtoReal : StronglyMeasurable (fun omega => (V omega).toReal) :=
    hVMeas.ennreal_toReal.stronglyMeasurable
  simpa only [V] using hVtoReal

omit [SigmaFiniteFiltration mu F] in
/-- A regular cumulative integral has total variation bounded by the absolute
coefficient integral, also for unbounded variation-integrable coefficients. -/
theorem totalVariation_cumulativeIntegral_le
    (E : SIntegrableFiniteVariationBridge G)
    {K : Process Omega} (hK : IsStronglyPredictable F K) (omega : Omega)
    (hIntegrable : Integrable (fun u => K u omega)
      (FiniteVariationPath.signedMeasure
        (G.finiteVariationPart_isBoundedVariation omega)).totalVariation)
    {B : NNReal → Real} (hB : BoundedVariationOn B univ)
    (hRight : ∀ t, ContinuousWithinAt B (Ici t) t)
    (hEq : ∀ t, B t - B 0 = finiteVariationIntegralProcess E K t omega) :
    (FiniteVariationPath.signedMeasure hB).totalVariation univ ≤
      ∫⁻ t, ‖K t omega‖ₑ ∂(FiniteVariationPath.signedMeasure
        (G.finiteVariationPart_isBoundedVariation omega)).totalVariation := by
  let ν := (FiniteVariationPath.signedMeasure
    (G.finiteVariationPart_isBoundedVariation omega)).totalVariation
  have hDensity : Integrable (fun t => finiteVariationIntegralDensity E K (t, omega)) ν :=
    integrable_finiteVariationIntegralDensity_section_of_integrable E hK omega hIntegrable
  rw [signedMeasure_totalVariation_eq_variation,
    ← withDensity_finiteVariationIntegralDensity_eq_signedMeasure_of_eq
      E hK omega hIntegrable hB hRight hEq,
    Measure.variation_withDensityᵥ hDensity,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  apply lintegral_mono
  intro t
  change ‖jumpCorrectedCanonicalVariationDensity E (t, omega) * K t omega‖ₑ ≤ _
  rw [enorm_mul]
  calc
    _ ≤ 1 * ‖K t omega‖ₑ := by
      apply mul_le_mul_left
      rw [Real.enorm_eq_ofReal_abs]
      exact (ENNReal.ofReal_le_ofReal
        (abs_jumpCorrectedCanonicalVariationDensity_le_one E (t, omega))).trans (by simp)
    _ = _ := one_mul _

end FTAPTheorem42.SIntegrableFiniteVariationBridge
