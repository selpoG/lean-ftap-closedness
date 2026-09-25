/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Predictable.PredictableCommonSimpleApproximation
import FTAPTheorem42.Stochastic.FiniteVariation.CanonicalVariationControl

/-!
# Completing finite-variation terminal integrals in predictable `L¹`

For a bounded strongly predictable coefficient, the pathwise signed
Stieltjes integral is a measurable terminal random variable.  Its `L¹`
distance is bounded by the predictable canonical-variation `L¹` distance.
Consequently the measure-independent common simple approximations give a
concrete Cauchy sequence of terminal finite-variation integrals.  This is the
finite-variation counterpart of the finite-grid martingale terminal
completion. The statements here concern terminal random variables;
process-valued integrals are constructed in `FiniteVariationIntegralProcess`.
-/

open Filter Function MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace FiniteVariationPath

/-- The norm of a pathwise signed Stieltjes integral is bounded by the
integral of the coefficient norm against Jordan total variation. -/
theorem enorm_integral_le_lintegral_enorm
    {A : ℝ≥0 → ℝ} (hA : BoundedVariationOn A Set.univ)
    (K : ℝ≥0 → ℝ) :
    ‖integral hA K‖ₑ ≤
      ∫⁻ t, ‖K t‖ₑ ∂(signedMeasure hA).totalVariation := by
  unfold integral
  have h := VectorMeasure.enorm_integral_le_lintegral_enorm
    (f := K) (μ := (signedMeasure hA : VectorMeasure ℝ≥0 ℝ))
    (B := ContinuousLinearMap.lsmul ℝ ℝ)
  rw [← signedMeasure_totalVariation_eq_variation] at h
  simpa using h

end FiniteVariationPath

namespace SIntegrableFiniteVariationBridge

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}
  {H : SIntegrableStrategy D}

/-- The pathwise terminal signed Stieltjes integral of a predictable
coefficient against the finite-variation component represented by `E`. -/
noncomputable def finiteVariationTerminalIntegral
    (_E : SIntegrableFiniteVariationBridge H) (K : Process Ω) : Ω → ℝ :=
  fun ω => FiniteVariationPath.integral
    (H.finiteVariationPart_isBoundedVariation ω) (fun t => K t ω)

omit [IsFiniteMeasure μ] in
private theorem section_integrable_of_bound
    {K : Process Ω} (hK : IsStronglyPredictable ℱ K)
    {C : ℝ} (hKBound : ∀ t ω, |K t ω| ≤ C) (ω : Ω) :
    Integrable (fun t => K t ω)
      (FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation ω)).totalVariation := by
  let ν := (FiniteVariationPath.signedMeasure
    (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
  let : IsFiniteMeasure ν := by
    dsimp only [ν]
    unfold SignedMeasure.totalVariation
    infer_instance
  have hSection : StronglyMeasurable fun t => K t ω :=
    (hK.mono (PredictableKernelMeasure.predictable_le_prod ℱ))
      |>.comp_measurable measurable_prodMk_right
  apply (integrable_const C).mono' hSection.aestronglyMeasurable
  filter_upwards with t
  exact hKBound t ω

/-- For a bounded predictable coefficient, the pathwise terminal Stieltjes
integral is a strongly measurable random variable. -/
theorem finiteVariationTerminalIntegral_stronglyMeasurable
    (E : SIntegrableFiniteVariationBridge H)
    {K : Process Ω} (hK : IsStronglyPredictable ℱ K)
    {C : ℝ} (hKBound : ∀ t ω, |K t ω| ≤ C) :
    StronglyMeasurable (finiteVariationTerminalIntegral E K) := by
  let : IsFiniteKernel (canonicalPositiveKernel E) :=
    isFiniteKernel_canonicalPositiveKernel E
  let : IsFiniteKernel (canonicalNegativeKernel E) :=
    isFiniteKernel_canonicalNegativeKernel E
  let κp := canonicalPositiveKernel E
  let κn := canonicalNegativeKernel E
  have hKProduct : StronglyMeasurable (Function.uncurry K) :=
    hK.mono (PredictableKernelMeasure.predictable_le_prod ℱ)
  have hp : StronglyMeasurable fun ω => ∫ t, K t ω ∂κp ω :=
    hKProduct.integral_kernel_prod_left
  have hn : StronglyMeasurable fun ω => ∫ t, K t ω ∂κn ω :=
    hKProduct.integral_kernel_prod_left
  have hDensity : StronglyMeasurable fun ω => (E.referenceDensity ω : ℝ) :=
    E.referenceDensity_measurable.coe_nnreal_real.stronglyMeasurable
  have hRepresentation : finiteVariationTerminalIntegral E K =
      fun ω => ((∫ t, K t ω ∂κp ω) - ∫ t, K t ω ∂κn ω) /
        (E.referenceDensity ω : ℝ) := by
    funext ω
    have hKInt := section_integrable_of_bound (H := H) hK hKBound ω
    have hKp : Integrable (fun t => K t ω)
        (FiniteVariationKernel.positivePathMeasure
          H.finiteVariationPart_isBoundedVariation ω) :=
      hKInt.mono_measure (by
        rw [show (FiniteVariationPath.signedMeasure
            (H.finiteVariationPart_isBoundedVariation ω)).totalVariation =
          FiniteVariationKernel.positivePathMeasure
              H.finiteVariationPart_isBoundedVariation ω +
            FiniteVariationKernel.negativePathMeasure
              H.finiteVariationPart_isBoundedVariation ω by rfl]
        exact Measure.le_add_right le_rfl)
    have hKn : Integrable (fun t => K t ω)
        (FiniteVariationKernel.negativePathMeasure
          H.finiteVariationPart_isBoundedVariation ω) :=
      hKInt.mono_measure (by
        rw [show (FiniteVariationPath.signedMeasure
            (H.finiteVariationPart_isBoundedVariation ω)).totalVariation =
          FiniteVariationKernel.positivePathMeasure
              H.finiteVariationPart_isBoundedVariation ω +
            FiniteVariationKernel.negativePathMeasure
              H.finiteVariationPart_isBoundedVariation ω by rfl]
        exact Measure.le_add_left le_rfl)
    rw [finiteVariationTerminalIntegral,
      FiniteVariationKernel.pathIntegral_eq_positive_sub_negative
        H.finiteVariationPart_isBoundedVariation ω (fun t => K t ω) hKp hKn,
      canonicalPositiveKernel_apply, canonicalNegativeKernel_apply,
      integral_smul_nnreal_measure, integral_smul_nnreal_measure]
    have hDensityNe : (E.referenceDensity ω : ℝ) ≠ 0 := by
      exact_mod_cast (E.referenceDensity_pos ω).ne'
    field_simp
    change (_ - _) * (E.referenceDensity ω : ℝ) =
      (E.referenceDensity ω : ℝ) * _ -
        (E.referenceDensity ω : ℝ) * _
    ring
  rw [hRepresentation]
  exact (hp.sub hn).div hDensity

/-- Predictable `L¹` control dominates the terminal Stieltjes `L¹` norm. -/
theorem eLpNorm_finiteVariationTerminalIntegral_le
    (E : SIntegrableFiniteVariationBridge H)
    {K : Process Ω} (hK : IsStronglyPredictable ℱ K)
    {C : ℝ} (hKBound : ∀ t ω, |K t ω| ≤ C) :
    eLpNorm (finiteVariationTerminalIntegral E K) 1 E.referenceMeasure ≤
      eLpNorm (Function.uncurry K) 1 (canonicalVariationMeasure E) := by
  have hTerminal := finiteVariationTerminalIntegral_stronglyMeasurable
    E hK hKBound
  rw [eLpNorm_one_eq_lintegral_enorm hTerminal.aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_enorm hK.aestronglyMeasurable]
  change (∫⁻ ω, ‖finiteVariationTerminalIntegral E K ω‖ₑ
      ∂μ.withDensity (fun ω => (E.referenceDensity ω : ℝ≥0∞))) ≤ _
  rw [lintegral_withDensity_eq_lintegral_mul μ
    E.referenceDensity_measurable.coe_nnreal_ennreal hTerminal.enorm]
  calc
    (∫⁻ ω, (E.referenceDensity ω : ℝ≥0∞) *
        ‖finiteVariationTerminalIntegral E K ω‖ₑ ∂μ) ≤
        ∫⁻ ω, (E.referenceDensity ω : ℝ≥0∞) *
          ∫⁻ t, ‖K t ω‖ₑ
            ∂(FiniteVariationPath.signedMeasure
              (H.finiteVariationPart_isBoundedVariation ω)).totalVariation
          ∂μ := by
      apply lintegral_mono
      intro ω
      exact mul_le_mul_right
        (FiniteVariationPath.enorm_integral_le_lintegral_enorm
          (H.finiteVariationPart_isBoundedVariation ω) (fun t => K t ω))
        (E.referenceDensity ω : ℝ≥0∞)
    _ = ∫⁻ p, ‖Function.uncurry K p‖ₑ
          ∂canonicalVariationMeasure E := by
      symm
      exact lintegral_canonicalVariationMeasure_eq_lintegral_pathVariation E
        hK.enorm

/-- A bounded predictable terminal Stieltjes integral belongs to `L¹` as
soon as its coefficient belongs to the canonical variation `L¹` space. -/
theorem finiteVariationTerminalIntegral_memLp_one
    (E : SIntegrableFiniteVariationBridge H)
    {K : Process Ω} (hK : IsStronglyPredictable ℱ K)
    {C : ℝ} (hKBound : ∀ t ω, |K t ω| ≤ C)
    (hKMemLp : MemLp (Function.uncurry K) 1
      (canonicalVariationMeasure E)) :
    MemLp (finiteVariationTerminalIntegral E K) 1 E.referenceMeasure := by
  exact (eLpNorm_finiteVariationTerminalIntegral_le E hK hKBound).trans_lt
    hKMemLp.eLpNorm_lt_top

/-- Pathwise terminal Stieltjes integration is additive with respect to
subtraction on bounded predictable coefficients. -/
theorem finiteVariationTerminalIntegral_sub
    (E : SIntegrableFiniteVariationBridge H)
    {K L : Process Ω} (hK : IsStronglyPredictable ℱ K)
    (hL : IsStronglyPredictable ℱ L)
    {C D : ℝ} (hKBound : ∀ t ω, |K t ω| ≤ C)
    (hLBound : ∀ t ω, |L t ω| ≤ D) :
    finiteVariationTerminalIntegral E (K - L) =
      finiteVariationTerminalIntegral E K -
        finiteVariationTerminalIntegral E L := by
  funext ω
  let η := FiniteVariationPath.signedMeasure
    (H.finiteVariationPart_isBoundedVariation ω)
  have hKInt := section_integrable_of_bound (H := H) hK hKBound ω
  have hLInt := section_integrable_of_bound (H := H) hL hLBound ω
  have hKVector : (η : VectorMeasure ℝ≥0 ℝ).Integrable
      (fun t => K t ω) := by
    change Integrable (fun t => K t ω) (η : VectorMeasure ℝ≥0 ℝ).variation
    rw [← signedMeasure_totalVariation_eq_variation]
    exact hKInt
  have hLVector : (η : VectorMeasure ℝ≥0 ℝ).Integrable
      (fun t => L t ω) := by
    change Integrable (fun t => L t ω) (η : VectorMeasure ℝ≥0 ℝ).variation
    rw [← signedMeasure_totalVariation_eq_variation]
    exact hLInt
  unfold finiteVariationTerminalIntegral FiniteVariationPath.integral
  exact VectorMeasure.integral_sub hKVector hLVector

/-- The terminal `L¹` distance contracts under pathwise finite-variation
integration. -/
theorem eLpNorm_finiteVariationTerminalIntegral_sub_le
    (E : SIntegrableFiniteVariationBridge H)
    {K L : Process Ω} (hK : IsStronglyPredictable ℱ K)
    (hL : IsStronglyPredictable ℱ L)
    {C D : ℝ} (hKBound : ∀ t ω, |K t ω| ≤ C)
    (hLBound : ∀ t ω, |L t ω| ≤ D) :
    eLpNorm
        (finiteVariationTerminalIntegral E K -
          finiteVariationTerminalIntegral E L)
        1 E.referenceMeasure ≤
      eLpNorm (Function.uncurry K - Function.uncurry L) 1
        (canonicalVariationMeasure E) := by
  have hSub : IsStronglyPredictable ℱ (K - L) := hK.sub hL
  have hSubBound : ∀ t ω, |(K - L) t ω| ≤ C + D := by
    intro t ω
    exact (abs_sub (K t ω) (L t ω)).trans
      (add_le_add (hKBound t ω) (hLBound t ω))
  rw [← finiteVariationTerminalIntegral_sub E hK hL hKBound hLBound]
  convert eLpNorm_finiteVariationTerminalIntegral_le E hSub hSubBound using 1
  congr 1

/-- The terminal Stieltjes integral of the common predictable simple
approximation. -/
noncomputable def commonFiniteVariationTerminalApproximation
    (E : SIntegrableFiniteVariationBridge H)
    (f : Process Ω) (hf : IsStronglyPredictable ℱ f) (n : ℕ) : Ω → ℝ :=
  finiteVariationTerminalIntegral E
    (predictableCommonSimpleApproximation f hf n)

/-- Every common terminal finite-variation approximation belongs to
`L¹` under the bridge reference measure. -/
theorem commonFiniteVariationTerminalApproximation_memLp
    (E : SIntegrableFiniteVariationBridge H)
    (f : Process Ω) (hf : IsStronglyPredictable ℱ f)
    (hF : MemLp (Function.uncurry f) 1 (canonicalVariationMeasure E))
    (n : ℕ) :
    MemLp (commonFiniteVariationTerminalApproximation E f hf n) 1
      E.referenceMeasure := by
  obtain ⟨C, hC⟩ :=
    exists_predictableCommonSimpleApproximation_bound f hf n
  apply finiteVariationTerminalIntegral_memLp_one E
    (predictableCommonSimpleApproximation_isStronglyPredictable f hf n)
    hC
  simpa only [uncurry_predictableCommonSimpleApproximation] using
    predictableCommonSimpleApproximationRaw_memLp f hf
      (canonicalVariationMeasure E) 1 hF n

/-- The common terminal approximation as an element of the completed
reference-measure `L¹` space. -/
noncomputable def commonFiniteVariationTerminalApproximationLp
    (E : SIntegrableFiniteVariationBridge H)
    (f : Process Ω) (hf : IsStronglyPredictable ℱ f)
    (hF : MemLp (Function.uncurry f) 1 (canonicalVariationMeasure E))
    (n : ℕ) : Lp ℝ 1 E.referenceMeasure :=
  (commonFiniteVariationTerminalApproximation_memLp E f hf hF n).toLp
    (commonFiniteVariationTerminalApproximation E f hf n)

/-- Terminal `L¹` distances between two common approximations are bounded
by their predictable canonical-variation distances. -/
theorem dist_commonFiniteVariationTerminalApproximationLp_le
    (E : SIntegrableFiniteVariationBridge H)
    (f : Process Ω) (hf : IsStronglyPredictable ℱ f)
    (hF : MemLp (Function.uncurry f) 1 (canonicalVariationMeasure E))
    (n m : ℕ) :
    dist (commonFiniteVariationTerminalApproximationLp E f hf hF n)
        (commonFiniteVariationTerminalApproximationLp E f hf hF m) ≤
      dist
        ((predictableCommonSimpleApproximationRaw_memLp f hf
          (canonicalVariationMeasure E) 1 hF n).toLp
            (predictableCommonSimpleApproximationRaw f hf n))
        ((predictableCommonSimpleApproximationRaw_memLp f hf
          (canonicalVariationMeasure E) 1 hF m).toLp
            (predictableCommonSimpleApproximationRaw f hf m)) := by
  obtain ⟨C, hC⟩ :=
    exists_predictableCommonSimpleApproximation_bound f hf n
  obtain ⟨D, hD⟩ :=
    exists_predictableCommonSimpleApproximation_bound f hf m
  unfold commonFiniteVariationTerminalApproximationLp
  rw [Lp.dist_edist, Lp.edist_toLp_toLp,
    Lp.dist_edist, Lp.edist_toLp_toLp]
  apply ENNReal.toReal_mono
    ((predictableCommonSimpleApproximationRaw_memLp f hf
      (canonicalVariationMeasure E) 1 hF n).sub
        (predictableCommonSimpleApproximationRaw_memLp f hf
          (canonicalVariationMeasure E) 1 hF m)).eLpNorm_ne_top
  convert eLpNorm_finiteVariationTerminalIntegral_sub_le E
    (predictableCommonSimpleApproximation_isStronglyPredictable f hf n)
    (predictableCommonSimpleApproximation_isStronglyPredictable f hf m)
    hC hD using 1 <;> congr 1

/-- The terminal Stieltjes integrals of the common predictable simple
approximations form a Cauchy sequence in the reference-measure `L¹` space. -/
theorem commonFiniteVariationTerminalApproximationLp_cauchySeq
    (E : SIntegrableFiniteVariationBridge H)
    (f : Process Ω) (hf : IsStronglyPredictable ℱ f)
    (hF : MemLp (Function.uncurry f) 1 (canonicalVariationMeasure E)) :
    CauchySeq (fun n =>
      commonFiniteVariationTerminalApproximationLp E f hf hF n) := by
  have hRawTendsto : Tendsto (fun n =>
      (predictableCommonSimpleApproximationRaw_memLp f hf
        (canonicalVariationMeasure E) 1 hF n).toLp
          (predictableCommonSimpleApproximationRaw f hf n))
      atTop (𝓝 (hF.toLp (Function.uncurry f))) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n => predictableCommonSimpleApproximationRaw f hf n)
      (fun n => predictableCommonSimpleApproximationRaw_memLp f hf
        (canonicalVariationMeasure E) 1 hF n)
      (Function.uncurry f) hF).mpr
    exact predictableCommonSimpleApproximationRaw_tendsto_eLpNorm
      f hf (canonicalVariationMeasure E) 1 (by norm_num) hF
  have hRawCauchy := hRawTendsto.cauchySeq
  rw [Metric.cauchySeq_iff] at hRawCauchy ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hRawCauchy ε hε
  refine ⟨N, fun n hn m hm => ?_⟩
  exact (dist_commonFiniteVariationTerminalApproximationLp_le
    E f hf hF n m).trans_lt (hN n hn m hm)

/-- The concrete completed terminal finite-variation integral of a
predictable canonical-variation `L¹` coefficient. -/
noncomputable def finiteVariationTerminalIntegralLp
    (E : SIntegrableFiniteVariationBridge H)
    (f : Process Ω) (hf : IsStronglyPredictable ℱ f)
    (hF : MemLp (Function.uncurry f) 1 (canonicalVariationMeasure E)) :
    Lp ℝ 1 E.referenceMeasure :=
  limUnder atTop (fun n =>
    commonFiniteVariationTerminalApproximationLp E f hf hF n)

/-- The terminal Stieltjes integrals of the common simple sequence converge
to the concrete completed finite-variation terminal integral. -/
theorem commonFiniteVariationTerminalApproximationLp_tendsto
    (E : SIntegrableFiniteVariationBridge H)
    (f : Process Ω) (hf : IsStronglyPredictable ℱ f)
    (hF : MemLp (Function.uncurry f) 1 (canonicalVariationMeasure E)) :
    Tendsto (fun n =>
      commonFiniteVariationTerminalApproximationLp E f hf hF n)
      atTop (𝓝 (finiteVariationTerminalIntegralLp E f hf hF)) :=
  (commonFiniteVariationTerminalApproximationLp_cauchySeq
    E f hf hF).tendsto_limUnder

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
