/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.FiniteVariation.VariationDirection
import FTAPTheorem42.Stochastic.Memin.PathwiseStieltjesControl
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableRealizationModel

/-!
# Pathwise Stieltjes calculus for realized stochastic integrals

The finite-variation component of an actual stochastic integral is the
pathwise Stieltjes integral of its predictable integrand against the source
finite-variation component.  This module records that standard primitive only
on the carrier selected by an `SIntegrableRealizationModel`; it does not make
the generally false assertion for every freely constructible raw
`SIntegrableStrategy` record.  It then identifies the intrinsic pathwise
Radon--Nikodym direction with the normalized Doléans direction and supplies
the local `S¹` predictable-limit consumer used after Lemma 4.11.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrableFiniteVariationBridge

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}
  {H : SIntegrableStrategy D}

/-- The normalized Doléans direction agrees pathwise almost everywhere with
the intrinsic Radon--Nikodym direction of the signed Stieltjes measure. -/
theorem jumpCorrectedCanonicalVariationDensity_ae_eq_variationDirection
    (E : SIntegrableFiniteVariationBridge H) :
    ∀ᵐ ω ∂μ,
      (fun t => jumpCorrectedCanonicalVariationDensity E (t, ω)) =ᵐ[
        (FiniteVariationPath.signedMeasure
          (H.finiteVariationPart_isBoundedVariation ω)).totalVariation]
        FiniteVariationPath.variationDirection
          (H.finiteVariationPart_isBoundedVariation ω) := by
  filter_upwards [signedMeasure_finiteVariationPart_eq_withDensity_ae E]
      with ω hDoleans
  let ν := FiniteVariationPath.signedMeasure
    (H.finiteVariationPart_isBoundedVariation ω)
  apply (integrable_jumpCorrectedCanonicalVariationDensity_section E ω)
    |>.ae_eq_of_withDensityᵥ_eq
      (FiniteVariationPath.integrable_variationDirection
        (H.finiteVariationPart_isBoundedVariation ω))
  exact hDoleans.symm.trans
    (FiniteVariationPath.withDensity_variationDirection_eq_signedMeasure
      (H.finiteVariationPart_isBoundedVariation ω)).symm

end SIntegrableFiniteVariationBridge

/-- The finite-variation Stieltjes primitive on the actual carrier selected by
a realization model.  The difference field is precisely the linear closure
used by the Mémin successive-difference argument.  The actual local strategy
`G` carries the source integrator; no predictable-multiplier calculus is
bundled into this capability. -/
structure SIntegrableFiniteVariationStieltjesCalculus
    {S : Process Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ]
    (D : SpecialSemimartingaleDecomposition S ℱ μ)
    (R : SIntegrableRealizationModel D)
    (G : ActualLocallySIntegrableStrategy R) where
  difference_isRealized :
    ∀ H K : ActualSIntegrableStrategy R,
      R.IsRealized
        (SIntegrablePredictableMultiplierLinearL2Calculus.lemma411Difference
          H.val K.val)
  finiteVariationPart_stopped_integrable :
    ∀ (H : ActualSIntegrableStrategy R) (T : ℝ≥0) (hT : 0 < T),
      ∀ᵐ ω ∂μ, Integrable (fun t => H.val.integrand t ω)
        (FiniteVariationPath.signedMeasure
          ((G.deterministicallyStopped T hT).val
            |>.finiteVariationPart_isBoundedVariation ω)).totalVariation
  finiteVariationPart_stopped_signedMeasure :
    ∀ (H : ActualSIntegrableStrategy R) (T : ℝ≥0) (hT : 0 < T),
      ∀ᵐ ω ∂μ,
        (FiniteVariationPath.signedMeasure
          ((G.deterministicallyStopped T hT).val
            |>.finiteVariationPart_isBoundedVariation ω)).totalVariation.withDensityᵥ
              (fun t =>
                FiniteVariationPath.variationDirection
                    ((G.deterministicallyStopped T hT).val
                      |>.finiteVariationPart_isBoundedVariation ω) t *
                  H.val.integrand t ω) =
          FiniteVariationPath.signedMeasure
            (((H.val.toLocally.deterministicallyStopped T hT
              ).finiteVariationPart_isBoundedVariation ω))

namespace SIntegrableFiniteVariationStieltjesCalculus

open SIntegrableFiniteVariationBridge
open SIntegrablePredictableMultiplierLinearL2Calculus

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}
  {R : SIntegrableRealizationModel D}
  {G : ActualLocallySIntegrableStrategy R}

/-- The actual strategy difference selected by the linear-closure field. -/
noncomputable def difference
    (C : SIntegrableFiniteVariationStieltjesCalculus D R G)
    (H K : ActualSIntegrableStrategy R) : ActualSIntegrableStrategy R :=
  ⟨lemma411Difference H.val K.val, C.difference_isRealized H K⟩

/-- The standard Stieltjes primitive supplies pathwise integrability for a
successive strategy difference at every finite horizon. -/
theorem meminIntegrandDifference_stopped_pathIntegrable
    (C : SIntegrableFiniteVariationStieltjesCalculus D R G)
    (H K : ActualSIntegrableStrategy R) (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂μ, Integrable
      (fun t => meminIntegrandDifference H.val K.val (t, ω))
      (FiniteVariationPath.signedMeasure
        ((G.val.deterministicallyStopped T hT
          ).finiteVariationPart_isBoundedVariation ω)).totalVariation := by
  simpa only [difference,
    ActualLocallySIntegrableStrategy.deterministicallyStopped,
    meminIntegrandDifference, lemma411Difference,
    SIntegrableStrategy.subOfRightContinuous,
    SIntegrableStrategy.add_of_rightContinuous, SIntegrableStrategy.neg,
    sub_eq_add_neg]
    using C.finiteVariationPart_stopped_integrable
      (C.difference H K) T hT

/-- The same primitive, after identifying the intrinsic and Doléans
directions, supplies exactly the stopped-output density identity consumed by
the Mémin local `S¹` argument. -/
theorem meminIntegrandDifference_stopped_pathDensity
    (C : SIntegrableFiniteVariationStieltjesCalculus D R G)
    (H K : ActualSIntegrableStrategy R) (T : ℝ≥0) (hT : 0 < T)
    (source : SIntegrableFiniteVariationBridge
      (G.val.deterministicallyStopped T hT)) :
    ∀ᵐ ω ∂μ,
      (FiniteVariationPath.signedMeasure
        ((G.val.deterministicallyStopped T hT
          ).finiteVariationPart_isBoundedVariation ω)).totalVariation.withDensityᵥ
            (fun t => jumpCorrectedCanonicalVariationDensity source (t, ω) *
              meminIntegrandDifference H.val K.val (t, ω)) =
        FiniteVariationPath.signedMeasure
          (((lemma411Difference H.val K.val).toLocally
            |>.deterministicallyStopped T hT
            ).finiteVariationPart_isBoundedVariation ω) := by
  filter_upwards [C.finiteVariationPart_stopped_signedMeasure
      (C.difference H K) T hT,
    source.jumpCorrectedCanonicalVariationDensity_ae_eq_variationDirection]
      with ω hStieltjes hDirection
  refine (WithDensityᵥEq.congr_ae ?_).trans hStieltjes
  filter_upwards [hDirection] with t ht
  simp only [difference,
    ActualLocallySIntegrableStrategy.deterministicallyStopped,
    meminIntegrandDifference, lemma411Difference,
    SIntegrableStrategy.subOfRightContinuous,
    SIntegrableStrategy.add_of_rightContinuous, SIntegrableStrategy.neg,
    sub_eq_add_neg]
  rw [ht]

/-- On every deterministic finite horizon, summable finite-variation output
differences make the canonical predictable `limUnder` integrable against the
stopped source variation.  The original integrands converge to it both
almost everywhere and in pathwise `L¹`. -/
theorem meminLimitIntegrand_stopped_path_l1
    (C : SIntegrableFiniteVariationStieltjesCalculus D R G)
    (L : ℕ → ActualSIntegrableStrategy R)
    (hVariationSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      lemma411DifferenceTotalVariation (L (k + 1)).val (L k).val ω))
    (hMartingaleSummable : ∀ T, ∀ᵐ ω ∂μ, Summable (fun k =>
      meminMartingaleDifferenceEnvelope
        (ActualSIntegrableStrategy.rawSequence L) T k ω)) :
    ∀ r, ∀ᵐ ω ∂μ,
      Integrable (fun t => meminLimitIntegrand
        (ActualSIntegrableStrategy.rawSequence L) t ω)
        (FiniteVariationPath.signedMeasure
          ((G.val.deterministicallyStopped ((r + 1 : ℕ) : ℝ≥0) (by positivity)
            ).finiteVariationPart_isBoundedVariation ω)).totalVariation ∧
      (∀ᵐ t ∂(FiniteVariationPath.signedMeasure
          ((G.val.deterministicallyStopped ((r + 1 : ℕ) : ℝ≥0) (by positivity)
            ).finiteVariationPart_isBoundedVariation ω)).totalVariation,
        Tendsto (fun n => (L n).val.integrand t ω) atTop
          (𝓝 (meminLimitIntegrand
            (ActualSIntegrableStrategy.rawSequence L) t ω))) ∧
      Tendsto (fun n => ∫⁻ t,
          edist ((L n).val.integrand t ω)
            (meminLimitIntegrand
              (ActualSIntegrableStrategy.rawSequence L) t ω)
          ∂(FiniteVariationPath.signedMeasure
            ((G.val.deterministicallyStopped ((r + 1 : ℕ) : ℝ≥0) (by positivity)
              ).finiteVariationPart_isBoundedVariation ω)).totalVariation)
        atTop (𝓝 0) := by
  intro r
  let T : ℝ≥0 := ((r + 1 : ℕ) : ℝ≥0)
  have hT : 0 < T := by
    dsimp only [T]
    positivity
  let source := meminLocalS1SourceFiniteVariationBridge G.val T hT
    (ActualSIntegrableStrategy.rawSequence L) hVariationSummable
      (hMartingaleSummable T)
  have hAllIntegrable : ∀ᵐ ω ∂μ, ∀ k,
      Integrable (fun t => (L k).val.integrand t ω)
        (FiniteVariationPath.signedMeasure
          ((G.val.deterministicallyStopped T hT
            ).finiteVariationPart_isBoundedVariation ω)).totalVariation :=
    eventually_countable_forall.2 fun k =>
      C.finiteVariationPart_stopped_integrable (L k) T hT
  have hAllDensity : ∀ᵐ ω ∂μ, ∀ k,
      (FiniteVariationPath.signedMeasure
        ((G.val.deterministicallyStopped T hT
          ).finiteVariationPart_isBoundedVariation ω)).totalVariation.withDensityᵥ
            (fun t => jumpCorrectedCanonicalVariationDensity source (t, ω) *
              meminIntegrandDifference (L (k + 1)).val (L k).val (t, ω)) =
        FiniteVariationPath.signedMeasure
          (((lemma411Difference (L (k + 1)).val (L k).val).toLocally
            |>.deterministicallyStopped T hT
            ).finiteVariationPart_isBoundedVariation ω) :=
    eventually_countable_forall.2 fun k =>
      C.meminIntegrandDifference_stopped_pathDensity
        (L (k + 1)) (L k) T hT source
  have hAllDifferenceIntegrable : ∀ᵐ ω ∂μ, ∀ k,
      Integrable
        (fun t => meminIntegrandDifference
          (L (k + 1)).val (L k).val (t, ω))
        (FiniteVariationPath.signedMeasure
          ((G.val.deterministicallyStopped T hT
            ).finiteVariationPart_isBoundedVariation ω)).totalVariation :=
    eventually_countable_forall.2 fun k =>
      C.meminIntegrandDifference_stopped_pathIntegrable
        (L (k + 1)) (L k) T hT
  filter_upwards [hVariationSummable, hAllIntegrable, hAllDensity,
      hAllDifferenceIntegrable,
      abs_jumpCorrectedCanonicalVariationDensity_ae_eq_one_pathwise source]
      with ω hVariation hIntegrable hDensity hDifferenceIntegrable hUnit
  let ν := (FiniteVariationPath.signedMeasure
    ((G.val.deterministicallyStopped T hT
      ).finiteVariationPart_isBoundedVariation ω)).totalVariation
  have hStepEq : ∀ k,
      (∫⁻ t, edist ((L (k + 1)).val.integrand t ω)
        ((L k).val.integrand t ω) ∂ν) =
        (FiniteVariationPath.signedMeasure
          (((lemma411Difference (L (k + 1)).val (L k).val).toLocally
            |>.deterministicallyStopped T hT
            ).finiteVariationPart_isBoundedVariation ω)).totalVariation
              Set.univ := by
    intro k
    have h :=
      lintegral_meminIntegrandDifference_eq_pathTotalVariation_of_density
        source (L (k + 1)).val (L k).val ω
        (hDifferenceIntegrable k) hUnit (hDensity k)
    simpa only [ν, edist_dist, Real.dist_eq,
      meminIntegrandDifference] using h
  have hSteps : (∑' k,
      ∫⁻ t, edist ((L (k + 1)).val.integrand t ω)
        ((L k).val.integrand t ω) ∂ν) ≠ ∞ := by
    apply ne_top_of_le_ne_top hVariation.tsum_ofReal_ne_top
    apply ENNReal.tsum_le_tsum
    intro k
    rw [hStepEq k]
    let η := (FiniteVariationPath.signedMeasure
      (((lemma411Difference (L (k + 1)).val (L k).val).toLocally
        |>.deterministicallyStopped T hT
        ).finiteVariationPart_isBoundedVariation ω)).totalVariation
    let : IsFiniteMeasure η := by
      dsimp only [η]
      unfold SignedMeasure.totalVariation
      infer_instance
    rw [← ofReal_measureReal (measure_ne_top η Set.univ)]
    exact ENNReal.ofReal_le_ofReal
      (deterministicallyStopped_lemma411Difference_totalVariation_le
        (L (k + 1)).val (L k).val T hT ω)
  have hLimit := MeminL1.integrable_l1_limit_of_summable_steps
    (ν := ν) (fun n t => (L n).val.integrand t ω)
    (fun n => (hIntegrable n).aestronglyMeasurable)
    (hIntegrable 0) hSteps
  simpa only [T, ν, meminLimitIntegrand] using hLimit

end SIntegrableFiniteVariationStieltjesCalculus

end FTAPTheorem42
