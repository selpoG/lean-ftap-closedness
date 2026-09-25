/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.Localization.AEDominatedFiniteVariationBridge
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedM2ARealization
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationStoppedStieltjes
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableCumulativeVariationBridge

/-!
# A finite-variation bridge for a common local refinement

Two local completed schedules may normalize their finite-variation parts by
different equivalent reference measures.  Their pointwise stopping-time
minimum therefore cannot reuse either bridge verbatim.  This module builds a
genuine bridge for a refined source prefix.  Its density is the product of
the two old densities and the canonical normalized density of the refined
prefix.  It is consequently dominated by both old densities, while the last
factor supplies the weighted-variation and `L²` bounds required by the bridge.

If the refined path variation is dominated by an old path variation, every
old variation-`L¹` coefficient transfers to the new canonical variation
measure.  Thus the one new bridge supports coefficients from both schedules;
no equality of their old reference measures is assumed.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace SIntegrableFiniteVariationBridge

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsFiniteMeasure mu]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {H K L : SIntegrableStrategy D}

/-- The sample density used by the common-refinement bridge. -/
noncomputable def commonRefinementReferenceDensity
    (E : SIntegrableFiniteVariationBridge H)
    (E' : SIntegrableFiniteVariationBridge K)
    (L : SIntegrableStrategy D) : Omega -> NNReal :=
  fun omega => E.referenceDensity omega * E'.referenceDensity omega *
    normalizedVariationReferenceDensity L omega

theorem commonRefinementReferenceDensity_measurable
    (E : SIntegrableFiniteVariationBridge H)
    (E' : SIntegrableFiniteVariationBridge K) :
    Measurable (commonRefinementReferenceDensity E E' L) := by
  exact (E.referenceDensity_measurable.mul E'.referenceDensity_measurable).mul
    (normalizedVariationReferenceDensity_measurable
      L.finiteVariationPart_isRightContinuous)

theorem commonRefinementReferenceDensity_pos
    (E : SIntegrableFiniteVariationBridge H)
    (E' : SIntegrableFiniteVariationBridge K) (omega : Omega) :
    0 < commonRefinementReferenceDensity E E' L omega := by
  exact mul_pos (mul_pos (E.referenceDensity_pos omega)
    (E'.referenceDensity_pos omega))
      (normalizedVariationReferenceDensity_pos L omega)

theorem commonRefinementReferenceDensity_le_one
    (E : SIntegrableFiniteVariationBridge H)
    (E' : SIntegrableFiniteVariationBridge K) (omega : Omega) :
    commonRefinementReferenceDensity E E' L omega <= 1 := by
  exact (mul_le_of_le_one_left (by positivity)
    ((mul_le_of_le_one_left (by positivity) (E.referenceDensity_le_one omega)).trans
      (E'.referenceDensity_le_one omega))).trans
        (normalizedVariationReferenceDensity_le_one L omega)

theorem commonRefinementReferenceDensity_le_left
    (E : SIntegrableFiniteVariationBridge H)
    (E' : SIntegrableFiniteVariationBridge K) (omega : Omega) :
    commonRefinementReferenceDensity E E' L omega <= E.referenceDensity omega := by
  unfold commonRefinementReferenceDensity
  rw [mul_assoc]
  calc
    E.referenceDensity omega *
        (E'.referenceDensity omega * normalizedVariationReferenceDensity L omega) <=
      E.referenceDensity omega * 1 :=
        mul_le_mul_of_nonneg_left
          ((mul_le_of_le_one_left (by positivity)
            (E'.referenceDensity_le_one omega)).trans
              (normalizedVariationReferenceDensity_le_one L omega)) (by positivity)
    _ = E.referenceDensity omega := mul_one _

theorem commonRefinementReferenceDensity_le_right
    (E : SIntegrableFiniteVariationBridge H)
    (E' : SIntegrableFiniteVariationBridge K) (omega : Omega) :
    commonRefinementReferenceDensity E E' L omega <= E'.referenceDensity omega := by
  unfold commonRefinementReferenceDensity
  calc
    E.referenceDensity omega * E'.referenceDensity omega *
        normalizedVariationReferenceDensity L omega =
      E'.referenceDensity omega *
        (E.referenceDensity omega * normalizedVariationReferenceDensity L omega) := by
          ring
    _ <= E'.referenceDensity omega := by
      calc
        E'.referenceDensity omega *
            (E.referenceDensity omega * normalizedVariationReferenceDensity L omega) <=
          E'.referenceDensity omega * 1 :=
            mul_le_mul_of_nonneg_left
              ((mul_le_of_le_one_left (by positivity)
                (E.referenceDensity_le_one omega)).trans
                  (normalizedVariationReferenceDensity_le_one L omega)) (by positivity)
        _ = E'.referenceDensity omega := mul_one _

/-- The common-refinement density still normalizes the refined prefix's
whole-axis path variation. -/
theorem commonRefinementReferenceDensity_mul_variation_le_one
    (E : SIntegrableFiniteVariationBridge H)
    (E' : SIntegrableFiniteVariationBridge K) (omega : Omega) :
    (commonRefinementReferenceDensity E E' L omega : ENNReal) *
        (FiniteVariationPath.signedMeasure
          (L.finiteVariationPart_isBoundedVariation omega)).totalVariation
            Set.univ <= 1 := by
  let a : ENNReal := (E.referenceDensity omega : ENNReal) *
    (E'.referenceDensity omega : ENNReal)
  let b : ENNReal :=
    (normalizedVariationReferenceDensity L omega : ENNReal) *
      (FiniteVariationPath.signedMeasure
        (L.finiteVariationPart_isBoundedVariation omega)).totalVariation Set.univ
  calc
    (commonRefinementReferenceDensity E E' L omega : ENNReal) *
        (FiniteVariationPath.signedMeasure
          (L.finiteVariationPart_isBoundedVariation omega)).totalVariation
            Set.univ = a * b := by
      simp only [commonRefinementReferenceDensity, ENNReal.coe_mul]
      ring
    _ <= a * 1 := mul_le_mul le_rfl
      (normalizedVariationReferenceDensity_mul_variation_le_one L omega)
      (by positivity) (by positivity)
    _ <= 1 * 1 := mul_le_mul
      (ENNReal.coe_le_coe.2 ((mul_le_of_le_one_left (by positivity)
        (E.referenceDensity_le_one omega)).trans
          (E'.referenceDensity_le_one omega))) le_rfl (by positivity) (by positivity)
    _ = 1 := by simp

/-- The refined prefix's total variation remains square integrable under the
smaller common-refinement reference measure. -/
theorem totalVariation_memLp_two_commonRefinementReferenceMeasure
    (E : SIntegrableFiniteVariationBridge H)
    (E' : SIntegrableFiniteVariationBridge K) :
    MemLp (fun omega =>
      (FiniteVariationPath.signedMeasure
        (L.finiteVariationPart_isBoundedVariation omega)).totalVariation.real
          Set.univ) (2 : ENNReal)
      (mu.withDensity fun omega =>
        (commonRefinementReferenceDensity E E' L omega : ENNReal)) := by
  apply (totalVariation_memLp_two_normalizedReferenceMeasure
    L.finiteVariationPart_isRightContinuous).mono_measure
  apply withDensity_mono
  exact Filter.Eventually.of_forall fun omega => ENNReal.coe_le_coe.2 <| by
    unfold commonRefinementReferenceDensity
    simpa only [one_mul] using mul_le_mul
      ((mul_le_of_le_one_left (by positivity) (E.referenceDensity_le_one omega)).trans
        (E'.referenceDensity_le_one omega)) le_rfl (by positivity) (by positivity)

/-- A bridge on the refined source prefix whose reference density is smaller
than the reference density of either input schedule. -/
noncomputable def commonRefinementFiniteVariationBridge
    (E : SIntegrableFiniteVariationBridge H)
    (E' : SIntegrableFiniteVariationBridge K)
    (L : SIntegrableStrategy D) : SIntegrableFiniteVariationBridge L :=
  ofCumulativeVariationWithDensity
    (commonRefinementReferenceDensity E E' L)
    (commonRefinementReferenceDensity_measurable E E')
    (commonRefinementReferenceDensity_pos E E')
    (commonRefinementReferenceDensity_le_one E E')
    ENNReal.one_lt_top
    (commonRefinementReferenceDensity_mul_variation_le_one E E')
    (totalVariation_memLp_two_commonRefinementReferenceMeasure E E')

/-- Variation-`L¹` membership descends when both the sample density and the
path variation decrease.  Unlike the older equal-reference-measure lemma,
this is the comparison needed by genuine common refinements. -/
theorem memLp_one_of_referenceDensity_le_of_pathVariation_le
    (E : SIntegrableFiniteVariationBridge H)
    (E' : SIntegrableFiniteVariationBridge K)
    (hReferenceDensity : forall omega,
      E.referenceDensity omega <= E'.referenceDensity omega)
    (hPathVariation : ∀ᵐ omega ∂mu,
      (FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation omega)).totalVariation <=
      (FiniteVariationPath.signedMeasure
        (K.finiteVariationPart_isBoundedVariation omega)).totalVariation)
    (f : Process Omega) (hf : IsStronglyPredictable F f)
    (hMemLp : MemLp (Function.uncurry f) 1
      (canonicalVariationMeasure E')) :
    MemLp (Function.uncurry f) 1 (canonicalVariationMeasure E) := by
  apply memLp_one_iff_integrable.mpr
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hGlobal :
      (∫⁻ p, ‖Function.uncurry f p‖ₑ
        ∂canonicalVariationMeasure E') < ∞ := by
    rw [← hasFiniteIntegral_iff_enorm]
    exact (memLp_one_iff_integrable.mp hMemLp).2
  apply lt_of_le_of_lt _ hGlobal
  rw [lintegral_canonicalVariationMeasure_eq_lintegral_pathVariation
      E hf.enorm,
    lintegral_canonicalVariationMeasure_eq_lintegral_pathVariation
      E' hf.enorm]
  apply lintegral_mono_ae
  filter_upwards [hPathVariation] with omega hPathOmega
  exact mul_le_mul
    (ENNReal.coe_le_coe.2 (hReferenceDensity omega))
    (lintegral_mono' hPathOmega le_rfl) (by positivity) (by positivity)

/-- An old coefficient remains variation-`L¹` on the common refinement when
the refined prefix is a path-variation restriction of the old prefix. -/
theorem memLp_one_commonRefinement_of_left
    (E : SIntegrableFiniteVariationBridge H)
    (E' : SIntegrableFiniteVariationBridge K)
    (hPathVariation : ∀ᵐ omega ∂mu,
      (FiniteVariationPath.signedMeasure
        (L.finiteVariationPart_isBoundedVariation omega)).totalVariation <=
      (FiniteVariationPath.signedMeasure
        (H.finiteVariationPart_isBoundedVariation omega)).totalVariation)
    (f : Process Omega) (hf : IsStronglyPredictable F f)
    (hMemLp : MemLp (Function.uncurry f) 1
      (canonicalVariationMeasure E)) :
    MemLp (Function.uncurry f) 1
      (canonicalVariationMeasure
        (commonRefinementFiniteVariationBridge E E' L)) := by
  exact memLp_one_of_referenceDensity_le_of_pathVariation_le
    (commonRefinementFiniteVariationBridge E E' L) E
    (commonRefinementReferenceDensity_le_left E E') hPathVariation f hf hMemLp

/-- Symmetric transport of a coefficient from the second input schedule. -/
theorem memLp_one_commonRefinement_of_right
    (E : SIntegrableFiniteVariationBridge H)
    (E' : SIntegrableFiniteVariationBridge K)
    (hPathVariation : ∀ᵐ omega ∂mu,
      (FiniteVariationPath.signedMeasure
        (L.finiteVariationPart_isBoundedVariation omega)).totalVariation <=
      (FiniteVariationPath.signedMeasure
        (K.finiteVariationPart_isBoundedVariation omega)).totalVariation)
    (f : Process Omega) (hf : IsStronglyPredictable F f)
    (hMemLp : MemLp (Function.uncurry f) 1
      (canonicalVariationMeasure E')) :
    MemLp (Function.uncurry f) 1
      (canonicalVariationMeasure
        (commonRefinementFiniteVariationBridge E E' L)) := by
  exact memLp_one_of_referenceDensity_le_of_pathVariation_le
    (commonRefinementFiniteVariationBridge E E' L) E'
    (commonRefinementReferenceDensity_le_right E E') hPathVariation f hf hMemLp

/-- The path variation of a further pointwise stop is dominated by the path
variation before that stop.  This is the concrete finite-variation fact used
when a pair schedule replaces an old localizer by a smaller one. -/
theorem stoppedPath_totalVariation_le
    (A : NNReal -> Real) (hA : BoundedVariationOn A Set.univ)
    (hRight : forall t, ContinuousWithinAt A (Set.Ici t) t)
    (tau : NNReal) :
    (FiniteVariationPath.signedMeasure
      (FiniteVariationStoppedPath.boundedVariationOn_stopAt hA tau)
      ).totalVariation <=
      (FiniteVariationPath.signedMeasure hA).totalVariation := by
  rw [FiniteVariationStoppedPath.totalVariation_stopAt_eq_restrict_Ioc
    A hA hRight tau]
  exact Measure.restrict_le_self

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
