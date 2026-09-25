/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationStoppedStieltjes
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym

/-! # Intrinsic direction of a Stieltjes measure

The Radon–Nikodym derivative against Jordan variation has unit absolute value.
It preserves integrability and agrees with the original direction after stopping.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace FTAPTheorem42

namespace FiniteVariationPath

variable {Time : Type*} [LinearOrder Time] [DenselyOrdered Time]
  [TopologicalSpace Time] [OrderTopology Time]
  [SecondCountableTopology Time] [CompactIccSpace Time]
  [MeasurableSpace Time] [BorelSpace Time]

/-- The intrinsic signed direction of a bounded-variation path measure. -/
noncomputable def variationDirection
    {A : Time → ℝ} (hA : BoundedVariationOn A Set.univ) : Time → ℝ :=
  let ν := signedMeasure hA
  ν.rnDeriv ν.totalVariation

/-- The intrinsic path direction is integrable for Jordan total variation. -/
theorem integrable_variationDirection
    {A : Time → ℝ} (hA : BoundedVariationOn A Set.univ) :
    Integrable (variationDirection hA) (signedMeasure hA).totalVariation :=
  SignedMeasure.integrable_rnDeriv _ _

/-- Weighting Jordan total variation by the intrinsic direction recovers the
signed Stieltjes measure. -/
theorem withDensity_variationDirection_eq_signedMeasure
    {A : Time → ℝ} (hA : BoundedVariationOn A Set.univ) :
    (signedMeasure hA).totalVariation.withDensityᵥ
        (variationDirection hA) = signedMeasure hA := by
  let ν := signedMeasure hA
  let : IsFiniteMeasure ν.totalVariation := by
    dsimp only [ν]
    unfold SignedMeasure.totalVariation
    infer_instance
  have hac : ν ≪ᵥ ν.totalVariation.toENNRealVectorMeasure := by
    rw [SignedMeasure.absolutelyContinuous_ennreal_iff,
      VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure]
  exact SignedMeasure.withDensityᵥ_rnDeriv_eq
    ν ν.totalVariation hac

/-- The intrinsic Radon--Nikodym direction has unit absolute value for
Jordan total variation. -/
theorem abs_variationDirection_ae_eq_one
    {A : Time → ℝ} (hA : BoundedVariationOn A Set.univ) :
    (fun t => |variationDirection hA t|) =ᵐ[
      (signedMeasure hA).totalVariation] (fun _ => (1 : ℝ)) := by
  let ν := (signedMeasure hA).totalVariation
  let h : Time → ℝ := variationDirection hA
  let : IsFiniteMeasure ν := by
    dsimp only [ν]
    unfold SignedMeasure.totalVariation
    infer_instance
  have hInt : Integrable h ν := integrable_variationDirection hA
  have hVariation := congrArg VectorMeasure.variation
    (withDensity_variationDirection_eq_signedMeasure hA).symm
  rw [← signedMeasure_totalVariation_eq_variation,
    Measure.variation_withDensityᵥ hInt] at hVariation
  have hDensityMeasure :
      ν.withDensity (fun t => ‖h t‖ₑ) =
        ν.withDensity (fun _ => (1 : ℝ≥0∞)) := by
    simpa only [withDensity_const, one_smul] using hVariation.symm
  have hEnormEq :
      (fun t => ‖h t‖ₑ) =ᵐ[ν] (fun _ => (1 : ℝ≥0∞)) :=
    (withDensity_eq_iff_of_sigmaFinite
      hInt.aestronglyMeasurable.enorm aemeasurable_const).mp hDensityMeasure
  filter_upwards [hEnormEq] with t ht
  simpa only [h, Real.enorm_eq_ofReal_abs, ENNReal.ofReal_eq_one] using ht

/-- Multiplication by the intrinsic Stieltjes direction preserves
integrability with respect to Jordan total variation. -/
theorem integrable_variationDirection_mul
    {A : Time → ℝ} (hA : BoundedVariationOn A Set.univ)
    {f : Time → ℝ}
    (hf : Integrable f (signedMeasure hA).totalVariation) :
    Integrable (fun t => variationDirection hA t * f t)
      (signedMeasure hA).totalVariation := by
  apply hf.mono
  · exact (integrable_variationDirection hA).aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  · filter_upwards [abs_variationDirection_ae_eq_one hA] with t ht
    rw [Real.norm_eq_abs, abs_mul, ht, one_mul, Real.norm_eq_abs]

end FiniteVariationPath

namespace FiniteVariationStoppedPath

/-- The intrinsic Jordan direction of a stopped path is the restriction of
the original direction.  Both functions are identified as densities of the
same stopped signed Stieltjes measure. -/
theorem variationDirection_stopAt_ae_eq
    (A : NNReal -> Real) (hA : BoundedVariationOn A Set.univ)
    (hRight : forall t, ContinuousWithinAt A (Set.Ici t) t)
    (tau : NNReal) :
    FiniteVariationPath.variationDirection
        (boundedVariationOn_stopAt hA tau) =ᵐ[
      (FiniteVariationPath.signedMeasure
        (boundedVariationOn_stopAt hA tau)).totalVariation]
      FiniteVariationPath.variationDirection hA := by
  let hStopped := boundedVariationOn_stopAt hA tau
  let nu := (FiniteVariationPath.signedMeasure hStopped).totalVariation
  have hOriginalIntegrable : Integrable
      (FiniteVariationPath.variationDirection hA) nu := by
    exact integrable_totalVariation_stopAt A hA hRight tau
      (FiniteVariationPath.integrable_variationDirection hA)
  have hStoppedIntegrable : Integrable
      (FiniteVariationPath.variationDirection hStopped) nu :=
    FiniteVariationPath.integrable_variationDirection hStopped
  apply hStoppedIntegrable.ae_eq_of_withDensityᵥ_eq hOriginalIntegrable
  exact
    (FiniteVariationPath.withDensity_variationDirection_eq_signedMeasure
      hStopped).trans
        (withDensityᵥ_stopAt_eq A A hA hA hRight hRight tau
          (FiniteVariationPath.integrable_variationDirection hA)
          (FiniteVariationPath.withDensity_variationDirection_eq_signedMeasure
            hA)).symm

end FiniteVariationStoppedPath

end FTAPTheorem42
