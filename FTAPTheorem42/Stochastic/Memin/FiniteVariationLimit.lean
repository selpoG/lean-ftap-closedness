/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableFiniteVariationStieltjesCalculus

/-!
# Identification of the Mémin finite-variation limit

An actual Mémin subsequence has a canonical predictable integrand limit and a
separately constructed finite-variation component limit.  On each finite
horizon, pathwise `L¹` convergence lets the signed Stieltjes integral pass to
the limit.  Uniqueness of real limits then identifies the resulting signed
measure with the Stieltjes measure of the component limit.  Actuality is
tracked by an `SIntegrableRealizationModel`; the theorem does not quantify over
arbitrary raw strategy records.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

namespace FiniteVariationPath

variable {Time : Type*} [LinearOrder Time] [DenselyOrdered Time]
  [TopologicalSpace Time] [OrderTopology Time]
  [SecondCountableTopology Time] [CompactIccSpace Time]
  [MeasurableSpace Time] [BorelSpace Time]

/-- Multiplication by the intrinsic unit direction preserves `L¹`
distance. -/
theorem lintegral_enorm_variationDirection_mul_sub
    {A : Time → ℝ} (hA : BoundedVariationOn A Set.univ)
    (f g : Time → ℝ) :
    (∫⁻ t, ‖variationDirection hA t * f t -
      variationDirection hA t * g t‖ₑ
        ∂(signedMeasure hA).totalVariation) =
      ∫⁻ t, edist (f t) (g t) ∂(signedMeasure hA).totalVariation := by
  apply lintegral_congr_ae
  filter_upwards [abs_variationDirection_ae_eq_one hA] with t ht
  rw [← mul_sub, enorm_mul, Real.enorm_eq_ofReal_abs, ht,
    ENNReal.ofReal_one, one_mul]
  simp only [edist_dist, Real.dist_eq, Real.enorm_eq_ofReal_abs]

end FiniteVariationPath

namespace SIntegrableFiniteVariationStieltjesCalculus

open SIntegrablePredictableMultiplierLinearL2Calculus

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}
  {R : SIntegrableRealizationModel D}
  {G : ActualLocallySIntegrableStrategy R}

/-- On every positive integer horizon, the signed Stieltjes measure obtained
from the canonical Mémin integrand limit is the signed Stieltjes measure of
the already constructed finite-variation component limit. -/
theorem meminLimitIntegrand_stopped_signedMeasure_eq_limit
    (C : SIntegrableFiniteVariationStieltjesCalculus D R G)
    (L : ℕ → ActualSIntegrableStrategy R)
    (finiteVariationLimit : Process Ω)
    (hVariationSummable : ∀ᵐ ω ∂μ, Summable (fun k =>
      lemma411DifferenceTotalVariation (L (k + 1)).val (L k).val ω))
    (hMartingaleSummable : ∀ T, ∀ᵐ ω ∂μ, Summable (fun k =>
      meminMartingaleDifferenceEnvelope
        (ActualSIntegrableStrategy.rawSequence L) T k ω))
    (hFiniteVariationTendsto : ∀ᵐ ω ∂μ, ∀ t,
      Tendsto (fun n => (L n).val.finiteVariationPart t ω) atTop
        (𝓝 (finiteVariationLimit t ω)))
    (hFiniteVariationBounded : ∀ ω, BoundedVariationOn
      (finiteVariationLimit · ω) Set.univ)
    (hFiniteVariationRight : ∀ ω t, ContinuousWithinAt
      (finiteVariationLimit · ω) (Set.Ici t) t) :
    ∀ r, ∀ᵐ ω ∂μ,
      (FiniteVariationPath.signedMeasure
        ((G.val.deterministicallyStopped ((r + 1 : ℕ) : ℝ≥0) (by positivity)
          ).finiteVariationPart_isBoundedVariation ω)).totalVariation.withDensityᵥ
            (fun t =>
              FiniteVariationPath.variationDirection
                  ((G.val.deterministicallyStopped ((r + 1 : ℕ) : ℝ≥0) (by positivity)
                    ).finiteVariationPart_isBoundedVariation ω) t *
                meminLimitIntegrand
                  (ActualSIntegrableStrategy.rawSequence L) t ω) =
        FiniteVariationPath.signedMeasure
          (FiniteVariationStoppedPath.boundedVariationOn_stopAt
            (hFiniteVariationBounded ω) ((r + 1 : ℕ) : ℝ≥0)) := by
  intro r
  let T : ℝ≥0 := ((r + 1 : ℕ) : ℝ≥0)
  have hT : 0 < T := by
    dsimp only [T]
    positivity
  have hAllStieltjes : ∀ᵐ ω ∂μ, ∀ n,
      (FiniteVariationPath.signedMeasure
        ((G.val.deterministicallyStopped T hT
          ).finiteVariationPart_isBoundedVariation ω)).totalVariation.withDensityᵥ
            (fun t =>
              FiniteVariationPath.variationDirection
                  ((G.val.deterministicallyStopped T hT
                    ).finiteVariationPart_isBoundedVariation ω) t *
                (L n).val.integrand t ω) =
        FiniteVariationPath.signedMeasure
          (((L n).val.toLocally.deterministicallyStopped T hT
            ).finiteVariationPart_isBoundedVariation ω) :=
    eventually_countable_forall.2 fun n =>
      C.finiteVariationPart_stopped_signedMeasure (L n) T hT
  have hAllIntegrable : ∀ᵐ ω ∂μ, ∀ n,
      Integrable (fun t => (L n).val.integrand t ω)
        (FiniteVariationPath.signedMeasure
          ((G.val.deterministicallyStopped T hT
            ).finiteVariationPart_isBoundedVariation ω)).totalVariation :=
    eventually_countable_forall.2 fun n =>
      C.finiteVariationPart_stopped_integrable (L n) T hT
  filter_upwards [C.meminLimitIntegrand_stopped_path_l1 L
      hVariationSummable hMartingaleSummable r,
    hFiniteVariationTendsto, hAllStieltjes, hAllIntegrable]
      with ω hLimit hTendsto hStieltjes hIntegrable
  let hSource := (G.val.deterministicallyStopped T hT
    ).finiteVariationPart_isBoundedVariation ω
  let ν := (FiniteVariationPath.signedMeasure hSource).totalVariation
  let direction := FiniteVariationPath.variationDirection hSource
  let limitIntegrand : ℝ≥0 → ℝ := fun t =>
    meminLimitIntegrand (ActualSIntegrableStrategy.rawSequence L) t ω
  have hLimitIntegrable : Integrable limitIntegrand ν := by
    simpa only [limitIntegrand, ν, hSource, T] using hLimit.1
  have hDirectedLimitIntegrable : Integrable
      (fun t => direction t * limitIntegrand t) ν := by
    exact FiniteVariationPath.integrable_variationDirection_mul
      hSource hLimitIntegrable
  have hDirectedIntegrable : ∀ n, Integrable
      (fun t => direction t * (L n).val.integrand t ω) ν := by
    intro n
    apply FiniteVariationPath.integrable_variationDirection_mul hSource
    simpa only [ν, hSource, T] using hIntegrable n
  have hDirectedL1 : Tendsto (fun n => ∫⁻ t,
      ‖direction t * (L n).val.integrand t ω -
        direction t * limitIntegrand t‖ₑ ∂ν) atTop (𝓝 0) := by
    have hRaw : Tendsto (fun n => ∫⁻ t,
        edist ((L n).val.integrand t ω) (limitIntegrand t) ∂ν)
        atTop (𝓝 0) := by
      simpa only [ν, hSource, T, limitIntegrand] using hLimit.2.2
    exact hRaw.congr' (Eventually.of_forall fun n =>
      (FiniteVariationPath.lintegral_enorm_variationDirection_mul_sub
        hSource (fun t => (L n).val.integrand t ω) limitIntegrand).symm)
  apply FiniteVariationPath.signedMeasure_ext_of_Ioc_univ
  · intro a b hab
    rw [withDensityᵥ_apply hDirectedLimitIntegrable measurableSet_Ioc]
    have hIntegral := tendsto_setIntegral_of_L1
      (fun t => direction t * limitIntegrand t)
      hDirectedLimitIntegrable.aestronglyMeasurable
      (Eventually.of_forall hDirectedIntegrable) hDirectedL1 (Ioc a b)
    have hApproxEq : ∀ n,
        (∫ t in Ioc a b, direction t * (L n).val.integrand t ω ∂ν) =
          FiniteVariationPath.signedMeasure
            (((L n).val.toLocally.deterministicallyStopped T hT
              ).finiteVariationPart_isBoundedVariation ω) (Ioc a b) := by
      intro n
      rw [← withDensityᵥ_apply (hDirectedIntegrable n) measurableSet_Ioc]
      exact congrArg (fun η : SignedMeasure ℝ≥0 => η (Ioc a b))
        (hStieltjes n)
    have hIntegralOutput : Tendsto (fun n =>
        FiniteVariationPath.signedMeasure
          (((L n).val.toLocally.deterministicallyStopped T hT
            ).finiteVariationPart_isBoundedVariation ω) (Ioc a b))
        atTop (𝓝 (∫ t in Ioc a b,
          direction t * limitIntegrand t ∂ν)) :=
      hIntegral.congr' (Eventually.of_forall hApproxEq)
    have hOutput : Tendsto (fun n =>
        FiniteVariationPath.signedMeasure
          (((L n).val.toLocally.deterministicallyStopped T hT
            ).finiteVariationPart_isBoundedVariation ω) (Ioc a b))
        atTop (𝓝 (FiniteVariationPath.signedMeasure
          (FiniteVariationStoppedPath.boundedVariationOn_stopAt
            (hFiniteVariationBounded ω) T) (Ioc a b))) := by
      rw [FiniteVariationPath.signedMeasure_Ioc
        (FiniteVariationStoppedPath.boundedVariationOn_stopAt
          (hFiniteVariationBounded ω) T)
        (FiniteVariationStoppedPath.rightContinuous_stopAt
          (finiteVariationLimit · ω) (hFiniteVariationRight ω) T) hab]
      have hSub := (hTendsto (min b T)).sub (hTendsto (min a T))
      apply hSub.congr'
      exact Eventually.of_forall fun n => by
        change (L n).val.finiteVariationPart (min b T) ω -
            (L n).val.finiteVariationPart (min a T) ω =
          FiniteVariationPath.signedMeasure
            (((L n).val.toLocally.deterministicallyStopped T hT
              ).finiteVariationPart_isBoundedVariation ω) (Ioc a b)
        rw [FiniteVariationPath.signedMeasure_Ioc
          (((L n).val.toLocally.deterministicallyStopped T hT
            ).finiteVariationPart_isBoundedVariation ω)
          (((L n).val.toLocally.deterministicallyStopped T hT
            ).finiteVariationPart_isRightContinuous ω) hab]
        rfl
    exact tendsto_nhds_unique hIntegralOutput hOutput
  · rw [withDensityᵥ_apply hDirectedLimitIntegrable MeasurableSet.univ]
    have hIntegral := tendsto_setIntegral_of_L1
      (fun t => direction t * limitIntegrand t)
      hDirectedLimitIntegrable.aestronglyMeasurable
      (Eventually.of_forall hDirectedIntegrable) hDirectedL1 Set.univ
    have hApproxEq : ∀ n,
        (∫ t in Set.univ, direction t * (L n).val.integrand t ω ∂ν) =
          FiniteVariationPath.signedMeasure
            (((L n).val.toLocally.deterministicallyStopped T hT
              ).finiteVariationPart_isBoundedVariation ω) Set.univ := by
      intro n
      rw [← withDensityᵥ_apply (hDirectedIntegrable n) MeasurableSet.univ]
      exact congrArg (fun η : SignedMeasure ℝ≥0 => η Set.univ)
        (hStieltjes n)
    have hIntegralOutput : Tendsto (fun n =>
        FiniteVariationPath.signedMeasure
          (((L n).val.toLocally.deterministicallyStopped T hT
            ).finiteVariationPart_isBoundedVariation ω) Set.univ)
        atTop (𝓝 (∫ t in Set.univ,
          direction t * limitIntegrand t ∂ν)) :=
      hIntegral.congr' (Eventually.of_forall hApproxEq)
    have hOutput : Tendsto (fun n =>
        FiniteVariationPath.signedMeasure
          (((L n).val.toLocally.deterministicallyStopped T hT
            ).finiteVariationPart_isBoundedVariation ω) Set.univ)
        atTop (𝓝 (FiniteVariationPath.signedMeasure
          (FiniteVariationStoppedPath.boundedVariationOn_stopAt
            (hFiniteVariationBounded ω) T) Set.univ)) := by
      rw [FiniteVariationStoppedPath.signedMeasure_univ_stopAt
        (finiteVariationLimit · ω) T
        (FiniteVariationStoppedPath.boundedVariationOn_stopAt
          (hFiniteVariationBounded ω) T)]
      have hSub := (hTendsto T).sub (hTendsto 0)
      apply hSub.congr'
      exact Eventually.of_forall fun n => by
        change (L n).val.finiteVariationPart T ω -
            (L n).val.finiteVariationPart 0 ω =
          FiniteVariationPath.signedMeasure
            (((L n).val.toLocally.deterministicallyStopped T hT
              ).finiteVariationPart_isBoundedVariation ω) Set.univ
        have hUniv : FiniteVariationPath.signedMeasure
            (((L n).val.toLocally.deterministicallyStopped T hT
              ).finiteVariationPart_isBoundedVariation ω) Set.univ =
            (L n).val.finiteVariationPart T ω -
              (L n).val.finiteVariationPart 0 ω := by
          exact FiniteVariationStoppedPath.signedMeasure_univ_stopAt
            ((L n).val.finiteVariationPart · ω) T
            (((L n).val.toLocally.deterministicallyStopped T hT
              ).finiteVariationPart_isBoundedVariation ω)
        exact hUniv.symm
    exact tendsto_nhds_unique hIntegralOutput hOutput

end SIntegrableFiniteVariationStieltjesCalculus

end FTAPTheorem42
