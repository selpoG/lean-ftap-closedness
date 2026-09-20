/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationProcessCompletionGeneralAgreement

/-!
# Algebra of the completed finite-variation process

The completed finite-variation operator is selected nonconstructively, so
its algebraic laws are not definitional.  Its agreement with the raw
cumulative Stieltjes integral transfers the pathwise linearity of that
integral to the selected completed process.  This file establishes scalar
homogeneity without adding an algebraic law as a completion capability.
-/

namespace FTAPTheorem42

open Filter Function MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega]

namespace SIntegrableFiniteVariationBridge

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : SIntegrableStrategy D}

omit [SigmaFiniteFiltration mu F] in
/-- The raw cumulative Stieltjes integral commutes pointwise with real
scalar multiplication of its coefficient. -/
theorem finiteVariationIntegralProcess_smul
    (E : SIntegrableFiniteVariationBridge G)
    (c : Real) (f : Process Omega) :
    finiteVariationIntegralProcess E (c • f) =
      c • finiteVariationIntegralProcess E f := by
  funext t omega
  simp only [finiteVariationIntegralProcess, finiteVariationIntegralDensity,
    Pi.smul_apply, smul_eq_mul]
  calc
    (∫ u, E.jumpCorrectedCanonicalVariationDensity (u, omega) *
        (c * f u omega) ∂E.pathVariationMeasureUpTo t omega) =
        ∫ u, c * (E.jumpCorrectedCanonicalVariationDensity (u, omega) *
          f u omega) ∂E.pathVariationMeasureUpTo t omega := by
      apply integral_congr_ae
      filter_upwards with u
      ring
    _ = c * ∫ u, E.jumpCorrectedCanonicalVariationDensity (u, omega) *
        f u omega ∂E.pathVariationMeasureUpTo t omega := by
      exact integral_const_mul c (fun u =>
        E.jumpCorrectedCanonicalVariationDensity (u, omega) * f u omega)

omit [SigmaFiniteFiltration mu F] in
/-- Scalar homogeneity of the selected completed finite-variation process.

Both integrability witnesses are constructed from the original coefficient;
the conclusion is process-level indistinguishability, hence is independent
of the noncomputable representatives selected by the two completions. -/
theorem completedFiniteVariationProcess_smul
    (hUsual : Filtration.UsualConditions mu F)
    (E : SIntegrableFiniteVariationBridge G)
    (f : Process Omega) (hf : IsStronglyPredictable F f)
    (hVariation : MemLp (Function.uncurry f) 1
      (canonicalVariationMeasure E))
    (c : Real) :
    ProcessIndistinguishable mu
      (completedFiniteVariationProcess hUsual E (c • f)
        (hf.const_smul c) (hVariation.const_smul c))
      (c • completedFiniteVariationProcess hUsual E f hf hVariation) := by
  have hScaled := completedFiniteVariationProcess_indistinguishable
    hUsual E (c • f) (hf.const_smul c) (hVariation.const_smul c)
  have hBase := completedFiniteVariationProcess_indistinguishable
    hUsual E f hf hVariation
  filter_upwards [hScaled, hBase] with omega hScaledOmega hBaseOmega
  intro t
  calc
    completedFiniteVariationProcess hUsual E (c • f)
        (hf.const_smul c) (hVariation.const_smul c) t omega =
        finiteVariationIntegralProcess E (c • f) t omega :=
      hScaledOmega t
    _ = c * finiteVariationIntegralProcess E f t omega := by
      rw [finiteVariationIntegralProcess_smul]
      rfl
    _ = c * completedFiniteVariationProcess hUsual E f hf hVariation t omega :=
      congrArg (c * ·) (hBaseOmega t).symm
    _ = (c • completedFiniteVariationProcess hUsual E f hf hVariation)
        t omega := rfl

/-!
## Additivity of the completed finite-variation process

Canonical variation `L1` membership supplies pathwise integrability outside
one market-null set.  On those paths, ordinary integral additivity proves
additivity of the raw cumulative Stieltjes integral.  Agreement with that
raw process then transfers the law to the selected completion.
-/

omit [SigmaFiniteFiltration mu F] in
/-- The raw cumulative Stieltjes integral is additive on paths where both
coefficients are integrable against the Jordan variation. -/
theorem finiteVariationIntegralProcess_add_ae
    (E : SIntegrableFiniteVariationBridge G)
    (f g : Process Omega)
    (hf : IsStronglyPredictable F f)
    (hg : IsStronglyPredictable F g)
    (hVariationF : MemLp (Function.uncurry f) 1
      (canonicalVariationMeasure E))
    (hVariationG : MemLp (Function.uncurry g) 1
      (canonicalVariationMeasure E)) :
    ProcessIndistinguishable mu
      (finiteVariationIntegralProcess E (f + g))
      (finiteVariationIntegralProcess E f +
        finiteVariationIntegralProcess E g) := by
  have hF := integrable_section_ae_of_memLp_one_canonicalVariation
    E f hf hVariationF
  have hG := integrable_section_ae_of_memLp_one_canonicalVariation
    E g hg hVariationG
  filter_upwards [hF, hG] with omega hFomega hGomega
  intro t
  have hFDensity :=
    integrable_finiteVariationIntegralDensity_section_of_integrable
      E hf omega hFomega
  have hGDensity :=
    integrable_finiteVariationIntegralDensity_section_of_integrable
      E hg omega hGomega
  have hFDensityUpTo : Integrable
      (fun u => finiteVariationIntegralDensity E f (u, omega))
      (pathVariationMeasureUpTo E t omega) := by
    simpa only [pathVariationMeasureUpTo, IntegrableOn] using
      hFDensity.integrableOn
  have hGDensityUpTo : Integrable
      (fun u => finiteVariationIntegralDensity E g (u, omega))
      (pathVariationMeasureUpTo E t omega) := by
    simpa only [pathVariationMeasureUpTo, IntegrableOn] using
      hGDensity.integrableOn
  change
    (∫ u, finiteVariationIntegralDensity E (f + g) (u, omega)
        ∂E.pathVariationMeasureUpTo t omega) =
      (∫ u, finiteVariationIntegralDensity E f (u, omega)
        ∂E.pathVariationMeasureUpTo t omega) +
      ∫ u, finiteVariationIntegralDensity E g (u, omega)
        ∂E.pathVariationMeasureUpTo t omega
  rw [← integral_add hFDensityUpTo hGDensityUpTo]
  apply integral_congr_ae
  filter_upwards with u
  simp only [finiteVariationIntegralDensity, Pi.add_apply]
  ring

omit [SigmaFiniteFiltration mu F] in
/-- Additivity of the selected completed finite-variation process. -/
theorem completedFiniteVariationProcess_add
    (hUsual : Filtration.UsualConditions mu F)
    (E : SIntegrableFiniteVariationBridge G)
    (f g : Process Omega)
    (hf : IsStronglyPredictable F f)
    (hg : IsStronglyPredictable F g)
    (hVariationF : MemLp (Function.uncurry f) 1
      (canonicalVariationMeasure E))
    (hVariationG : MemLp (Function.uncurry g) 1
      (canonicalVariationMeasure E)) :
    ProcessIndistinguishable mu
      (completedFiniteVariationProcess hUsual E (f + g)
        (hf.add hg) (hVariationF.add hVariationG))
      (completedFiniteVariationProcess hUsual E f hf hVariationF +
        completedFiniteVariationProcess hUsual E g hg hVariationG) := by
  have hSum := completedFiniteVariationProcess_indistinguishable
    hUsual E (f + g) (hf.add hg) (hVariationF.add hVariationG)
  have hF := completedFiniteVariationProcess_indistinguishable
    hUsual E f hf hVariationF
  have hG := completedFiniteVariationProcess_indistinguishable
    hUsual E g hg hVariationG
  have hRaw := finiteVariationIntegralProcess_add_ae
    E f g hf hg hVariationF hVariationG
  filter_upwards [hSum, hF, hG, hRaw]
      with omega hSumOmega hFOmega hGOmega hRawOmega
  intro t
  calc
    completedFiniteVariationProcess hUsual E (f + g)
        (hf.add hg) (hVariationF.add hVariationG) t omega =
        finiteVariationIntegralProcess E (f + g) t omega := hSumOmega t
    _ = finiteVariationIntegralProcess E f t omega +
        finiteVariationIntegralProcess E g t omega := hRawOmega t
    _ = completedFiniteVariationProcess hUsual E f hf hVariationF t omega +
        completedFiniteVariationProcess hUsual E g hg hVariationG t omega := by
      rw [hFOmega t, hGOmega t]

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
