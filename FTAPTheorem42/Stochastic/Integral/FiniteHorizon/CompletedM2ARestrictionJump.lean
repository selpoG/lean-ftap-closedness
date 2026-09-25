/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedM2ACadlag
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.M2ACoefficientRestriction
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.MartingaleIntegralJump
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationProcessCompletionGeneralAgreement
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrablePathwiseRestrictionCalculus

/-!
# Jumps of predictably restricted completed M2A graphs

The càdlàg completed martingale integral has jump `H Delta M`, while the
completed finite-variation process has jump `H Delta A`.  Applying these
two identities to an indicator-restricted coefficient proves the whole-gain
jump semantics of predictable restriction inside the concrete completed
finite-horizon calculus.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace FTAPTheorem42

variable {Omega : Type*} [MeasurableSpace Omega]

namespace SIntegrableFiniteVariationBridge

open BoundedMartingaleQuadraticEnergy.Data

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  [SigmaFiniteFiltration mu F]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : SIntegrableStrategy D}
  {T : NNReal}

/-- Indicator restriction has the expected jump on the càdlàg completed
martingale component. -/
theorem finiteHorizonCompletedMartingaleCadlagPart_restrictPredictable_jump
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (hGMartingale : Martingale G.martingalePart F mu)
    (hGMLeft : ProcessHasLeftLimits G.martingalePart)
    (hGMTerminal : MemLp (G.martingalePart T) (2 : ENNReal) mu)
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B)
    (c : FiniteHorizonM2ACoefficient E Q) :
    ∀ᵐ omega ∂mu, ∀ t,
      processLeftJump
          (finiteHorizonCompletedMartingaleCadlagPart hUsual Q hGMartingale
            hGMLeft hGMTerminal (c.restrictPredictable B hB)) t omega =
        predictableRestrictedLeftJump B
          (finiteHorizonCompletedMartingaleCadlagPart hUsual Q hGMartingale
            hGMLeft hGMTerminal c) t omega := by
  have hRestricted := finiteHorizonMartingaleIntegralCadlagProcess_processLeftJump
    hUsual Q hGMartingale G.martingalePart_isRightContinuous hGMLeft
      hGMTerminal
      (Function.uncurry (c.restrictPredictable B hB).integrand)
      (c.restrictPredictable B hB).integrand_isStronglyPredictable
      (c.restrictPredictable B hB).integrand_memLp_energy
  have hOriginal := finiteHorizonMartingaleIntegralCadlagProcess_processLeftJump
    hUsual Q hGMartingale G.martingalePart_isRightContinuous hGMLeft
      hGMTerminal (Function.uncurry c.integrand)
      c.integrand_isStronglyPredictable c.integrand_memLp_energy
  filter_upwards [hRestricted, hOriginal] with omega hRestrictedOmega
      hOriginalOmega
  intro t
  unfold finiteHorizonCompletedMartingaleCadlagPart
  rw [hRestrictedOmega t]
  rw [FiniteHorizonM2ACoefficient.restrictPredictable_integrand]
  unfold predictableRestrictedLeftJump PredictableProcess.restrict
  by_cases ht : (t, omega) ∈ B
  · rw [hOriginalOmega t]
    simp [Function.uncurry, ht]
  · simp [Function.uncurry, ht]

omit [SigmaFiniteFiltration mu F] in
/-- Indicator restriction has the expected jump on the completed
finite-variation component. -/
theorem finiteHorizonCompletedFiniteVariationPart_restrictPredictable_jump
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (E : SIntegrableFiniteVariationBridge G)
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B)
    (c : FiniteHorizonM2ACoefficient E Q) :
    ∀ᵐ omega ∂mu, ∀ t,
      processLeftJump
          (finiteHorizonCompletedFiniteVariationPart hUsual T Q E
            (c.restrictPredictable B hB)) t omega =
        predictableRestrictedLeftJump B
          (finiteHorizonCompletedFiniteVariationPart hUsual T Q E c)
            t omega := by
  have hRestrictedVersion :=
    (finiteHorizonCompletedFiniteVariationPart_indistinguishable
      hUsual E Q (c.restrictPredictable B hB)).processLeftJump_eq
  have hOriginalVersion :=
    (finiteHorizonCompletedFiniteVariationPart_indistinguishable
      hUsual E Q c).processLeftJump_eq
  have hRestrictedRaw :=
    processLeftJump_finiteVariationIntegralProcess_eq_of_memLp_one
      E (c.restrictPredictable B hB).integrand
      (c.restrictPredictable B hB).integrand_isStronglyPredictable
      (c.restrictPredictable B hB).integrand_memLp_variation
  have hOriginalRaw :=
    processLeftJump_finiteVariationIntegralProcess_eq_of_memLp_one
      E c.integrand c.integrand_isStronglyPredictable
      c.integrand_memLp_variation
  filter_upwards [hRestrictedVersion, hOriginalVersion, hRestrictedRaw,
      hOriginalRaw] with omega hRestrictedVersionOmega
        hOriginalVersionOmega hRestrictedRawOmega hOriginalRawOmega
  intro t
  rw [hRestrictedVersionOmega t, hRestrictedRawOmega t,
    FiniteHorizonM2ACoefficient.restrictPredictable_integrand]
  unfold predictableRestrictedLeftJump PredictableProcess.restrict
  by_cases ht : (t, omega) ∈ B
  · rw [hOriginalVersionOmega t, hOriginalRawOmega t]
    simp [Function.uncurry, ht]
  · simp [ht]

/-- Indicator restriction has the expected whole-gain jump on the càdlàg
completed `M2 + A1` representative. -/
theorem finiteHorizonCompletedM2ACadlagGain_restrictPredictable_jump
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (E : SIntegrableFiniteVariationBridge G)
    (hGMartingale : Martingale G.martingalePart F mu)
    (hGMLeft : ProcessHasLeftLimits G.martingalePart)
    (hGMTerminal : MemLp (G.martingalePart T) (2 : ENNReal) mu)
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B)
    (c : FiniteHorizonM2ACoefficient E Q) :
    ∀ᵐ omega ∂mu, ∀ t,
      processLeftJump
          (finiteHorizonCompletedM2ACadlagGain hUsual Q E hGMartingale
            hGMLeft hGMTerminal (c.restrictPredictable B hB)) t omega =
        predictableRestrictedLeftJump B
          (finiteHorizonCompletedM2ACadlagGain hUsual Q E hGMartingale
            hGMLeft hGMTerminal c) t omega := by
  have hMartingale :=
    finiteHorizonCompletedMartingaleCadlagPart_restrictPredictable_jump
      hUsual Q hGMartingale hGMLeft hGMTerminal B hB c
  have hFiniteVariation :=
    finiteHorizonCompletedFiniteVariationPart_restrictPredictable_jump
      hUsual Q E B hB c
  let V := finiteHorizonCompletedM2ACadlagStrategy hUsual Q E hGMartingale
    hGMLeft hGMTerminal c
  let VB := finiteHorizonCompletedM2ACadlagStrategy hUsual Q E hGMartingale
    hGMLeft hGMTerminal (c.restrictPredictable B hB)
  have hVM := finiteHorizonCompletedM2ACadlagStrategy_martingalePart_hasLeftLimits
    hUsual Q E hGMartingale hGMLeft hGMTerminal c
  have hVBM := finiteHorizonCompletedM2ACadlagStrategy_martingalePart_hasLeftLimits
    hUsual Q E hGMartingale hGMLeft hGMTerminal
      (c.restrictPredictable B hB)
  have hVMDef : V.martingalePart =
      finiteHorizonCompletedMartingaleCadlagPart hUsual Q hGMartingale
        hGMLeft hGMTerminal c := rfl
  have hVADef : V.finiteVariationPart =
      finiteHorizonCompletedFiniteVariationPart hUsual T Q E c := rfl
  have hVBMDef : VB.martingalePart =
      finiteHorizonCompletedMartingaleCadlagPart hUsual Q hGMartingale
        hGMLeft hGMTerminal (c.restrictPredictable B hB) := rfl
  have hVBADef : VB.finiteVariationPart =
      finiteHorizonCompletedFiniteVariationPart hUsual T Q E
        (c.restrictPredictable B hB) := rfl
  have hVDecomposition := V.processLeftJump_eq_components hVM
  have hVBDecomposition := VB.processLeftJump_eq_components hVBM
  filter_upwards [hMartingale, hFiniteVariation, hVDecomposition,
      hVBDecomposition] with omega hMartingaleOmega hFiniteVariationOmega
        hVDecompositionOmega hVBDecompositionOmega
  intro t
  change processLeftJump VB.stochasticIntegral t omega =
    predictableRestrictedLeftJump B V.stochasticIntegral t omega
  unfold predictableRestrictedLeftJump
  by_cases ht : (t, omega) ∈ B
  · simp only [ht, ite_true]
    rw [hVBDecompositionOmega t, hVDecompositionOmega t,
      hVBMDef, hVBADef, hVMDef, hVADef,
      hMartingaleOmega t, hFiniteVariationOmega t]
    unfold predictableRestrictedLeftJump
    simp [ht]
  · rw [hVBDecompositionOmega t, hVBMDef, hVBADef,
      hMartingaleOmega t, hFiniteVariationOmega t]
    unfold predictableRestrictedLeftJump
    simp [ht]

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
