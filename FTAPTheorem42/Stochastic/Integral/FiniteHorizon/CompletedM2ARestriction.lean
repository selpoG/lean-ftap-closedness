/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.M2ACoefficientRestriction
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedM2AAgreement
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationProcessCompletionGeneralAgreement

/-!
# Predictable restriction in the completed finite-horizon M2A calculus

The completed martingale integral of an indicator-restricted coefficient has
no larger terminal `L²` norm.  On the finite-variation side the completed
operator agrees with the raw cumulative Stieltjes integral of the same
restricted predictable process.  These are the two concrete operator facts
needed before a carrier-level restriction can be connected to a raw market
restriction operation.
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

/-- Predictable indicator restriction contracts the terminal martingale
energy of the completed integral. -/
theorem finiteHorizonCompletedMartingalePart_restrictPredictable_eLpNorm_le
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (hGMartingale : Martingale G.martingalePart F mu)
    (hGMTerminal : MemLp (G.martingalePart T) (2 : ENNReal) mu)
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B)
    (K : FiniteHorizonM2ACoefficient E Q) :
    eLpNorm
        (finiteHorizonCompletedMartingalePart hUsual T Q hGMartingale
          hGMTerminal (K.restrictPredictable B hB) T)
        (2 : ENNReal) mu ≤
      eLpNorm
        (finiteHorizonCompletedMartingalePart hUsual T Q hGMartingale
          hGMTerminal K T)
        (2 : ENNReal) mu := by
  have hIntegrand :=
    FiniteHorizonM2ACoefficient.restrictPredictable_integrand B hB K
  have hUncurry : Function.uncurry (K.restrictPredictable B hB).integrand =
      B.indicator (Function.uncurry K.integrand) := by
    rw [hIntegrand]
    rfl
  have hRestrictedNorm :=
    finiteHorizonMartingaleIntegralProcess_terminal_eLpNorm_eq
      hUsual Q hGMartingale G.martingalePart_isRightContinuous
        hGMTerminal
        (Function.uncurry (K.restrictPredictable B hB).integrand)
        (K.restrictPredictable B hB).integrand_isStronglyPredictable
        (K.restrictPredictable B hB).integrand_memLp_energy
  have hOriginalNorm :=
    finiteHorizonMartingaleIntegralProcess_terminal_eLpNorm_eq
      hUsual Q hGMartingale G.martingalePart_isRightContinuous
        hGMTerminal (Function.uncurry K.integrand)
          K.integrand_isStronglyPredictable K.integrand_memLp_energy
  calc
    eLpNorm
        (finiteHorizonCompletedMartingalePart hUsual T Q hGMartingale
          hGMTerminal (K.restrictPredictable B hB) T)
        (2 : ENNReal) mu =
      eLpNorm (Function.uncurry (K.restrictPredictable B hB).integrand)
        (2 : ENNReal) Q.predictableEnergyMeasure := hRestrictedNorm
    _ = eLpNorm (B.indicator (Function.uncurry K.integrand))
        (2 : ENNReal) Q.predictableEnergyMeasure := by rw [hUncurry]
    _ ≤ eLpNorm (Function.uncurry K.integrand)
        (2 : ENNReal) Q.predictableEnergyMeasure := eLpNorm_indicator_le _ hB
    _ = eLpNorm
        (finiteHorizonCompletedMartingalePart hUsual T Q hGMartingale
          hGMTerminal K T)
        (2 : ENNReal) mu := hOriginalNorm.symm

omit [SigmaFiniteFiltration mu F] in
/-- The completed finite-variation part of a restricted coefficient is the
raw cumulative Stieltjes integral of the predictably restricted integrand. -/
theorem finiteHorizonCompletedFiniteVariationPart_restrictPredictable
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (E : SIntegrableFiniteVariationBridge G)
    (B : Set (NNReal × Omega)) (hB : MeasurableSet[F.predictable] B)
    (K : FiniteHorizonM2ACoefficient E Q) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedFiniteVariationPart hUsual T Q E
        (K.restrictPredictable B hB))
      (finiteVariationIntegralProcess E
        (PredictableProcess.restrict B K.integrand)) := by
  have hAgreement := finiteHorizonCompletedFiniteVariationPart_indistinguishable
    hUsual E Q (K.restrictPredictable B hB)
  have hIntegrand :=
    FiniteHorizonM2ACoefficient.restrictPredictable_integrand B hB K
  exact hAgreement.trans (Filter.Eventually.of_forall fun omega t => by
    exact congrFun
      (congrFun (congrArg (finiteVariationIntegralProcess E) hIntegrand)
        t) omega)

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
