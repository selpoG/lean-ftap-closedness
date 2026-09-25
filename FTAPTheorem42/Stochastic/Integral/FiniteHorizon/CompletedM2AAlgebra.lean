/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.M2ACoefficientAlgebra
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.MartingaleIntegralAlgebra
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationProcessCompletionAdditivity

/-!
# Scalar homogeneity of the completed finite-horizon M2A gain

The two selected process completions are homogeneous up to
indistinguishability.  Applying those results to the common scaled
coefficient yields homogeneity of their completed semimartingale gain.
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

/-- Scalar homogeneity of the completed martingale component when expressed
through a common finite-horizon coefficient. -/
theorem finiteHorizonCompletedMartingalePart_smul
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (hGMartingale : Martingale G.martingalePart F mu)
    (hGMTerminal : MemLp (G.martingalePart T) (2 : ENNReal) mu)
    (K : FiniteHorizonM2ACoefficient E Q) (c : Real) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedMartingalePart hUsual T Q hGMartingale
        hGMTerminal (K.smul c))
      (c • finiteHorizonCompletedMartingalePart hUsual T Q hGMartingale
        hGMTerminal K) := by
  have hIntegrand : Function.uncurry (K.smul c).integrand =
      c • Function.uncurry K.integrand :=
    congrArg Function.uncurry
      (FiniteHorizonM2ACoefficient.smul_integrand c K)
  have hAE : Function.uncurry (K.smul c).integrand
      =ᵐ[Q.predictableEnergyMeasure]
        c • Function.uncurry K.integrand :=
    Filter.Eventually.of_forall fun point => congrFun hIntegrand point
  have hCongr := finiteHorizonMartingaleIntegralProcess_indistinguishable_of_ae_eq
    hUsual Q hGMartingale G.martingalePart_isRightContinuous hGMTerminal
      (Function.uncurry (K.smul c).integrand)
      (K.smul c).integrand_isStronglyPredictable
      (K.smul c).integrand_memLp_energy
      (c • Function.uncurry K.integrand)
      (K.integrand_isStronglyPredictable.const_smul c)
      (K.integrand_memLp_energy.const_smul c) hAE
  exact hCongr.trans (finiteHorizonMartingaleIntegralProcess_smul
    hUsual Q hGMartingale G.martingalePart_isRightContinuous hGMTerminal
      (Function.uncurry K.integrand) K.integrand_isStronglyPredictable
        K.integrand_memLp_energy c)

omit [SigmaFiniteFiltration mu F] in
/-- Scalar homogeneity of the completed finite-variation component when
expressed through a common finite-horizon coefficient. -/
theorem finiteHorizonCompletedFiniteVariationPart_smul
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (E : SIntegrableFiniteVariationBridge G)
    (K : FiniteHorizonM2ACoefficient E Q) (c : Real) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedFiniteVariationPart hUsual T Q E (K.smul c))
      (c • finiteHorizonCompletedFiniteVariationPart hUsual T Q E K) := by
  have hIntegrand := FiniteHorizonM2ACoefficient.smul_integrand c K
  have hCongr : ProcessIndistinguishable mu
      (completedFiniteVariationProcess hUsual E (K.smul c).integrand
        (K.smul c).integrand_isStronglyPredictable
          (K.smul c).integrand_memLp_variation)
      (completedFiniteVariationProcess hUsual E (c • K.integrand)
        (K.integrand_isStronglyPredictable.const_smul c)
          (K.integrand_memLp_variation.const_smul c)) := by
    have hLeft := completedFiniteVariationProcess_indistinguishable
      hUsual E (K.smul c).integrand
        (K.smul c).integrand_isStronglyPredictable
          (K.smul c).integrand_memLp_variation
    have hRight := completedFiniteVariationProcess_indistinguishable
      hUsual E (c • K.integrand)
        (K.integrand_isStronglyPredictable.const_smul c)
          (K.integrand_memLp_variation.const_smul c)
    filter_upwards [hLeft, hRight] with omega hLeftOmega hRightOmega
    intro t
    exact (hLeftOmega t).trans ((congrArg
      (fun integrand => finiteVariationIntegralProcess E integrand t omega)
        hIntegrand).trans (hRightOmega t).symm)
  exact hCongr.trans (completedFiniteVariationProcess_smul
    hUsual E K.integrand K.integrand_isStronglyPredictable
      K.integrand_memLp_variation c)

/-- The completed finite-horizon `M2 + A1` gain commutes with deterministic
real scalar multiplication, up to process indistinguishability. -/
theorem finiteHorizonCompletedM2AGain_smul
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (E : SIntegrableFiniteVariationBridge G)
    (hGMartingale : Martingale G.martingalePart F mu)
    (hGMTerminal : MemLp (G.martingalePart T) (2 : ENNReal) mu)
    (K : FiniteHorizonM2ACoefficient E Q) (c : Real) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedM2AGain hUsual T Q E hGMartingale
        hGMTerminal (K.smul c))
      (c • finiteHorizonCompletedM2AGain hUsual T Q E hGMartingale
        hGMTerminal K) := by
  have hM := finiteHorizonCompletedMartingalePart_smul
    hUsual Q hGMartingale hGMTerminal K c
  have hA := finiteHorizonCompletedFiniteVariationPart_smul
    hUsual Q E K c
  filter_upwards [hM, hA] with omega hMOmega hAOmega
  intro t
  change
    finiteHorizonCompletedMartingalePart hUsual T Q hGMartingale
          hGMTerminal (K.smul c) t omega +
        finiteHorizonCompletedFiniteVariationPart hUsual T Q E
          (K.smul c) t omega =
      c * (finiteHorizonCompletedMartingalePart hUsual T Q hGMartingale
          hGMTerminal K t omega +
        finiteHorizonCompletedFiniteVariationPart hUsual T Q E K t omega)
  rw [hMOmega t, hAOmega t]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
