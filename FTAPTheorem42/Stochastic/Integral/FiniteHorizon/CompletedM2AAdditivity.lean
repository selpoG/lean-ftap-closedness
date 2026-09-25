/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.M2ACoefficientAlgebra
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.MartingaleIntegralAdditivity
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationProcessCompletionAdditivity

/-!
# Additivity of the completed finite-horizon M2A gain

The martingale and finite-variation completions are additive for one common
finite-horizon integrator.  Applying those laws to the sum of two common
coefficients proves additivity of the completed semimartingale gain.
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

/-- Additivity of the completed martingale component for two coefficients
over one finite-horizon quadratic-energy control. -/
theorem finiteHorizonCompletedMartingalePart_add
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (hGMartingale : Martingale G.martingalePart F mu)
    (hGMTerminal : MemLp (G.martingalePart T) (2 : ENNReal) mu)
    (K L : FiniteHorizonM2ACoefficient E Q) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedMartingalePart hUsual T Q hGMartingale
        hGMTerminal (K.add L))
      (finiteHorizonCompletedMartingalePart hUsual T Q hGMartingale
          hGMTerminal K +
        finiteHorizonCompletedMartingalePart hUsual T Q hGMartingale
          hGMTerminal L) := by
  have hIntegrand : Function.uncurry (K.add L).integrand =
      Function.uncurry K.integrand + Function.uncurry L.integrand :=
    congrArg Function.uncurry
      (FiniteHorizonM2ACoefficient.add_integrand K L)
  have hAE : Function.uncurry (K.add L).integrand
      =ᵐ[Q.predictableEnergyMeasure]
        Function.uncurry K.integrand + Function.uncurry L.integrand :=
    Filter.Eventually.of_forall fun point => congrFun hIntegrand point
  have hCongr := finiteHorizonMartingaleIntegralProcess_indistinguishable_of_ae_eq
    hUsual Q hGMartingale G.martingalePart_isRightContinuous hGMTerminal
      (Function.uncurry (K.add L).integrand)
      (K.add L).integrand_isStronglyPredictable
      (K.add L).integrand_memLp_energy
      (Function.uncurry K.integrand + Function.uncurry L.integrand)
      (K.integrand_isStronglyPredictable.add L.integrand_isStronglyPredictable)
      (K.integrand_memLp_energy.add L.integrand_memLp_energy) hAE
  exact hCongr.trans (finiteHorizonMartingaleIntegralProcess_add
    hUsual Q hGMartingale G.martingalePart_isRightContinuous hGMTerminal
      (Function.uncurry K.integrand) (Function.uncurry L.integrand)
      K.integrand_isStronglyPredictable L.integrand_isStronglyPredictable
      K.integrand_memLp_energy L.integrand_memLp_energy)

omit [SigmaFiniteFiltration mu F] in
/-- Additivity of the completed finite-variation component for two
coefficients over one finite-horizon variation control. -/
theorem finiteHorizonCompletedFiniteVariationPart_add
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (E : SIntegrableFiniteVariationBridge G)
    (K L : FiniteHorizonM2ACoefficient E Q) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedFiniteVariationPart hUsual T Q E (K.add L))
      (finiteHorizonCompletedFiniteVariationPart hUsual T Q E K +
        finiteHorizonCompletedFiniteVariationPart hUsual T Q E L) := by
  have hIntegrand := FiniteHorizonM2ACoefficient.add_integrand K L
  have hCongr : ProcessIndistinguishable mu
      (completedFiniteVariationProcess hUsual E (K.add L).integrand
        (K.add L).integrand_isStronglyPredictable
          (K.add L).integrand_memLp_variation)
      (completedFiniteVariationProcess hUsual E
        (K.integrand + L.integrand)
        (K.integrand_isStronglyPredictable.add L.integrand_isStronglyPredictable)
        (K.integrand_memLp_variation.add L.integrand_memLp_variation)) := by
    have hLeft := completedFiniteVariationProcess_indistinguishable
      hUsual E (K.add L).integrand
        (K.add L).integrand_isStronglyPredictable
          (K.add L).integrand_memLp_variation
    have hRight := completedFiniteVariationProcess_indistinguishable
      hUsual E (K.integrand + L.integrand)
        (K.integrand_isStronglyPredictable.add L.integrand_isStronglyPredictable)
        (K.integrand_memLp_variation.add L.integrand_memLp_variation)
    filter_upwards [hLeft, hRight] with omega hLeftOmega hRightOmega
    intro t
    exact (hLeftOmega t).trans ((congrArg
      (fun integrand => finiteVariationIntegralProcess E integrand t omega)
        hIntegrand).trans (hRightOmega t).symm)
  exact hCongr.trans (completedFiniteVariationProcess_add
    hUsual E K.integrand L.integrand
      K.integrand_isStronglyPredictable L.integrand_isStronglyPredictable
      K.integrand_memLp_variation L.integrand_memLp_variation)

/-- The completed finite-horizon `M2 + A1` gain is additive for two
coefficients over the same source prefix and controls. -/
theorem finiteHorizonCompletedM2AGain_add
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (E : SIntegrableFiniteVariationBridge G)
    (hGMartingale : Martingale G.martingalePart F mu)
    (hGMTerminal : MemLp (G.martingalePart T) (2 : ENNReal) mu)
    (K L : FiniteHorizonM2ACoefficient E Q) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedM2AGain hUsual T Q E hGMartingale
        hGMTerminal (K.add L))
      (finiteHorizonCompletedM2AGain hUsual T Q E hGMartingale
          hGMTerminal K +
        finiteHorizonCompletedM2AGain hUsual T Q E hGMartingale
          hGMTerminal L) := by
  have hM := finiteHorizonCompletedMartingalePart_add
    hUsual Q hGMartingale hGMTerminal K L
  have hA := finiteHorizonCompletedFiniteVariationPart_add
    hUsual Q E K L
  filter_upwards [hM, hA] with omega hMOmega hAOmega
  intro t
  change
    finiteHorizonCompletedMartingalePart hUsual T Q hGMartingale
          hGMTerminal (K.add L) t omega +
        finiteHorizonCompletedFiniteVariationPart hUsual T Q E
          (K.add L) t omega =
      (finiteHorizonCompletedMartingalePart hUsual T Q hGMartingale
          hGMTerminal K t omega +
        finiteHorizonCompletedFiniteVariationPart hUsual T Q E K t omega) +
      (finiteHorizonCompletedMartingalePart hUsual T Q hGMartingale
          hGMTerminal L t omega +
        finiteHorizonCompletedFiniteVariationPart hUsual T Q E L t omega)
  rw [hMOmega t, hAOmega t]
  simp only [Pi.add_apply]
  ring

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
