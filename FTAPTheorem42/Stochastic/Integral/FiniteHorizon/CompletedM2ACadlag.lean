/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedM2ARealization
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.MartingaleIntegralCadlag

/-!
# Càdlàg representatives of completed finite-horizon M2A graphs

For a source martingale with left limits, the completed martingale operator
has a càdlàg version.  Combining that version with the existing completed
finite-variation process gives a concrete representative of the same
finite-horizon `M² ⊕ A¹` graph.  Graph extensionality then places this
representative in the existing completed realization carrier.
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

/-- The càdlàg completed martingale component associated with a common
finite-horizon coefficient. -/
noncomputable def finiteHorizonCompletedMartingaleCadlagPart
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (hGMartingale : Martingale G.martingalePart F mu)
    (hGMLeft : ProcessHasLeftLimits G.martingalePart)
    (hGMTerminal : MemLp (G.martingalePart T) (2 : ENNReal) mu)
    (c : FiniteHorizonM2ACoefficient E Q) : Process Omega :=
  finiteHorizonMartingaleIntegralCadlagProcess
    hUsual Q hGMartingale G.martingalePart_isRightContinuous hGMLeft
      hGMTerminal (Function.uncurry c.integrand)
      c.integrand_isStronglyPredictable c.integrand_memLp_energy

/-- The càdlàg martingale component is a version of the original completed
component. -/
theorem finiteHorizonCompletedMartingaleCadlagPart_indistinguishable
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (hGMartingale : Martingale G.martingalePart F mu)
    (hGMLeft : ProcessHasLeftLimits G.martingalePart)
    (hGMTerminal : MemLp (G.martingalePart T) (2 : ENNReal) mu)
    (c : FiniteHorizonM2ACoefficient E Q) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedMartingaleCadlagPart hUsual Q hGMartingale
        hGMLeft hGMTerminal c)
      (finiteHorizonCompletedMartingalePart hUsual T Q hGMartingale
        hGMTerminal c) :=
  finiteHorizonMartingaleIntegralCadlagProcess_indistinguishable
    hUsual Q hGMartingale G.martingalePart_isRightContinuous hGMLeft
      hGMTerminal (Function.uncurry c.integrand)
      c.integrand_isStronglyPredictable c.integrand_memLp_energy

/-- The completed gain using the càdlàg martingale representative. -/
noncomputable def finiteHorizonCompletedM2ACadlagGain
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (E : SIntegrableFiniteVariationBridge G)
    (hGMartingale : Martingale G.martingalePart F mu)
    (hGMLeft : ProcessHasLeftLimits G.martingalePart)
    (hGMTerminal : MemLp (G.martingalePart T) (2 : ENNReal) mu)
    (c : FiniteHorizonM2ACoefficient E Q) : Process Omega :=
  fun t omega =>
    finiteHorizonCompletedMartingaleCadlagPart hUsual Q hGMartingale
        hGMLeft hGMTerminal c t omega +
      finiteHorizonCompletedFiniteVariationPart hUsual T Q E c t omega

/-- Replacing the martingale component by its càdlàg version does not change
the completed gain graph. -/
theorem finiteHorizonCompletedM2ACadlagGain_indistinguishable
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (E : SIntegrableFiniteVariationBridge G)
    (hGMartingale : Martingale G.martingalePart F mu)
    (hGMLeft : ProcessHasLeftLimits G.martingalePart)
    (hGMTerminal : MemLp (G.martingalePart T) (2 : ENNReal) mu)
    (c : FiniteHorizonM2ACoefficient E Q) :
    ProcessIndistinguishable mu
      (finiteHorizonCompletedM2ACadlagGain hUsual Q E hGMartingale
        hGMLeft hGMTerminal c)
      (finiteHorizonCompletedM2AGain hUsual T Q E hGMartingale
        hGMTerminal c) :=
  (finiteHorizonCompletedMartingaleCadlagPart_indistinguishable
    hUsual Q hGMartingale hGMLeft hGMTerminal c).add
      (ProcessIndistinguishable.refl mu _)

/-- A raw càdlàg strategy representing the completed finite-horizon graph. -/
noncomputable def finiteHorizonCompletedM2ACadlagStrategy
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (E : SIntegrableFiniteVariationBridge G)
    (hGMartingale : Martingale G.martingalePart F mu)
    (hGMLeft : ProcessHasLeftLimits G.martingalePart)
    (hGMTerminal : MemLp (G.martingalePart T) (2 : ENNReal) mu)
    (c : FiniteHorizonM2ACoefficient E Q) : SIntegrableStrategy D := by
  let I : Process Omega := finiteHorizonCompletedMartingaleCadlagPart
    hUsual Q hGMartingale hGMLeft hGMTerminal c
  let B : Process Omega := finiteHorizonCompletedFiniteVariationPart
    hUsual T Q E c
  have hIMartingale : Martingale I F mu :=
    finiteHorizonMartingaleIntegralCadlagProcess_isMartingale
      hUsual Q hGMartingale G.martingalePart_isRightContinuous hGMLeft
        hGMTerminal (Function.uncurry c.integrand)
        c.integrand_isStronglyPredictable c.integrand_memLp_energy
  have hIRight : ∀ omega t,
      ContinuousWithinAt (I · omega) (Ici t) t :=
    finiteHorizonMartingaleIntegralCadlagProcess_rightContinuous
      hUsual Q hGMartingale G.martingalePart_isRightContinuous hGMLeft
        hGMTerminal (Function.uncurry c.integrand)
        c.integrand_isStronglyPredictable c.integrand_memLp_energy
  have hBPredictable : IsStronglyPredictable F B :=
    completedFiniteVariationProcess_isStronglyPredictable
      hUsual E c.integrand c.integrand_isStronglyPredictable
        c.integrand_memLp_variation
  have hBRight : ∀ omega t,
      ContinuousWithinAt (B · omega) (Ici t) t :=
    completedFiniteVariationProcess_rightContinuous
      hUsual E c.integrand c.integrand_isStronglyPredictable
        c.integrand_memLp_variation
  have hBVariation : ∀ omega,
      BoundedVariationOn (B · omega) Set.univ :=
    completedFiniteVariationProcess_isBoundedVariation
      hUsual E c.integrand c.integrand_isStronglyPredictable
        c.integrand_memLp_variation
  exact {
    integrand := c.integrand
    stochasticIntegral := fun t omega => I t omega + B t omega
    martingalePart := I
    finiteVariationPart := B
    finiteVariationMeasure := 0
    integrand_isPredictable := c.integrand_isStronglyPredictable
    stochasticIntegral_isStronglyAdapted :=
      hIMartingale.stronglyAdapted.add hBPredictable.stronglyAdapted
    stochasticIntegral_isRightContinuous := fun omega t =>
      (hIRight omega t).add (hBRight omega t)
    martingalePart_isLocalMartingale := ProbabilityTheory.Locally.of_prop
      hIMartingale
    martingalePart_isStronglyAdapted := hIMartingale.stronglyAdapted
    martingalePart_isRightContinuous := hIRight
    finiteVariationPart_isPredictable := hBPredictable
    finiteVariationPart_isRightContinuous := hBRight
    finiteVariationPart_isBoundedVariation := hBVariation
    integral_decomposition := ProcessIndistinguishable.refl mu _
    source_decomposition := G.source_decomposition }

/-- The càdlàg representative's martingale coordinate has left limits. -/
theorem finiteHorizonCompletedM2ACadlagStrategy_martingalePart_hasLeftLimits
    (hUsual : Filtration.UsualConditions mu F)
    (Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T)
    (E : SIntegrableFiniteVariationBridge G)
    (hGMartingale : Martingale G.martingalePart F mu)
    (hGMLeft : ProcessHasLeftLimits G.martingalePart)
    (hGMTerminal : MemLp (G.martingalePart T) (2 : ENNReal) mu)
    (c : FiniteHorizonM2ACoefficient E Q) :
    ProcessHasLeftLimits
      (finiteHorizonCompletedM2ACadlagStrategy hUsual Q E hGMartingale
        hGMLeft hGMTerminal c).martingalePart :=
  finiteHorizonMartingaleIntegralCadlagProcess_hasLeftLimits
    hUsual Q hGMartingale G.martingalePart_isRightContinuous hGMLeft
      hGMTerminal (Function.uncurry c.integrand)
      c.integrand_isStronglyPredictable c.integrand_memLp_energy

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
