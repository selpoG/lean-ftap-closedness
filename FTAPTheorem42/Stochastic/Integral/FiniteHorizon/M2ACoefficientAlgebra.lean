/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Integral.FiniteHorizon.CompletedM2ARealization

/-!
# Algebra of finite-horizon M2A coefficients

The two control-space memberships carried by a common finite-horizon
coefficient are preserved by deterministic real scalar multiplication.  The
horizon restriction of the scaled coefficient is the corresponding scalar
multiple of the original restricted process.
-/

namespace FTAPTheorem42

open MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega]

namespace SIntegrableFiniteVariationBridge

open BoundedMartingaleQuadraticEnergy.Data

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : SIntegrableStrategy D}
  {T : NNReal}

namespace FiniteHorizonM2ACoefficient

/-- Deterministic scalar multiplication preserves both finite-horizon
control-space memberships. -/
def smul
    {E : SIntegrableFiniteVariationBridge G}
    {Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T}
    (c : Real) (K : FiniteHorizonM2ACoefficient E Q) :
    FiniteHorizonM2ACoefficient E Q where
  coefficient := c • K.coefficient
  coefficient_isStronglyMeasurable :=
    K.coefficient_isStronglyMeasurable.const_smul c
  coefficient_memLp_variation := K.coefficient_memLp_variation.const_smul c
  coefficient_memLp_energy := K.coefficient_memLp_energy.const_smul c

/-- Horizon restriction commutes with scalar multiplication. -/
theorem smul_integrand
    {E : SIntegrableFiniteVariationBridge G}
    {Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T}
    (c : Real) (K : FiniteHorizonM2ACoefficient E Q) :
    (K.smul c).integrand = c • K.integrand := by
  unfold integrand finiteHorizonCoefficient
  exact PredictableProcess.restrict_smul _ _ _

end FiniteHorizonM2ACoefficient

end SIntegrableFiniteVariationBridge

/-!
## Additivity of finite-horizon M2A coefficients

The common martingale-energy and finite-variation control memberships are
closed under addition.  This is the coefficient-level input for additivity
of the two completed stochastic-integral operators.
-/

namespace SIntegrableFiniteVariationBridge

variable {S : Process Omega}
  {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
  {mu : Measure Omega} [IsProbabilityMeasure mu]
  {D : SpecialSemimartingaleDecomposition S F mu}
  {G : SIntegrableStrategy D}
  {T : NNReal}

namespace FiniteHorizonM2ACoefficient

/-- Addition preserves both finite-horizon control-space memberships. -/
def add
    {E : SIntegrableFiniteVariationBridge G}
    {Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T}
    (K L : FiniteHorizonM2ACoefficient E Q) :
    FiniteHorizonM2ACoefficient E Q where
  coefficient := K.coefficient + L.coefficient
  coefficient_isStronglyMeasurable :=
    K.coefficient_isStronglyMeasurable.add L.coefficient_isStronglyMeasurable
  coefficient_memLp_variation :=
    K.coefficient_memLp_variation.add L.coefficient_memLp_variation
  coefficient_memLp_energy :=
    K.coefficient_memLp_energy.add L.coefficient_memLp_energy

/-- Horizon restriction commutes with coefficient addition. -/
theorem add_integrand
    {E : SIntegrableFiniteVariationBridge G}
    {Q : BoundedMartingaleQuadraticKernel.Data
      F mu G.martingalePart T}
    (K L : FiniteHorizonM2ACoefficient E Q) :
    (K.add L).integrand = K.integrand + L.integrand := by
  unfold integrand finiteHorizonCoefficient
  exact PredictableProcess.restrict_add _ _ _

end FiniteHorizonM2ACoefficient

end SIntegrableFiniteVariationBridge

end FTAPTheorem42
