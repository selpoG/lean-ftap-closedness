/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.DS.Lemma410.StrategyConvexification

/-!
# Predictable Hahn best-of strategies for Lemma 4.11

For two convexified strategies, restrict their difference to the positive
Hahn set of its finite-variation path measure and add that restriction to the
second strategy.  The resulting actual strategy follows the first integrand
on the positive set and the second integrand on its complement.  Its
finite-variation gains over both inputs are increasing, and their sum is the
total variation of the finite-variation difference.

The module also connects the martingale part of the Hahn restriction to the
predictable-indicator transform occurring in the Lemma 4.10 Emery
quasi-norm, using the compatibility of multiplication and restriction.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrablePredictableMultiplierLinearL2Calculus

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- The actual difference to which the Lemma 4.11 Hahn separator is
applied. -/
noncomputable def lemma411Difference
    (H K : SIntegrableStrategy D) : SIntegrableStrategy D :=
  H.subOfRightContinuous K

end SIntegrablePredictableMultiplierLinearL2Calculus

end FTAPTheorem42

namespace FTAPTheorem42

/-!
## Finite-horizon variation witnesses for Lemma 4.11

The Hahn best-of strategy has two nonnegative finite-variation improvements,
whose sum is the total variation of the original strategy difference.  This
module turns a positive-probability total-variation event into one of the two
oriented strict-improvement events, with the quantitative half-level and
half-mass bounds used in the maximality contradiction.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrablePredictableMultiplierLinearL2Calculus

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsProbabilityMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- Total variation of the finite-variation difference on one chronological
interval. -/
noncomputable def lemma411DifferenceVariation
    (H K : SIntegrableStrategy D) (a b : ℝ≥0) (ω : Ω) : ℝ :=
  (FiniteVariationPath.signedMeasure
    ((lemma411Difference H K).finiteVariationPart_isBoundedVariation ω)
    ).totalVariation.real (Set.Ioc a b)

/-- Total variation of the finite-variation difference on the whole
nonnegative time axis. -/
noncomputable def lemma411DifferenceTotalVariation
    (H K : SIntegrableStrategy D) (ω : Ω) : ℝ :=
  (FiniteVariationPath.signedMeasure
    ((lemma411Difference H K).finiteVariationPart_isBoundedVariation ω)
    ).totalVariation.real Set.univ

/-- Every finite-horizon difference variation is bounded by the whole-axis
total variation. -/
theorem lemma411DifferenceVariation_le_totalVariation
    (H K : SIntegrableStrategy D) (ω : Ω) (a b : ℝ≥0) :
    lemma411DifferenceVariation H K a b ω ≤
      lemma411DifferenceTotalVariation H K ω := by
  let ν := (FiniteVariationPath.signedMeasure
    ((lemma411Difference H K).finiteVariationPart_isBoundedVariation ω)
    ).totalVariation
  let : IsFiniteMeasure ν := by
    constructor
    change (FiniteVariationPath.signedMeasure
      ((lemma411Difference H K).finiteVariationPart_isBoundedVariation ω)
      ).totalVariation Set.univ < ∞
    rw [SignedMeasure.totalVariation, Measure.add_apply, ENNReal.add_lt_top]
    exact ⟨measure_lt_top _ _, measure_lt_top _ _⟩
  change ν.real (Set.Ioc a b) ≤ ν.real Set.univ
  exact measureReal_mono (Set.subset_univ _)

/-- The whole-axis total variation of a strategy difference is measurable. -/
theorem lemma411_differenceTotalVariation_measurable
    (H K : SIntegrableStrategy D) :
    Measurable (lemma411DifferenceTotalVariation H K) := by
  change Measurable fun ω =>
    (FiniteVariationPath.signedMeasure
      ((lemma411Difference H K).finiteVariationPart_isBoundedVariation ω)
      ).totalVariation.real Set.univ
  exact
    SIntegrableFiniteVariationBridge.measurable_totalVariation_univ_of_cumulativeVariation
      (H := lemma411Difference H K)
      (lemma411Difference H K).finiteVariationPart_isRightContinuous

end SIntegrablePredictableMultiplierLinearL2Calculus

end FTAPTheorem42
