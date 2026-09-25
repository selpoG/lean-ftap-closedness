/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.DS.Lemma411.VariationWitness
import FTAPTheorem42.Stochastic.Memin.SummableL1Limit
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-!
# Predictable limits under countably many local control measures

In the Mémín closedness proof, prelocal `S¹` control makes the integrands
Cauchy modulo each stopped integrator.  The stopped integrators give a
countable family of measures on the predictable sigma-algebra.  This module
performs the measure-theoretic diagonal step: one strict subsequence converges
almost everywhere for every control measure, and its `limUnder` is strongly
predictable.

No stochastic-integral identity is assumed or concluded here.  The remaining
closedness step must still show that the component-gauge estimates imply the
control-measure Cauchy hypothesis and that the resulting predictable limit
integrates to the component-process limit.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A nonnegative control measure carried by the predictable sigma algebra. -/
abbrev MeminPredictableControlMeasure
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) :=
  @Measure (ℝ≥0 × Ω) ℱ.predictable

end FTAPTheorem42

namespace FTAPTheorem42

/-!
## Predictable control-measure `L¹` estimates in the Mémín argument

The local `S¹` step in Mémín's closedness proof controls the difference of
two integrands in `L¹` of a measure on the predictable sigma algebra.  This
module turns that quantitative integral estimate into the event-tail
hypothesis used by `exists_meminPredictableLimit_of_countableControl_cauchy`.

The square in the hypothesis is intentional: Markov's inequality at level
`ε` then gives control-measure mass at most `ε`.  No finiteness assumption on
the control measure is needed.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SIntegrablePredictableMultiplierLinearL2Calculus

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω}
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- Pointwise difference of two actual strategy integrands, viewed on
predictable time--sample space. -/
def meminIntegrandDifference
    (H K : SIntegrableStrategy D) : ℝ≥0 × Ω → ℝ := fun p =>
  H.integrand p.1 p.2 - K.integrand p.1 p.2

/-- The canonical pointwise limit of a sequence of actual strategy
integrands.  Summable local `L¹` steps will force convergence to this same
process under every stopped control measure. -/
noncomputable def meminLimitIntegrand
    (H : ℕ → SIntegrableStrategy D) : Process Ω := fun t ω =>
  limUnder atTop (fun k => (H k).integrand t ω)

/-- The canonical pointwise limit of predictable integrands remains strongly
predictable, independently of any convergence hypothesis. -/
theorem meminLimitIntegrand_isStronglyPredictable
    (H : ℕ → SIntegrableStrategy D) :
    IsStronglyPredictable ℱ (meminLimitIntegrand H) := by
  change StronglyMeasurable[ℱ.predictable]
    (fun p : ℝ≥0 × Ω => limUnder atTop
      (fun k => (H k).integrand p.1 p.2))
  exact @MeasureTheory.StronglyMeasurable.limUnder
    ℕ (ℝ≥0 × Ω) ℝ ℱ.predictable _ _ atTop _
    (fun k p => (H k).integrand p.1 p.2) _ _
    (fun k => (H k).integrand_isPredictable)

/-- The predictable-control `L¹` size of the difference of two actual
strategy integrands. -/
noncomputable def meminIntegrandDifferenceLIntegral
    (control : MeminPredictableControlMeasure ℱ)
    (H K : SIntegrableStrategy D) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal
    |meminIntegrandDifference H K p| ∂control

/-- The integrand difference is strongly measurable on predictable
time--sample space. -/
theorem meminIntegrandDifference_stronglyMeasurable
    (H K : SIntegrableStrategy D) :
    StronglyMeasurable[ℱ.predictable] (meminIntegrandDifference H K) :=
  H.integrand_isPredictable.sub K.integrand_isPredictable

end SIntegrablePredictableMultiplierLinearL2Calculus

end FTAPTheorem42
