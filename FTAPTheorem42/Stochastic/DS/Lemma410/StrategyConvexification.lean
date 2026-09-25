/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.DS.Lemma410.StoppedPrefixMartingale
import FTAPTheorem42.Stochastic.Topology.Emery.TruncatedExpectation
import Mathlib.Analysis.Normed.Group.Tannery
import FTAPTheorem42.Stochastic.DS.Lemma48.NormalizedTail
import FTAPTheorem42.Foundations.MaximalProbability
import FTAPTheorem42.Stochastic.DS.Lemma49.StoppedTailMartingale

/-!
# Actual common convexifications for Lemma 4.10

The Hilbert argument selects finite-support `TailConvexWeights`.  Lemma 4.9
and the realized-strategy algebra use weights on an initial finite range.
This module converts the support without changing any coefficient, realizes
the resulting convex combinations as actual `SIntegrableStrategy` objects,
and proves the individual stopped-prefix/post-passage-tail decomposition at
every integer coordinate.  In particular, no strategy-dependent stopping is
commuted with convexification.
-/

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

namespace TailConvexWeights

/-- A canonical initial range containing the finite support. -/
def rangeSize {n : ℕ} (w : TailConvexWeights n) : ℕ :=
  w.support.sup id + 1

theorem support_subset_rangeSize {n : ℕ} (w : TailConvexWeights n) :
    w.support ⊆ Finset.range w.rangeSize := by
  intro i hi
  rw [Finset.mem_range]
  exact Nat.lt_succ_of_le
    (Finset.le_sup (f := fun j : ℕ => j) hi)

theorem coeff_nonneg_on_rangeSize {n : ℕ} (w : TailConvexWeights n) :
    ∀ i ∈ Finset.range w.rangeSize, 0 ≤ w.coeff i := by
  intro i _hi
  exact w.coeff_nonneg i

theorem sum_coeff_rangeSize_eq_one {n : ℕ} (w : TailConvexWeights n) :
    ∑ i ∈ Finset.range w.rangeSize, w.coeff i = 1 :=
  w.sum_coeff_superset_eq_one w.support_subset_rangeSize

end TailConvexWeights

namespace SIntegrableStrategy

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsFiniteMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}

/-- Realize fixed-tail weights as one actual finite convex combination of
strategies. Coefficients outside the declared support are zero. -/
noncomputable def tailConvexCombination
    (H : ℕ → SIntegrableStrategy D) {n : ℕ}
    (w : TailConvexWeights n) : SIntegrableStrategy D :=
  weightedPrefixSum H w.coeff w.rangeSize

@[simp]
theorem tailConvexCombination_integrand_apply
    (H : ℕ → SIntegrableStrategy D) {n : ℕ}
    (w : TailConvexWeights n) (t : ℝ≥0) (ω : Ω) :
    (tailConvexCombination H w).integrand t ω =
      w.apply (fun i => (H i).integrand t) ω := by
  rw [tailConvexCombination, weightedPrefixSum_integrand_apply]
  exact congrFun
    (w.apply_eq_sum_coeff_superset w.support_subset_rangeSize
      (fun i => (H i).integrand t)) ω

@[simp]
theorem tailConvexCombination_martingalePart_apply
    (H : ℕ → SIntegrableStrategy D) {n : ℕ}
    (w : TailConvexWeights n) (t : ℝ≥0) (ω : Ω) :
    (tailConvexCombination H w).martingalePart t ω =
      w.apply (fun i => (H i).martingalePart t) ω := by
  rw [tailConvexCombination, weightedPrefixSum_martingalePart_apply]
  exact congrFun
    (w.apply_eq_sum_coeff_superset w.support_subset_rangeSize
      (fun i => (H i).martingalePart t)) ω

/-!
## Martingale-part Cauchy estimate for Lemma 4.10

The common Hilbert weights control the passage-stopped prefix at every
integer horizon.  This section realizes differences of the actual convexified
strategies, transports the prefix/tail decomposition through one bounded
predictable multiplier, and combines the prefix `L²` estimate with the two
Lemma 4.9 tail estimates in the semimartingale quasi-norm.
-/

/-- Difference of two actual strategies, constructed with the synchronized
right-continuous localizing calculus. -/
noncomputable def subOfRightContinuous
    (H K : SIntegrableStrategy D) : SIntegrableStrategy D :=
  H.add_of_rightContinuous K.neg

end SIntegrableStrategy

end FTAPTheorem42
