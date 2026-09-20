/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Stochastic.DS.Lemma410.StrategyConvexification
import FTAPTheorem42.Stochastic.Integral.Calculus.SIntegrableRealizationModel
import FTAPTheorem42.Trading.Basic

/-!
# Actual finite convex combinations of stochastic-integral strategies

The raw strategy algebra constructs the finite convex combinations selected
by the Hilbert argument, but raw regularity data alone do not certify that
the result belongs to a concrete stochastic-integration range.  This module
records precisely that carrier-level closure and packages the raw convex
combination as an `ActualSIntegrableStrategy`.
-/

open Filter MeasureTheory Topology
open scoped NNReal

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A realization carrier is closed under the finite tail convex
combinations used in Lemmas 4.10--4.11. -/
structure SIntegrableActualConvexCombinationCalculus
    {S : Process Ω}
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {μ : Measure Ω} [IsFiniteMeasure μ] [SigmaFiniteFiltration μ ℱ]
    {D : SpecialSemimartingaleDecomposition S ℱ μ}
    (R : SIntegrableRealizationModel D) where
  tailConvexCombination_isRealized :
    ∀ (H : ℕ → ActualSIntegrableStrategy R) {n : ℕ}
      (w : TailConvexWeights n),
      R.IsRealized
        (SIntegrableStrategy.tailConvexCombination
          (ActualSIntegrableStrategy.rawSequence H) w)

namespace SIntegrableActualConvexCombinationCalculus

variable {S : Process Ω}
  {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {μ : Measure Ω} [IsFiniteMeasure μ] [SigmaFiniteFiltration μ ℱ]
  {D : SpecialSemimartingaleDecomposition S ℱ μ}
  {R : SIntegrableRealizationModel D}

/-- The Hilbert tail weights, realized on the actual carrier without
changing their raw strategy record. -/
noncomputable def tailConvexCombination
    (C : SIntegrableActualConvexCombinationCalculus R)
    (H : ℕ → ActualSIntegrableStrategy R) {n : ℕ}
    (w : TailConvexWeights n) : ActualSIntegrableStrategy R :=
  ⟨SIntegrableStrategy.tailConvexCombination
      (ActualSIntegrableStrategy.rawSequence H) w,
    C.tailConvexCombination_isRealized H w⟩

end SIntegrableActualConvexCombinationCalculus

end FTAPTheorem42
