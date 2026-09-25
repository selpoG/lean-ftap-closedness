/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.Semimartingale
import FTAPTheorem42.Foundations.UsualConditions

/-! # BoundedSource shared by the analytic interface and its implementation -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal ProbabilityTheory BigOperators

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A bounded real-valued càdlàg semimartingale source on a filtered
probability space. -/
structure BoundedSemimartingaleSource
    (S : Process Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (mu : Measure Ω) [IsProbabilityMeasure mu] where
  usualConditions : Filtration.UsualConditions mu F
  stronglyAdapted : StronglyAdapted F S
  rightContinuous : ∀ omega t,
    ContinuousWithinAt (S · omega) (Set.Ici t) t
  hasLeftLimits : ProcessHasLeftLimits S
  bound : Real
  uniformBound : ∀ᵐ omega ∂mu, ∀ t, |S t omega| ≤ bound
  isSemimartingale : IsSemimartingale S F mu

end FTAPTheorem42
