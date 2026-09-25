/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import Mathlib.Topology.EMetricSpace.BoundedVariation
import FTAPTheorem42.Foundations.Paths

/-! # Decomposition shared by the analytic interface and its implementation -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal ProbabilityTheory BigOperators

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Every regular zero-initial local-martingale/FV decomposition is admitted.
The finite-variation part is adapted, and need not be predictable. -/
structure J1Decomposition (X : Process Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω)) (mu : Measure Ω) where
  N : Process Ω
  A : Process Ω
  decomposition : ProcessIndistinguishable mu X (fun t w => N t w + A t w)
  localMartingale : LocalMartingale N F mu
  adaptedN : StronglyAdapted F N
  rightN : ∀ w t, ContinuousWithinAt (N · w) (Ici t) t
  leftN : ProcessHasLeftLimits N
  zeroN : N 0 = 0
  adaptedA : StronglyAdapted F A
  rightA : ∀ w t, ContinuousWithinAt (A · w) (Ici t) t
  leftA : ProcessHasLeftLimits A
  variationA : ∀ w, LocallyBoundedVariationOn (A · w) univ
  zeroA : A 0 = 0

end FTAPTheorem42
