/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.ElementaryPredictable

/-! # ElementaryIntegrand shared by the analytic interface and its implementation -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal ProbabilityTheory BigOperators

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

variable {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

namespace PredictableElementaryInterval

/-- The predictable integrand represented by one elementary block. -/
noncomputable def integrand
    (B : PredictableElementaryInterval ℱ) : Process Ω :=
  fun t ω =>
    if B.interval.startTime ω < t ∧ t ≤ B.interval.stopTime ω then
      B.interval.coefficient ω
    else 0

end PredictableElementaryInterval

namespace PredictableElementaryStrategy

/-- The finite sum of the integrand processes represented by an elementary
strategy. -/
noncomputable def integrand
    (H : PredictableElementaryStrategy ℱ) : Process Ω :=
  H.map PredictableElementaryInterval.integrand |>.sum

end PredictableElementaryStrategy

end FTAPTheorem42
