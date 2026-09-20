/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import FTAPTheorem42.Foundations.ElementaryIntegrand

/-! # Semimartingale shared by the analytic interface and its implementation -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal ProbabilityTheory BigOperators

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Uniform convergence to zero of predictable elementary integrands on
`NNReal × Ω`. -/
def ElementaryIntegrandsTendstoUniformlyZero
    {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    (H : Nat → PredictableElementaryStrategy F) : Prop :=
  ∀ ε : Real, 0 < ε → ∀ᶠ n in atTop, ∀ t omega,
    |PredictableElementaryStrategy.integrand (H n) t omega| ≤ ε

/-- Bichteler--Dellacherie good-integrator predicate for a real-valued source
process.  The elementary gain is the already-defined pathwise finite sum. -/
def IsSemimartingale
    (S : Process Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (mu : Measure Ω) : Prop :=
  (∀ (H : PredictableElementaryStrategy F) (T : NNReal),
      AEStronglyMeasurable
        (ElementaryStrategy.gain S H.toElementary T) mu) ∧
    ∀ (H : Nat → PredictableElementaryStrategy F),
      ElementaryIntegrandsTendstoUniformlyZero H →
        ∀ T : NNReal, TendstoInMeasure mu
          (fun n => ElementaryStrategy.gain S (H n).toElementary T)
          atTop 0

end FTAPTheorem42
