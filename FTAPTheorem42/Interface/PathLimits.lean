/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Process.Envelope.AllTimeCauchyLimit
import FTAPTheorem42.Foundations.TerminalLimit

/-! # Completeness of regular paths under uniform convergence in probability -/

namespace FTAPTheorem42.AnalyticInterface
open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]
  {F : Filtration NNReal (inferInstance : MeasurableSpace Ω)} {μ : Measure Ω}

theorem regular_uniform_limit
    (X : Nat → Process Ω) (hUsual : Filtration.UsualConditions μ F)
    (hX : ∀ n, StronglyAdapted F (X n))
    (hXR : ∀ n ω t, ContinuousWithinAt (X n · ω) (Ici t) t)
    (hXL : ∀ n, ProcessHasLeftLimits (X n))
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ →
      ∃ N, ∀ n m, N ≤ n → N ≤ m →
        μ {ω | ∃ t, ε ≤ ‖X n t ω - X m t ω‖} ≤ ENNReal.ofReal δ) :
    ∃ (f : Nat → Nat) (Y : Process Ω), StrictMono f ∧ StronglyAdapted F Y ∧
      (∀ ω t, ContinuousWithinAt (Y · ω) (Ici t) t) ∧ ProcessHasLeftLimits Y ∧
      ∀ᵐ ω ∂μ, TendstoUniformly (fun n t => X (f n) t ω) (Y · ω) atTop :=
  exists_cadlag_uniform_limit_of_allTimeGap_cauchyInMeasure X hUsual hX hXR hXL hcauchy

end FTAPTheorem42.AnalyticInterface
