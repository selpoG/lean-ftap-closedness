/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.LocalProperty

/-! # Process shared by the analytic interface and its implementation -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal ProbabilityTheory BigOperators

namespace FTAPTheorem42

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A real-valued process on nonnegative real time. -/
abbrev Process (Ω : Type*) := ℝ≥0 → Ω → ℝ

omit [MeasurableSpace Ω] in
@[simp]
theorem stoppedProcess_const_apply
    (M : Process Ω) (c u : ℝ≥0) (ω : Ω) :
    MeasureTheory.stoppedProcess M
        (fun _ : Ω => (c : WithTop ℝ≥0)) u ω =
      M (min u c) ω := by
  simp only [MeasureTheory.stoppedProcess, ← WithTop.coe_min,
    WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]

/-- A process stopped at a deterministic horizon. -/
noncomputable def deterministicallyStoppedProcess (X : Process Ω) (T : ℝ≥0) :
    Process Ω :=
  MeasureTheory.stoppedProcess X (fun _ : Ω => (T : WithTop ℝ≥0))

omit [MeasurableSpace Ω] in
@[simp] theorem deterministicallyStoppedProcess_apply
    (X : Process Ω) (T t : ℝ≥0) (ω : Ω) :
    deterministicallyStoppedProcess X T t ω = X (min t T) ω :=
  stoppedProcess_const_apply X T t ω

/-- A local martingale, using mathlib's local-property interface. -/
def LocalMartingale
    (X : Process Ω)
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (μ : Measure Ω) : Prop :=
  ProbabilityTheory.Locally
    (fun Y : Process Ω => MeasureTheory.Martingale Y ℱ μ) ℱ X μ

end FTAPTheorem42
