/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/
import Mathlib.Probability.Process.Stopping

/-! # Finite truncation of stopping times

Truncate a WithTop-valued stopping time at a deterministic level, extract
its finite value, and retain the stopping-time property after re-embedding. -/

namespace FTAPTheorem42

open MeasureTheory

variable {Ω Time : Type*} [MeasurableSpace Ω] [LinearOrder Time]
  [Nonempty Time]

namespace PredictableElementaryStrategy

attribute [local instance] Classical.propDecidable

variable {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}

/-- Replace top by the finite localization level after truncating a stopping time. -/
noncomputable def truncatedStoppingTime
    (τ : Ω → WithTop Time) (r : Time) : Ω → Time :=
  fun ω => (min (τ ω) (r : WithTop Time)).untopA

omit [MeasurableSpace Ω] in
/- The finite truncation, when re-embedded, is the stopped WithTop time. -/
theorem coe_truncatedStoppingTime
    {τ : Ω → WithTop Time} (r : Time) :
    (fun ω => ((truncatedStoppingTime (Time := Time) τ r) ω : WithTop Time)) =
      fun ω => min (τ ω) (r : WithTop Time) := by
  let σ : Ω → WithTop Time := fun ω => min (τ ω) (r : WithTop Time)
  have hσ_le : ∀ ω, σ ω ≤ (r : WithTop Time) := by
    intro ω
    exact min_le_right _ _
  funext ω
  have hne : σ ω ≠ ⊤ := by
    intro htop
    have hle := hσ_le ω
    rw [htop] at hle
    exact (WithTop.not_top_le_coe r) hle
  change (↑((σ ω).untopA) = σ ω)
  rw [WithTop.untopA_eq_untop hne]
  exact WithTop.coe_untop _ hne

/-- The truncation of a stopping time is a finite-valued stopping time. -/
theorem truncatedStoppingTime_isStoppingTime
    {τ : Ω → WithTop Time} (hτ : IsStoppingTime ℱ τ) (r : Time) :
    IsStoppingTime ℱ
      (fun ω => ((truncatedStoppingTime (Time := Time) τ r) ω : WithTop Time)) := by
  rw [coe_truncatedStoppingTime (Time := Time) r]
  exact hτ.min_const r

end PredictableElementaryStrategy

end FTAPTheorem42
