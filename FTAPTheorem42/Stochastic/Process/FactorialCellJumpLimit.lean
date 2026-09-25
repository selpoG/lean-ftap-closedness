/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Stochastic.Predictable.LeftContinuousPredictable
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationFactorialApproximation
import FTAPTheorem42.Foundations.CadlagEnvelope
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral

/-! # Factorial cell increments converge to left jumps -/

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal ProbabilityTheory

namespace FTAPTheorem42.LeftContinuousPredictable

/-- Increment across the cell containing `s` in its half-open interior.
Both endpoints are clamped at the fixed horizon. -/
noncomputable def cellIncrement (f : NNReal → Real) (T : NNReal) (r : Nat) (s : NNReal) : Real :=
  f (min (gridPoint r (leftIndex r s + 1)) T) - f (min (approx r s) T)

private theorem rightPoint_eq_approx {s : NNReal} (hs : s ≠ 0) (r : Nat) :
    gridPoint r (leftIndex r s + 1) = FactorialChronologicalGrid.approx (r + 1) s := by
  have hpos : 0 < Nat.ceil (s * (denominator r : NNReal)) :=
    Nat.ceil_pos.mpr (mul_pos (pos_iff_ne_zero.mpr hs) (by
      exact_mod_cast Nat.factorial_pos (r + 1)))
  dsimp only [gridPoint, leftIndex]
  rw [Nat.sub_add_cancel hpos]
  rfl

/-- On an actual mesh cell, the approximation is its stopped increment. -/
theorem cellIncrement_eq_of_mem_Ioc
    (f : NNReal → Real) (T : NNReal) {r k : Nat} {s : NNReal}
    (hs : s ∈ Ioc (gridPoint r k) (gridPoint r (k + 1))) :
    cellIncrement f T r s = f (min (gridPoint r (k + 1)) T) - f (min (gridPoint r k) T) := by
  have hLeft := approx_eq_gridPoint_of_mem_Ioc hs
  have hIndex : leftIndex r s = k := by
    have hd : (denominator r : NNReal) ≠ 0 := by
      exact_mod_cast (Nat.factorial_ne_zero (r + 1))
    have h := (div_left_inj' hd).mp hLeft
    exact_mod_cast h
  simp only [cellIncrement, hIndex, hLeft]

/-- The cell step is measurable even when no measurability is supplied
for the path: at each level it has only countably many values. -/
theorem cellIncrement_measurable (f : NNReal → Real) (T : NNReal) (r : Nat) :
    Measurable (cellIncrement f T r) := by
  have hIndex : Measurable (leftIndex r) :=
    ((measurable_id.mul_const (denominator r : NNReal)).nat_ceil).sub_const 1
  exact (measurable_of_countable (f := fun k : Nat =>
    f (min (gridPoint r (k + 1)) T) - f (min (gridPoint r k) T))).comp hIndex

/-- Positive-time cell increments converge to the left jump, including
when the time belongs to every sufficiently fine mesh. -/
theorem tendsto_cellIncrement
    (f : NNReal → Real)
    (hRight : ∀ s, ContinuousWithinAt f (Ici s) s)
    (hLeft : ∀ s, Tendsto f (𝓝[<] s) (𝓝 (Function.leftLim f s)))
    {T s : NNReal} (hs : s ∈ Ioc 0 T) :
    Tendsto (fun r => cellIncrement f T r s) atTop (𝓝 (f s - Function.leftLim f s)) := by
  have hLower : Tendsto (fun r => approx r s) atTop (𝓝[<] s) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨tendsto_approx s, Eventually.of_forall (fun r => approx_lt (ne_of_gt hs.1) r)⟩
  have hLowerValue : Tendsto (fun r => f (min (approx r s) T)) atTop
      (𝓝 (Function.leftLim f s)) := by
    simpa only [Function.comp_def, min_eq_left ((approx_le _ s).trans hs.2)] using
      (hLeft s).comp hLower
  have hUpperValue : Tendsto (fun r => f (min (gridPoint r (leftIndex r s + 1)) T))
      atTop (𝓝 (f s)) := by
    simp_rw [rightPoint_eq_approx (ne_of_gt hs.1)]
    exact (FiniteVariationFactorialApproximation.tendsto_apply_min_approx f hRight hs.2).comp
      (tendsto_add_atTop_nat 1)
  exact hUpperValue.sub hLowerValue

/-- Dominated convergence under any finite time measure. The exclusion
of time zero matches the left-jump convention and the half-open cells. -/
theorem tendsto_lintegral_cellIncrement_error
    (f : NNReal → Real)
    (hRight : ∀ s, ContinuousWithinAt f (Ici s) s)
    (hLeft : ∀ s, Tendsto f (𝓝[<] s) (𝓝 (Function.leftLim f s)))
    (T : NNReal) (ν : Measure NNReal) [IsFiniteMeasure ν] :
    Tendsto (fun r => ∫⁻ s in Ioc (0 : NNReal) T,
      ENNReal.ofReal |cellIncrement f T r s - (f s - Function.leftLim f s)| ∂ν)
      atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := FactorialChronologicalGrid.exists_abs_le_on_Icc_of_rightContinuous_leftLimits
    f hRight hLeft T
  have hBound : ∀ r, ∀ᵐ s ∂ν.restrict (Ioc 0 T), ‖cellIncrement f T r s‖ ≤ 2 * C := by
    intro r
    apply Eventually.of_forall
    intro s
    rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (by
      linarith [hC (min (gridPoint r (leftIndex r s + 1)) T) (min_le_right _ _),
        hC (min (approx r s) T) (min_le_right _ _)])
  have hLimit : ∀ᵐ s ∂ν.restrict (Ioc 0 T), Tendsto (fun r => cellIncrement f T r s)
      atTop (𝓝 (f s - Function.leftLim f s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact tendsto_cellIncrement f hRight hLeft hs
  simpa only [Real.norm_eq_abs] using tendsto_lintegral_norm_of_dominated_convergence
    (fun r => (cellIncrement_measurable f T r).aestronglyMeasurable)
    (integrable_const (2 * C) :
      Integrable (fun _ => 2 * C) (ν.restrict (Ioc 0 T))).hasFiniteIntegral
    hBound hLimit

end FTAPTheorem42.LeftContinuousPredictable
