/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-! # L² contraction under conditional expectation

Conditional expectation contracts the squared integral. For a martingale,
a square-integrable later value therefore controls every earlier L² norm. -/

namespace FTAPTheorem42

open Filter MeasureTheory Topology
open scoped ENNReal NNReal RealInnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

namespace MartingaleL2Terminal

section OrderedIndex

variable {ι : Type*} [Preorder ι]
  {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ι (inferInstance : MeasurableSpace Ω)}
  {M : ι → Ω → ℝ}

omit [IsFiniteMeasure μ] in
/-- A square-integrable later value of a martingale makes every earlier
value square integrable, with the usual `L²` contraction. -/
theorem Martingale.memLp_two_of_le_and_eLpNorm_le
    (hM : Martingale M ℱ μ) {i j : ι} (hij : i ≤ j)
    (hTerminal : MemLp (M j) (2 : ℝ≥0∞) μ) :
    MemLp (M i) (2 : ℝ≥0∞) μ ∧
      eLpNorm (M i) (2 : ℝ≥0∞) μ ≤
        eLpNorm (M j) (2 : ℝ≥0∞) μ := by
  have hCond : MemLp (μ[M j | ℱ i]) (2 : ℝ≥0∞) μ :=
    hTerminal.condExp (by norm_num)
  have hEq : μ[M j | ℱ i] =ᵐ[μ] M i := hM.condExp_ae_eq hij
  have hEarlier : MemLp (M i) (2 : ℝ≥0∞) μ := hCond.ae_eq hEq
  refine ⟨hEarlier, ?_⟩
  rw [← eLpNorm_congr_ae hEq]
  rw [← ofReal_lpNorm hCond, ← ofReal_lpNorm hTerminal]
  exact ENNReal.ofReal_le_ofReal
    (hTerminal.lpNorm_condExp_le_lpNorm (m := ℱ i) (by norm_num))

end OrderedIndex

end MartingaleL2Terminal

end FTAPTheorem42

namespace FTAPTheorem42

open Filter MeasureTheory Set Topology
open scoped ENNReal MeasureTheory NNReal ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

namespace CountableCondExpEnvelope

/-- Conditional expectation contracts the squared integral. -/
theorem lintegral_condExp_sq_le
    {Time : Type*} [Preorder Time]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}
    {J : Ω → ℝ} (hJ : MemLp J (2 : ℝ≥0∞) μ) (t : Time) :
    (∫⁻ ω, ENNReal.ofReal ((μ[J | ℱ t] ω) ^ 2) ∂μ) ≤
      ∫⁻ ω, ENNReal.ofReal ((J ω) ^ 2) ∂μ := by
  have hJsq : Integrable (fun ω => ‖J ω‖ ^ (2 : ℝ)) μ := by
    simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using
      hJ.integrable_sq
  have hcondMem : MemLp (μ[J | ℱ t]) (2 : ℝ≥0∞) μ :=
    hJ.condExp (by norm_num)
  have hcondSq : Integrable (fun ω => (μ[J | ℱ t] ω) ^ 2) μ :=
    hcondMem.integrable_sq
  have hJSq' : Integrable (fun ω => (J ω) ^ 2) μ := hJ.integrable_sq
  have hreal : (∫ ω, (μ[J | ℱ t] ω) ^ 2 ∂μ) ≤
      ∫ ω, (J ω) ^ 2 ∂μ := by
    simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using
      (integral_norm_condExp_rpow_le (m := ℱ t)
        (p := (2 : ℝ)) (by norm_num) hJsq)
  have hcondNonneg : ∀ᵐ ω ∂μ, 0 ≤ (μ[J | ℱ t] ω) ^ 2 :=
    Filter.Eventually.of_forall fun ω => sq_nonneg _
  have hJNonneg : ∀ᵐ ω ∂μ, 0 ≤ (J ω) ^ 2 :=
    Filter.Eventually.of_forall fun ω => sq_nonneg _
  rw [← ofReal_integral_eq_lintegral_ofReal hcondSq hcondNonneg,
    ← ofReal_integral_eq_lintegral_ofReal hJSq' hJNonneg]
  exact ENNReal.ofReal_le_ofReal hreal

end CountableCondExpEnvelope

end FTAPTheorem42
