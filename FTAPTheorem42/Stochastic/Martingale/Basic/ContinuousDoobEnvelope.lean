/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.GridEnvelope
import FTAPTheorem42.Stochastic.Martingale.Basic.MartingaleChronologicalGrid
import FTAPTheorem42.Stochastic.FiniteVariation.FiniteVariationFactorialApproximation
import FTAPTheorem42.Stochastic.Process.ProcessLeftJump

/-!
# Factorial-grid envelopes for continuous-time Doob estimates

The stopped factorial grids are nested finite chronological grids.  Their
running maxima therefore form an increasing measurable sequence.  Right
continuity shows that its `ℝ≥0∞` supremum dominates the process at every time
up to the deterministic horizon.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal MeasureTheory NNReal ProbabilityTheory

namespace FTAPTheorem42

namespace FactorialChronologicalGrid

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Monotone convergence transfers the gridwise Doob estimates to the
squared factorial envelope. -/
theorem Submartingale.lintegral_eFactorialRunningMaxSqEnvelope_le
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {f : ℝ≥0 → Ω → ℝ} (hf : Submartingale f ℱ μ) (hf_nonneg : 0 ≤ f)
    (T : ℝ≥0) (hterminal : MemLp (f T) (2 : ℝ≥0∞) μ) :
    (∫⁻ ω, eFactorialRunningMaxSqEnvelope f T ω ∂μ) ≤
      4 * ∫⁻ ω, ENNReal.ofReal ((f T ω) ^ 2) ∂μ := by
  let c := Nat.ceil T
  let g : ℕ → Ω → ℝ≥0∞ := fun q ω =>
    ENNReal.ofReal ((factorialRunningMax f T (q + c) ω) ^ 2)
  have hF_nonneg : ∀ r, 0 ≤ factorialRunningMax f T r := by
    intro r
    exact finiteRunningMax_nonneg _ _
      ((stoppedGrid T r).natSample_nonneg hf_nonneg)
  have hg_meas : ∀ q, Measurable (g q) := by
    intro q
    exact ((measurable_factorialRunningMax f T (q + c)
      (fun t => ((hf.stronglyMeasurable t).mono (ℱ.le t)).measurable)).pow_const 2).ennreal_ofReal
  have hg_mono : Monotone g := by
    intro q p hqp ω
    apply ENNReal.ofReal_le_ofReal
    have hmax := factorialRunningMax_mono f T
      (Nat.add_le_add_right hqp c) ω
    exact (sq_le_sq₀ (hF_nonneg (q + c) ω)
      (hF_nonneg (p + c) ω)).2 hmax
  have henvelope : eFactorialRunningMaxSqEnvelope f T = fun ω => ⨆ q, g q ω := by
    funext ω
    apply le_antisymm
    · apply iSup_le
      intro r
      exact le_iSup_of_le r (by
        apply ENNReal.ofReal_le_ofReal
        have hmax := factorialRunningMax_mono f T
          (show r ≤ r + c from Nat.le_add_right r c) ω
        exact (sq_le_sq₀ (hF_nonneg r ω)
          (hF_nonneg (r + c) ω)).2 hmax)
    · apply iSup_le
      intro q
      exact le_iSup (fun r => ENNReal.ofReal
        ((factorialRunningMax f T r ω) ^ 2)) (q + c)
  rw [henvelope, lintegral_iSup hg_meas hg_mono]
  apply iSup_le
  intro q
  have hgrid :=
    Submartingale.lintegral_sq_factorialRunningMax_le_four_mul
      hf hf_nonneg T (show Nat.ceil T ≤ q + c by
        exact Nat.le_add_left c q) hterminal
  exact hgrid

end FactorialChronologicalGrid

end FTAPTheorem42
