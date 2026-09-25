/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/
import FTAPTheorem42.Foundations.Envelope
import FTAPTheorem42.Stochastic.Martingale.Basic.DoobL2Maximal
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import FTAPTheorem42.Foundations.FactorialChronologicalGrid

/-!
# Sampling martingales on chronological grids

A finite chronological grid has an ordered `Fin` index.  This module extends
that finite index constantly to `ℕ`, reindexes a continuous-time filtration,
and proves that martingales remain martingales after sampling.  Hence the
finite-horizon Doob `L²` inequality applies without treating an unordered
right-dense skeleton as trading time.
-/

open Filter MeasureTheory Set
open scoped ENNReal MeasureTheory NNReal ProbabilityTheory

namespace FTAPTheorem42

namespace ChronologicalGrid

variable {Time Ω : Type*} [LinearOrder Time] [MeasurableSpace Ω]
variable {N : ℕ} (G : ChronologicalGrid Time N)

theorem Martingale.natSample
    {μ : Measure Ω}
    {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}
    {f : Time → Ω → ℝ} (hf : Martingale f ℱ μ) :
    Martingale (G.natSample f) (G.sampledFiltration ℱ) μ := by
  refine ⟨?_, ?_⟩
  · intro k
    exact hf.stronglyMeasurable (G.sampledTime k)
  · intro i j hij
    exact hf.condExp_ae_eq (G.sampledTime_mono hij)

/-- Sampling a submartingale on a chronological grid preserves the
submartingale property. -/
theorem Submartingale.natSample
    {μ : Measure Ω}
    {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}
    {f : Time → Ω → ℝ} (hf : Submartingale f ℱ μ) :
    Submartingale (G.natSample f) (G.sampledFiltration ℱ) μ := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    exact hf.stronglyMeasurable (G.sampledTime k)
  · intro i j hij
    exact hf.ae_le_condExp (G.sampledTime_mono hij)
  · intro k
    exact hf.integrable (G.sampledTime k)

/-- Doob's finite-horizon estimate after sampling a nonnegative
submartingale on an arbitrary ordered time grid. -/
theorem Submartingale.eLpNorm_finiteRunningMax_sample_le_two_mul
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}
    {f : Time → Ω → ℝ} (hf : Submartingale f ℱ μ) (hf_nonneg : 0 ≤ f)
    (hterminal : MemLp (f (G.time ⟨N, Nat.lt_succ_self N⟩))
      (2 : ℝ≥0∞) μ) :
    eLpNorm (finiteRunningMax (G.natSample f) N) (2 : ℝ≥0∞) μ ≤
      2 * eLpNorm (f (G.time ⟨N, Nat.lt_succ_self N⟩))
        (2 : ℝ≥0∞) μ := by
  have hlast : G.natSample f N =
      f (G.time ⟨N, Nat.lt_succ_self N⟩) := by
    change f (G.time (G.natIndex N)) = _
    rw [G.natIndex_last]
  have hsample : Submartingale (G.natSample f)
      (G.sampledFiltration ℱ) μ :=
    ChronologicalGrid.Submartingale.natSample (G := G) hf
  simpa only [hlast] using
    FTAPTheorem42.Submartingale.eLpNorm_finiteRunningMax_le_two_mul
      hsample (G.natSample_nonneg hf_nonneg) N
      (by simpa only [hlast] using hterminal)

/-- Squared `lintegral` form of Doob's `L²` estimate on an arbitrary
finite chronological grid. -/
theorem Submartingale.lintegral_sq_finiteRunningMax_sample_le_four_mul
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration Time (inferInstance : MeasurableSpace Ω)}
    {f : Time → Ω → ℝ} (hf : Submartingale f ℱ μ) (hf_nonneg : 0 ≤ f)
    (hterminal : MemLp (f (G.time ⟨N, Nat.lt_succ_self N⟩))
      (2 : ℝ≥0∞) μ) :
    (∫⁻ ω, ENNReal.ofReal
        ((finiteRunningMax (G.natSample f) N ω) ^ 2) ∂μ) ≤
      4 * ∫⁻ ω, ENNReal.ofReal
        ((f (G.time ⟨N, Nat.lt_succ_self N⟩) ω) ^ 2) ∂μ := by
  let F : Ω → ℝ := finiteRunningMax (G.natSample f) N
  let Z : Ω → ℝ := f (G.time ⟨N, Nat.lt_succ_self N⟩)
  have hsample : Submartingale (G.natSample f)
      (G.sampledFiltration ℱ) μ :=
    ChronologicalGrid.Submartingale.natSample (G := G) hf
  have hsample_nonneg : 0 ≤ G.natSample f :=
    G.natSample_nonneg hf_nonneg
  have hcoord : ∀ k, k ≤ N →
      MemLp (G.natSample f k) (2 : ℝ≥0∞) μ := by
    intro k hk
    have hlast : G.natSample f N = Z := by
      change f (G.time (G.natIndex N)) = _
      rw [G.natIndex_last]
    have hterminal' : MemLp (G.natSample f N) (2 : ℝ≥0∞) μ := by
      simpa only [hlast] using hterminal
    have hcond : MemLp
        (μ[G.natSample f N | G.sampledFiltration ℱ k])
        (2 : ℝ≥0∞) μ := hterminal'.condExp (by norm_num)
    have hmeas := (hsample.stronglyMeasurable k).mono
      ((G.sampledFiltration ℱ).le k)
    apply MemLp.of_le hcond hmeas.aestronglyMeasurable
    filter_upwards [hsample.ae_le_condExp hk,
      condExp_nonneg (Filter.Eventually.of_forall
        (hsample_nonneg N))] with ω hle hcond_nonneg
    rw [Real.norm_eq_abs, abs_of_nonneg (hsample_nonneg k ω),
      Real.norm_eq_abs, abs_of_nonneg hcond_nonneg]
    exact hle
  have hF : MemLp F (2 : ℝ≥0∞) μ :=
    finiteRunningMax_memLp_two _ _ hsample_nonneg
      (fun k hk => ((hsample.stronglyMeasurable k).mono
        ((G.sampledFiltration ℱ).le k)).measurable) hcoord
  have hnorm : eLpNorm F (2 : ℝ≥0∞) μ ≤
      2 * eLpNorm Z (2 : ℝ≥0∞) μ := by
    have hlast : G.natSample f N = Z := by
      change f (G.time (G.natIndex N)) = _
      rw [G.natIndex_last]
    simpa only [F, Z, hlast] using
      ChronologicalGrid.Submartingale.eLpNorm_finiteRunningMax_sample_le_two_mul
        (G := G) hf hf_nonneg hterminal
  have hnormReal : (eLpNorm F (2 : ℝ≥0∞) μ).toReal ≤
      (2 * eLpNorm Z (2 : ℝ≥0∞) μ).toReal :=
    ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num)
      hterminal.eLpNorm_ne_top) hnorm
  rw [eLpNorm_two_toReal_eq_sqrt_integral_norm_sq hF,
    ENNReal.toReal_mul,
    eLpNorm_two_toReal_eq_sqrt_integral_norm_sq hterminal] at hnormReal
  norm_num only [ENNReal.toReal_ofNat] at hnormReal
  have hFsq_int : Integrable (fun ω => F ω ^ 2) μ := by
    exact (hF.integrable_mul hF).congr
      (Filter.Eventually.of_forall fun ω => by simp [pow_two])
  have hZsq_int : Integrable (fun ω => Z ω ^ 2) μ := by
    exact (hterminal.integrable_mul hterminal).congr
      (Filter.Eventually.of_forall fun ω => by simp [Z, pow_two])
  have hreal : (∫ ω, F ω ^ 2 ∂μ) ≤
      4 * ∫ ω, Z ω ^ 2 ∂μ := by
    have hF0 : 0 ≤ ∫ ω, ‖F ω‖ ^ 2 ∂μ :=
      integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun ω => sq_nonneg ‖F ω‖)
    have hZ0 : 0 ≤ ∫ ω, ‖Z ω‖ ^ 2 ∂μ :=
      integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun ω => sq_nonneg ‖Z ω‖)
    have hsquare : (∫ ω, ‖F ω‖ ^ 2 ∂μ) ≤
        4 * ∫ ω, ‖Z ω‖ ^ 2 ∂μ := by
      nlinarith [Real.sq_sqrt hF0, Real.sq_sqrt hZ0,
        Real.sqrt_nonneg (∫ ω, ‖F ω‖ ^ 2 ∂μ),
        Real.sqrt_nonneg (∫ ω, ‖Z ω‖ ^ 2 ∂μ)]
    simpa only [Real.norm_eq_abs, sq_abs] using hsquare
  have hF_nonneg : ∀ᵐ ω ∂μ, 0 ≤ F ω ^ 2 :=
    Filter.Eventually.of_forall fun ω => sq_nonneg (F ω)
  have hZ_nonneg : ∀ᵐ ω ∂μ, 0 ≤ Z ω ^ 2 :=
    Filter.Eventually.of_forall fun ω => sq_nonneg (Z ω)
  rw [← ofReal_integral_eq_lintegral_ofReal hFsq_int hF_nonneg,
    ← ofReal_integral_eq_lintegral_ofReal hZsq_int hZ_nonneg]
  calc
    ENNReal.ofReal (∫ ω, F ω ^ 2 ∂μ) ≤
        ENNReal.ofReal (4 * ∫ ω, Z ω ^ 2 ∂μ) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = 4 * ENNReal.ofReal (∫ ω, Z ω ^ 2 ∂μ) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num

end ChronologicalGrid

namespace FactorialChronologicalGrid

/-- Stopping every factorial grid at the same horizon preserves nesting of
the grid ranges. -/
theorem range_stoppedGrid_mono (T : ℝ≥0) :
    Monotone (fun r => Set.range (stoppedGrid T r).time) := by
  intro r q hr _ hmem
  obtain ⟨k, rfl⟩ := hmem
  obtain ⟨l, hl⟩ := range_grid_mono hr ⟨k, rfl⟩
  refine ⟨l, ?_⟩
  simp only [stoppedGrid_time]
  rw [hl]

theorem stoppedGrid_last_time
    (T : ℝ≥0) {r : ℕ} (hr : Nat.ceil T ≤ r) :
    (stoppedGrid T r).time
        ⟨r * r.factorial, Nat.lt_succ_self (r * r.factorial)⟩ = T := by
  rw [stoppedGrid_time, min_eq_right]
  dsimp only [grid]
  have hTr : T ≤ (r : ℝ≥0) := by
    exact (Nat.le_ceil T).trans (by exact_mod_cast hr)
  simpa [Nat.cast_mul, (show (r.factorial : ℝ≥0) ≠ 0 by positivity)] using hTr

/-- Doob's `L²` estimate on every sufficiently fine factorial grid stopped
at `T`. -/
theorem Submartingale.eLpNorm_factorialRunningMax_le_two_mul
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {f : ℝ≥0 → Ω → ℝ} (hf : Submartingale f ℱ μ) (hf_nonneg : 0 ≤ f)
    (T : ℝ≥0) {r : ℕ} (hr : Nat.ceil T ≤ r)
    (hterminal : MemLp (f T) (2 : ℝ≥0∞) μ) :
    eLpNorm
        (finiteRunningMax ((stoppedGrid T r).natSample f) (r * r.factorial))
        (2 : ℝ≥0∞) μ ≤
      2 * eLpNorm (f T) (2 : ℝ≥0∞) μ := by
  have hlast := stoppedGrid_last_time T hr
  simpa only [hlast] using
    ChronologicalGrid.Submartingale.eLpNorm_finiteRunningMax_sample_le_two_mul
      (G := stoppedGrid T r) hf hf_nonneg
      (by simpa only [hlast] using hterminal)

/-- Squared `lintegral` form of the factorial-grid estimate. -/
theorem Submartingale.lintegral_sq_factorialRunningMax_le_four_mul
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {f : ℝ≥0 → Ω → ℝ} (hf : Submartingale f ℱ μ) (hf_nonneg : 0 ≤ f)
    (T : ℝ≥0) {r : ℕ} (hr : Nat.ceil T ≤ r)
    (hterminal : MemLp (f T) (2 : ℝ≥0∞) μ) :
    (∫⁻ ω, ENNReal.ofReal
        ((finiteRunningMax ((stoppedGrid T r).natSample f)
          (r * r.factorial) ω) ^ 2) ∂μ) ≤
      4 * ∫⁻ ω, ENNReal.ofReal ((f T ω) ^ 2) ∂μ := by
  let F : Ω → ℝ := finiteRunningMax ((stoppedGrid T r).natSample f)
    (r * r.factorial)
  have hlast := stoppedGrid_last_time T hr
  have hsample : Submartingale ((stoppedGrid T r).natSample f)
      ((stoppedGrid T r).sampledFiltration ℱ) μ :=
    ChronologicalGrid.Submartingale.natSample (G := stoppedGrid T r) hf
  have hsample_nonneg : 0 ≤ (stoppedGrid T r).natSample f :=
    (stoppedGrid T r).natSample_nonneg hf_nonneg
  have hterminal' : MemLp
      ((stoppedGrid T r).natSample f (r * r.factorial))
      (2 : ℝ≥0∞) μ := by
    simpa only [ChronologicalGrid.natSample,
      ChronologicalGrid.sampledTime,
      ChronologicalGrid.natIndex_last, hlast] using hterminal
  have hcoord : ∀ k, k ≤ r * r.factorial →
      MemLp ((stoppedGrid T r).natSample f k) (2 : ℝ≥0∞) μ := by
    intro k hk
    have hcond : MemLp
        (μ[(stoppedGrid T r).natSample f (r * r.factorial) |
          (stoppedGrid T r).sampledFiltration ℱ k])
        (2 : ℝ≥0∞) μ := hterminal'.condExp (by norm_num)
    have hmeas := (hsample.stronglyMeasurable k).mono
      (((stoppedGrid T r).sampledFiltration ℱ).le k)
    apply MemLp.of_le hcond hmeas.aestronglyMeasurable
    filter_upwards [hsample.ae_le_condExp hk,
      condExp_nonneg (Filter.Eventually.of_forall
        (hsample_nonneg (r * r.factorial)))]
        with ω hle hcond_nonneg
    rw [Real.norm_eq_abs, abs_of_nonneg (hsample_nonneg k ω),
      Real.norm_eq_abs, abs_of_nonneg hcond_nonneg]
    exact hle
  have hF : MemLp F (2 : ℝ≥0∞) μ :=
    finiteRunningMax_memLp_two _ _ hsample_nonneg
      (fun k hk => ((hsample.stronglyMeasurable k).mono
        (((stoppedGrid T r).sampledFiltration ℱ).le k)).measurable) hcoord
  have hnorm : eLpNorm F (2 : ℝ≥0∞) μ ≤
      2 * eLpNorm (f T) (2 : ℝ≥0∞) μ := by
    simpa only [F] using
      FactorialChronologicalGrid.Submartingale.eLpNorm_factorialRunningMax_le_two_mul
        hf hf_nonneg T hr hterminal
  have hnormReal : (eLpNorm F (2 : ℝ≥0∞) μ).toReal ≤
      (2 * eLpNorm (f T) (2 : ℝ≥0∞) μ).toReal :=
    ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num)
      hterminal.eLpNorm_ne_top) hnorm
  rw [eLpNorm_two_toReal_eq_sqrt_integral_norm_sq hF,
    ENNReal.toReal_mul,
    eLpNorm_two_toReal_eq_sqrt_integral_norm_sq hterminal] at hnormReal
  norm_num only [ENNReal.toReal_ofNat] at hnormReal
  have hFsq_int : Integrable (fun ω => F ω ^ 2) μ := by
    exact (hF.integrable_mul hF).congr
      (Filter.Eventually.of_forall fun ω => by simp [pow_two])
  have hTsq_int : Integrable (fun ω => f T ω ^ 2) μ := by
    exact (hterminal.integrable_mul hterminal).congr
      (Filter.Eventually.of_forall fun ω => by simp [pow_two])
  have hreal : (∫ ω, F ω ^ 2 ∂μ) ≤
      4 * ∫ ω, f T ω ^ 2 ∂μ := by
    have hF0 : 0 ≤ ∫ ω, ‖F ω‖ ^ 2 ∂μ :=
      integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun ω => sq_nonneg ‖F ω‖)
    have hT0 : 0 ≤ ∫ ω, ‖f T ω‖ ^ 2 ∂μ :=
      integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun ω => sq_nonneg ‖f T ω‖)
    have hsquare : (∫ ω, ‖F ω‖ ^ 2 ∂μ) ≤
        4 * ∫ ω, ‖f T ω‖ ^ 2 ∂μ := by
      nlinarith [Real.sq_sqrt hF0, Real.sq_sqrt hT0,
        Real.sqrt_nonneg (∫ ω, ‖F ω‖ ^ 2 ∂μ),
        Real.sqrt_nonneg (∫ ω, ‖f T ω‖ ^ 2 ∂μ)]
    simpa only [Real.norm_eq_abs, sq_abs] using hsquare
  have hF_nonneg : ∀ᵐ ω ∂μ, 0 ≤ F ω ^ 2 :=
    Filter.Eventually.of_forall fun ω => sq_nonneg (F ω)
  have hT_nonneg : ∀ᵐ ω ∂μ, 0 ≤ f T ω ^ 2 :=
    Filter.Eventually.of_forall fun ω => sq_nonneg (f T ω)
  rw [← ofReal_integral_eq_lintegral_ofReal hFsq_int hF_nonneg,
    ← ofReal_integral_eq_lintegral_ofReal hTsq_int hT_nonneg]
  calc
    ENNReal.ofReal (∫ ω, F ω ^ 2 ∂μ) ≤
        ENNReal.ofReal (4 * ∫ ω, f T ω ^ 2 ∂μ) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = 4 * ENNReal.ofReal (∫ ω, f T ω ^ 2 ∂μ) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num

end FactorialChronologicalGrid

end FTAPTheorem42
